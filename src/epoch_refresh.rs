//! Phase 2: Automated Epoch Refresh
//!
//! At the beginning of each epoch, the client derives a Daily Token bound to the
//! current epoch `T`. The client proves possession of a valid Master Token,
//! that the token is not expired, and that the epoch nullifier `N_T` is correctly
//! computed. The server verifies the proof and issues a blind Daily Token under
//! the daily signing key.
//!
//! This module implements the complete refresh proof as specified in Section 5.

extern crate alloc;
use alloc::vec::Vec;
use ark_bls12_381::{Fq12, Fr, G1Projective, G2Projective};
use ark_ec::{CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::Zero;
use sha2::Digest as _;
use ark_std::io::Write as _;
use crate::bbs_proof::BbsSignature;
use crate::bulletproofs::{prove_range, serialize_proof, verify_range, RangeProof};
use crate::error::{ActError, Result};
use crate::hash::{hash_to_g1, hash_to_scalar_from_hasher, HasherWriter};
use crate::setup::{Generators, ServerKeys};
use crate::types::Scalar;

/// Efficient MSM using precomputed affine bases (no projective→affine conversion).
///
/// Callers that already hold `G1Affine` bases (e.g. the cached generator affines)
/// should call `G1Projective::msm` directly; this helper is for the small number
/// of call sites that still start from projective inputs.
fn msm_projective(bases: &[G1Projective], scalars: &[Fr]) -> G1Projective {
    let affine = G1Projective::normalize_batch(bases);
    G1Projective::msm(&affine, scalars).expect("MSM length mismatch")
}

// ============================================================================
// Refresh Proof Structure
// ============================================================================

/// The complete refresh proof sent by the client.
#[derive(Clone, Debug)]
pub struct RefreshProof {
    // BBS+ core proof elements
    pub a_prime: G1Projective,
    pub a_bar: G1Projective,
    pub t_bbs: G1Projective,

    // Bridging commitments
    pub t_scale_n: G1Projective,
    pub t_n: G1Projective,
    pub t_scale_d: G1Projective,
    pub t_d: G1Projective,
    pub t_scale_b: G1Projective,
    pub t_b: G1Projective,

    // Responses
    pub z_e: Scalar,
    pub z_r1: Scalar,
    pub z_s_tilde: Scalar,
    pub z_k_tilde: Scalar,
    pub z_c_tilde: Scalar,
    pub z_e_tilde: Scalar,
    pub z_u: Scalar,
    pub z_v: Scalar,
    pub z_w: Scalar,

    // Range proof for expiry
    pub bp_exp: RangeProof,

    // Public values (sent separately but included here for convenience)
    pub n_t: G1Projective,
    pub k_daily: G1Projective,
    pub c_delta: G1Projective,
}

/// Server response containing the blind Daily Token.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RefreshResponse {
    #[serde(with = "crate::types::g1_serde")]
    pub a_daily: G1Projective,
    pub e_daily: Scalar,
    pub s_prime_daily: Scalar,
}

// ============================================================================
// Client State
// ============================================================================

/// Client state for epoch refresh.
pub struct RefreshClient {
    /// Secret subscription identifier.
    pub k_sub: Scalar,
    /// Maximum credits per epoch.
    pub c_max: u32,
    /// Expiry epoch.
    pub e_max: u32,
    /// Current epoch.
    pub t: u32,
    /// Daily token secret (to be used after finalization).
    pub k_daily: Scalar,
    /// Daily token blinding.
    pub r_daily: Scalar,
    /// Expiry proof blinding.
    pub r_delta: Scalar,
}

impl RefreshClient {
    /// Finalize the Daily Token after receiving the server's response.
    pub fn finalize(
        self,
        response: RefreshResponse,
    ) -> (BbsSignature, Scalar) {
        let s_daily = self.r_daily + response.s_prime_daily;
        let daily_sig = BbsSignature {
            a: response.a_daily,
            e: response.e_daily,
            s: s_daily,
        };
        (daily_sig, self.k_daily)
    }
}

// ============================================================================
// Combined Refresh Prover
// ============================================================================

/// A prover that generates the complete refresh proof with all bridging
/// commitments and consistent randomness.
pub struct RefreshProver {
    // BBS+ core
    r1: Scalar,
    a_prime: G1Projective,
    a_bar: G1Projective,
    t_bbs: G1Projective,
    // Scaled secrets
    s_tilde: Scalar,
    k_tilde: Scalar,
    c_tilde: Scalar,
    e_tilde: Scalar,
    // BBS+ blinders
    rho_e: Scalar,
    rho_r1: Scalar,
    rho_s: Scalar,
    rho_k: Scalar,
    rho_c: Scalar,
    rho_e_msg: Scalar,
    // External blinders
    rho_u: Scalar,
    rho_v: Scalar,
    rho_w: Scalar,
}

impl RefreshProver {
    /// Generate the refresh proof and return the client state needed for
    /// finalization.
    #[allow(clippy::too_many_arguments)]
    pub fn prove(
        rng: &mut (impl CryptoRng + RngCore),
        master: &BbsSignature,
        k_sub: Scalar,
        c_max: u32,
        e_max: u32,
        t: u32,
        generators: &Generators,
        pk_master: &G2Projective,
        h_ctx: Scalar,
    ) -> Result<(RefreshClient, RefreshProof)> {
        // 1. Expiry check
        if e_max < t {
            return Err(ActError::ProtocolError("Master token expired".into()));
        }
        let delta = e_max - t;

        // 2. Compute epoch nullifier
        let h_t = hash_to_g1(b"ACT:Epoch:", &t.to_le_bytes());
        let n_t = h_t * k_sub.0;

        // 3. Daily commitment secrets
        let k_daily = Scalar::rand_nonzero(rng);
        let r_daily = Scalar::rand(rng);
        let k_daily_commit = generators.h[4] * Scalar::from(c_max).0
            + generators.h[1] * k_daily.0
            + generators.h[2] * Scalar::from(t).0
            + generators.h[0] * r_daily.0;

        // 4. Expiry commitment
        let r_delta = Scalar::rand(rng);
        let c_delta = generators.h[3] * Scalar::from(delta).0
            + generators.h[0] * r_delta.0;

        // 5. BBS+ randomization and scaled secrets
        let r1 = Scalar::rand_nonzero(rng);
        let a_prime = master.a * r1.0;

        // Compute message part M = g1^1 * h0^s * h1^{k_sub} * h2^{c_max} * h3^{e_max}
        // Use pre-cached affine generators — no field inversions needed.
        let msg_part = {
            let bases = [
                generators.g1_affine,
                generators.h_affine[0],
                generators.h_affine[1],
                generators.h_affine[2],
                generators.h_affine[3],
            ];
            let scalars = [
                Fr::from(1u64),
                master.s.0,
                k_sub.0,
                Fr::from(c_max as u64),
                Fr::from(e_max as u64),
            ];
            G1Projective::msm(&bases, &scalars).expect("MSM length mismatch")
        };
        let a_bar = a_prime * (-master.e.0) + msg_part * r1.0;

        let s_tilde = master.s * r1;
        let k_tilde = k_sub * r1;
        let c_tilde = Scalar::from(c_max) * r1;
        let e_tilde = Scalar::from(e_max) * r1;

        // 6. BBS+ blinders
        let rho_e = Scalar::rand(rng);
        let rho_r1 = Scalar::rand(rng);
        let rho_s = Scalar::rand(rng);
        let rho_k = Scalar::rand(rng);
        let rho_c = Scalar::rand(rng);
        let rho_e_msg = Scalar::rand(rng);

        // T_BBS — use a_prime's affine + pre-cached affine generators.
        let t_bbs = {
            let a_prime_affine = a_prime.into_affine();
            let bases = [
                a_prime_affine,
                generators.g1_affine,
                generators.h_affine[0],
                generators.h_affine[1],
                generators.h_affine[2],
                generators.h_affine[3],
            ];
            let scalars = [
                -rho_e.0,
                rho_r1.0,
                rho_s.0,
                rho_k.0,
                rho_c.0,
                rho_e_msg.0,
            ];
            G1Projective::msm(&bases, &scalars).expect("T_BBS MSM length mismatch")
        };

        // 7. External blinders
        let rho_u = Scalar::rand(rng);
        let rho_v = Scalar::rand(rng);
        let rho_w = Scalar::rand(rng);

        // 8. Bridging commitments
        // T_scale_N = rho_r1 * N_T
        let t_scale_n = n_t * rho_r1.0;
        // T_N = rho_k * H_T
        let t_n = h_t * rho_k.0;

        // T_scale_D = rho_r1 * K_daily
        let t_scale_d = k_daily_commit * rho_r1.0;
        // T_D = rho_c * h4 + rho_u * h1 + rho_r1 * T * h2 + rho_v * h0
        // Use pre-cached affine generators for this small 4-base MSM.
        let t_d = {
            let bases = [
                generators.h_affine[4],
                generators.h_affine[1],
                generators.h_affine[2],
                generators.h_affine[0],
            ];
            let scalars = [
                rho_c.0,
                rho_u.0,
                (rho_r1 * Scalar::from(t)).0,
                rho_v.0,
            ];
            G1Projective::msm(&bases, &scalars).expect("T_D MSM length mismatch")
        };

        // C_bridge = C_delta + T * h3
        let c_bridge = c_delta + generators.h[3] * Scalar::from(t).0;
        // T_scale_B = rho_r1 * C_bridge
        let t_scale_b = c_bridge * rho_r1.0;
        // T_B = rho_e_msg * h3 + rho_w * h0 (2-base MSM with cached affines)
        let t_b = {
            let bases = [generators.h_affine[3], generators.h_affine[0]];
            let scalars = [rho_e_msg.0, rho_w.0];
            G1Projective::msm(&bases, &scalars).expect("T_B MSM length mismatch")
        };

        // 9. Generate Bulletproof (needs BBS+ commitments in extra data)
        // Capacity: 32 h_ctx + 4 epoch + 3*48 G1 points + overallocate for bp
        let mut bp_extra = Vec::with_capacity(32 + 4 + 3 * 48 + 8);
        bp_extra.extend_from_slice(&h_ctx.to_bytes());
        bp_extra.extend_from_slice(&t.to_le_bytes());
        n_t.serialize_compressed(&mut bp_extra).unwrap();
        k_daily_commit.serialize_compressed(&mut bp_extra).unwrap();
        c_delta.serialize_compressed(&mut bp_extra).unwrap();
        a_prime.serialize_compressed(&mut bp_extra).unwrap();
        a_bar.serialize_compressed(&mut bp_extra).unwrap();
        t_bbs.serialize_compressed(&mut bp_extra).unwrap();
        let (bp_exp, _) = prove_range(
            rng,
            delta as u64,
            r_delta,
            32,
            generators.h[3],
            generators.h[0],
            b"ACT:Expiry",
            &bp_extra,
        )?;

        // 10. Challenge — feed all elements directly into SHA-256, no intermediate Vec.
        let bp_bytes = serialize_proof(&bp_exp).unwrap();
        let c = {
            let mut hasher = sha2::Sha256::new();
            let mut w = HasherWriter(&mut hasher);
            w.write_all(&h_ctx.to_bytes()).unwrap();
            pk_master.serialize_compressed(&mut w).unwrap();
            w.write_all(&t.to_le_bytes()).unwrap();
            n_t.serialize_compressed(&mut w).unwrap();
            k_daily_commit.serialize_compressed(&mut w).unwrap();
            c_delta.serialize_compressed(&mut w).unwrap();
            w.write_all(&bp_bytes).unwrap();
            a_prime.serialize_compressed(&mut w).unwrap();
            a_bar.serialize_compressed(&mut w).unwrap();
            t_bbs.serialize_compressed(&mut w).unwrap();
            t_scale_n.serialize_compressed(&mut w).unwrap();
            t_n.serialize_compressed(&mut w).unwrap();
            t_scale_d.serialize_compressed(&mut w).unwrap();
            t_d.serialize_compressed(&mut w).unwrap();
            t_scale_b.serialize_compressed(&mut w).unwrap();
            t_b.serialize_compressed(&mut w).unwrap();
            w.write_all(b"Refresh").unwrap();
            drop(w);
            hash_to_scalar_from_hasher(hasher)
        };

        // 11. Responses
        let z_e = rho_e + c * master.e;
        let z_r1 = rho_r1 + c * r1;
        let z_s_tilde = rho_s + c * s_tilde;
        let z_k_tilde = rho_k + c * k_tilde;
        let z_c_tilde = rho_c + c * c_tilde;
        let z_e_tilde = rho_e_msg + c * e_tilde;
        let z_u = rho_u + c * (k_daily * r1);
        let z_v = rho_v + c * (r_daily * r1);
        let z_w = rho_w + c * (r_delta * r1);

        let proof = RefreshProof {
            a_prime,
            a_bar,
            t_bbs,
            t_scale_n,
            t_n,
            t_scale_d,
            t_d,
            t_scale_b,
            t_b,
            z_e,
            z_r1,
            z_s_tilde,
            z_k_tilde,
            z_c_tilde,
            z_e_tilde,
            z_u,
            z_v,
            z_w,
            bp_exp,
            n_t,
            k_daily: k_daily_commit,
            c_delta,
        };

        let client = RefreshClient {
            k_sub,
            c_max,
            e_max,
            t,
            k_daily,
            r_daily,
            r_delta,
        };

        Ok((client, proof))
    }
}

// ============================================================================
// Server Verification
// ============================================================================

/// Verify a refresh proof and issue a Daily Token.
pub fn verify_refresh(
    proof: &RefreshProof,
    current_epoch: u32,
    generators: &Generators,
    pk_master: &G2Projective,
    keys: &ServerKeys,
    h_ctx: Scalar,
    rng: &mut impl RngCore,
) -> Result<RefreshResponse> {
    // 1. Basic bounds
    if proof.n_t.is_zero() {
        return Err(ActError::VerificationFailed("N_T is zero".into()));
    }
    if proof.a_prime.is_zero() || proof.t_bbs.is_zero() {
        return Err(ActError::VerificationFailed("Zero point in proof".into()));
    }

    // 2. Expiry bridge: C_bridge = C_delta + T * h3
    let c_bridge = proof.c_delta + generators.h[3] * Scalar::from(current_epoch).0;

    // 3. Recompute challenge — feed all elements directly into SHA-256.
    let bp_bytes = serialize_proof(&proof.bp_exp).unwrap();
    let c = {
        let mut hasher = sha2::Sha256::new();
        let mut w = HasherWriter(&mut hasher);
        w.write_all(&h_ctx.to_bytes()).unwrap();
        pk_master.serialize_compressed(&mut w).unwrap();
        w.write_all(&current_epoch.to_le_bytes()).unwrap();
        proof.n_t.serialize_compressed(&mut w).unwrap();
        proof.k_daily.serialize_compressed(&mut w).unwrap();
        proof.c_delta.serialize_compressed(&mut w).unwrap();
        w.write_all(&bp_bytes).unwrap();
        proof.a_prime.serialize_compressed(&mut w).unwrap();
        proof.a_bar.serialize_compressed(&mut w).unwrap();
        proof.t_bbs.serialize_compressed(&mut w).unwrap();
        proof.t_scale_n.serialize_compressed(&mut w).unwrap();
        proof.t_n.serialize_compressed(&mut w).unwrap();
        proof.t_scale_d.serialize_compressed(&mut w).unwrap();
        proof.t_d.serialize_compressed(&mut w).unwrap();
        proof.t_scale_b.serialize_compressed(&mut w).unwrap();
        proof.t_b.serialize_compressed(&mut w).unwrap();
        w.write_all(b"Refresh").unwrap();
        drop(w);
        hash_to_scalar_from_hasher(hasher)
    };

    // 4. Epoch hash H_T (needed for nullifier bridge base).
    let h_t = hash_to_g1(b"ACT:Epoch:", &current_epoch.to_le_bytes());

    // 5. Combined batch check for all four bridge + Schnorr equations.
    //
    // Rather than checking the four equations separately:
    //   Eq1 (Nullifier):   h_t * z_k_tilde - n_t * z_r1 + t_scale_n - t_n = 0
    //   Eq2 (Daily):       h[4]*z_c + h[1]*z_u + h[2]*(z_r1*T) + h[0]*z_v
    //                      - k_daily*z_r1 - t_d + t_scale_d = 0
    //   Eq3 (Expiry):      h[3]*z_e_t + h[0]*z_w - c_bridge*z_r1 - t_b + t_scale_b = 0
    //   Eq4 (Schnorr):     a'*(-z_e) + g1*z_r1 + h[0]*z_s + h[1]*z_k_t + h[2]*z_c_t
    //                      + h[3]*z_e_t - t_bbs - a_bar*c = 0
    //
    // We combine them with multipliers (c, c², c³, 1) — a random linear
    // combination derived from the Fiat–Shamir challenge `c`.  By Schwartz–
    // Zippell, the combined check fails with probability ≤ 4/|Fr| ≈ 2⁻²⁵².
    // This replaces ~16 individual scalar multiplications with a single
    // 19-base Pippenger MSM.
    {
        let c_fr  = c.0;
        let c2_fr = c_fr * c_fr;
        let c3_fr = c2_fr * c_fr;
        let epoch_fr = Fr::from(current_epoch as u64);
        let fr_one = Fr::from(1u64);

        // Scalar coefficient for each basis.
        let sc_ht       = c_fr  * proof.z_k_tilde.0;
        let sc_nt       = -(c_fr * proof.z_r1.0);
        let sc_tscale_n = c_fr;
        let sc_tn       = -c_fr;
        // h[0]: c²·z_v + c³·z_w + z_s_tilde
        let sc_h0       = c2_fr * proof.z_v.0 + c3_fr * proof.z_w.0 + proof.z_s_tilde.0;
        // h[1]: c²·z_u + z_k_tilde
        let sc_h1       = c2_fr * proof.z_u.0 + proof.z_k_tilde.0;
        // h[2]: c²·(z_r1·T) + z_c_tilde
        let sc_h2       = c2_fr * (proof.z_r1.0 * epoch_fr) + proof.z_c_tilde.0;
        // h[3]: (c³ + 1)·z_e_tilde
        let sc_h3       = (c3_fr + fr_one) * proof.z_e_tilde.0;
        // h[4]: c²·z_c_tilde
        let sc_h4       = c2_fr * proof.z_c_tilde.0;
        let sc_g1       = proof.z_r1.0;
        let sc_aprime   = -proof.z_e.0;
        let sc_kdaily   = -(c2_fr * proof.z_r1.0);
        let sc_cbridge  = -(c3_fr * proof.z_r1.0);
        let sc_abar     = -c_fr;   // a_bar is scaled by Fiat-Shamir c
        let sc_td       = -c2_fr;
        let sc_tscale_d = c2_fr;
        let sc_tb       = -c3_fr;
        let sc_tscale_b = c3_fr;
        let sc_tbbs     = -fr_one;

        // Batch-normalize the 13 dynamic proof points in one field inversion.
        let dyn_pts = G1Projective::normalize_batch(&[
            h_t,
            proof.n_t,
            proof.t_scale_n,
            proof.t_n,
            proof.a_prime,
            proof.k_daily,
            c_bridge,
            proof.a_bar,
            proof.t_d,
            proof.t_scale_d,
            proof.t_b,
            proof.t_scale_b,
            proof.t_bbs,
        ]);

        // Build the combined MSM (19 bases total: 13 dynamic + 6 static).
        let bases = [
            dyn_pts[0],              // h_t
            dyn_pts[1],              // n_t
            dyn_pts[2],              // t_scale_n
            dyn_pts[3],              // t_n
            generators.h_affine[0], // h[0]
            generators.h_affine[1], // h[1]
            generators.h_affine[2], // h[2]
            generators.h_affine[3], // h[3]
            generators.h_affine[4], // h[4]
            generators.g1_affine,   // g1
            dyn_pts[4],              // a_prime
            dyn_pts[5],              // k_daily
            dyn_pts[6],              // c_bridge
            dyn_pts[7],              // a_bar
            dyn_pts[8],              // t_d
            dyn_pts[9],              // t_scale_d
            dyn_pts[10],             // t_b
            dyn_pts[11],             // t_scale_b
            dyn_pts[12],             // t_bbs
        ];
        let scalars = [
            sc_ht, sc_nt, sc_tscale_n, sc_tn,
            sc_h0, sc_h1, sc_h2, sc_h3, sc_h4,
            sc_g1, sc_aprime, sc_kdaily, sc_cbridge, sc_abar,
            sc_td, sc_tscale_d, sc_tb, sc_tscale_b, sc_tbbs,
        ];

        let combined = G1Projective::msm(&bases, &scalars)
            .map_err(|e| ActError::VerificationFailed(alloc::format!("MSM failed: {:?}", e)))?;
        if !combined.is_zero() {
            return Err(ActError::VerificationFailed(
                "Combined bridge+Schnorr check failed".into(),
            ));
        }
    }

    // 6. Bulletproof verification
    let mut bp_extra = Vec::with_capacity(32 + 4 + 6 * 48);
    bp_extra.extend_from_slice(&h_ctx.to_bytes());
    bp_extra.extend_from_slice(&current_epoch.to_le_bytes());
    proof.n_t.serialize_compressed(&mut bp_extra).unwrap();
    proof.k_daily.serialize_compressed(&mut bp_extra).unwrap();
    proof.c_delta.serialize_compressed(&mut bp_extra).unwrap();
    proof.a_prime.serialize_compressed(&mut bp_extra).unwrap();
    proof.a_bar.serialize_compressed(&mut bp_extra).unwrap();
    proof.t_bbs.serialize_compressed(&mut bp_extra).unwrap();
    verify_range(
        &proof.bp_exp,
        proof.c_delta,
        32,
        generators.h[3],
        generators.h[0],
        b"ACT:Expiry",
        &bp_extra,
    )?;

    // 7. Pairing check: e(A', pk_master) == e(A_bar, g2).
    // Combined into a single multi-pairing (one shared Miller loop + one final
    // exponentiation) rather than two separate pairings.
    let pairing_check = ark_bls12_381::Bls12_381::multi_pairing(
        [proof.a_prime.into_affine(), (-proof.a_bar).into_affine()],
        [(*pk_master).into_affine(), generators.g2.into_affine()],
    );
    if pairing_check.0 != Fq12::ONE {
        return Err(ActError::VerificationFailed("Pairing check failed".into()));
    }

    // 8. Issue Daily Token — use cached affines for the 3-base MSM.
    let e_daily = Scalar::rand(rng);
    let s_prime_daily = Scalar::rand(rng);
    let a_daily = {
        let k_daily_affine = proof.k_daily.into_affine();
        let bases = [generators.g1_affine, k_daily_affine, generators.h_affine[0]];
        let scalars = [Fr::from(1u64), Fr::from(1u64), s_prime_daily.0];
        let msg_part = G1Projective::msm(&bases, &scalars).expect("issue MSM length mismatch");
        let denom = e_daily + keys.sk_daily;
        let denom_inv = denom.0.inverse().unwrap();
        msg_part * denom_inv
    };

    Ok(RefreshResponse {
        a_daily,
        e_daily,
        s_prime_daily,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bbs_proof::BbsSignature;
    use crate::commitments::commit;
    use crate::hash::compute_h_ctx;
    use crate::setup::{Generators, ServerKeys};
    use crate::types::Scalar;
    use ark_std::rand::thread_rng;

    fn create_master_signature(
        rng: &mut impl RngCore,
        k_sub: Scalar,
        c_max: u32,
        e_max: u32,
        generators: &Generators,
        keys: &ServerKeys,
    ) -> (BbsSignature, Scalar) {
        let r_sub = Scalar::rand(rng);
        let k_sub_commit = commit(k_sub, r_sub, generators.h[1], generators.h[0]);
        let e_sub = Scalar::rand(rng);
        let s_prime_sub = Scalar::rand(rng);
        let bases = vec![
            generators.g1,
            k_sub_commit,
            generators.h[0],
            generators.h[2],
            generators.h[3],
        ];
        let scalars = vec![
            Scalar::ONE.0,
            Scalar::ONE.0,
            s_prime_sub.0,
            Scalar::from(c_max).0,
            Scalar::from(e_max).0,
        ];
        let msg_part = msm_projective(&bases, &scalars);
        let denom = e_sub + keys.sk_master;
        let a_sub = msg_part * denom.0.inverse().unwrap();
        let s_sub = r_sub + s_prime_sub;
        (BbsSignature { a: a_sub, e: e_sub, s: s_sub }, k_sub)
    }

    #[test]
    fn refresh_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx(
            "test-app",
            &keys.pk_master,
            &keys.pk_daily,
            &generators,
        );

        let k_sub = Scalar::rand_nonzero(&mut rng);
        let c_max = 100u32;
        let e_max = 5000u32;
        let current_epoch = 1000u32;

        let (master, _) = create_master_signature(
            &mut rng,
            k_sub,
            c_max,
            e_max,
            &generators,
            &keys,
        );

        // Client prepares proof
        let (client, proof) = RefreshProver::prove(
            &mut rng,
            &master,
            k_sub,
            c_max,
            e_max,
            current_epoch,
            &generators,
            &keys.pk_master,
            h_ctx,
        )
        .unwrap();

        // Server verifies
        let response = verify_refresh(
            &proof,
            current_epoch,
            &generators,
            &keys.pk_master,
            &keys,
            h_ctx,
            &mut rng,
        )
        .unwrap();

        // Client finalizes
        let (daily_sig, k_daily) = client.finalize(response);
        assert!(!daily_sig.a.is_zero());
        assert!(!k_daily.is_zero());
    }

    #[test]
    fn expired_token_rejected() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx(
            "test-app",
            &keys.pk_master,
            &keys.pk_daily,
            &generators,
        );

        let k_sub = Scalar::rand_nonzero(&mut rng);
        let c_max = 100;
        let e_max = 1000;
        let current_epoch = 2000; // expired

        let (master, _) = create_master_signature(
            &mut rng,
            k_sub,
            c_max,
            e_max,
            &generators,
            &keys,
        );

        let result = RefreshProver::prove(
            &mut rng,
            &master,
            k_sub,
            c_max,
            e_max,
            current_epoch,
            &generators,
            &keys.pk_master,
            h_ctx,
        );
        assert!(result.is_err());
    }
}
