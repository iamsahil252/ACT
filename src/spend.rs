//! Phase 3: Intra‑Day Spending
//!
//! The client spends a portion of the daily credits, producing a Refund Token
//! for the remaining balance. The spend proof demonstrates knowledge of a valid
//! Daily/Refund Token under the daily public key, discloses the token nullifier
//! `k_cur` and the issue epoch `T_issue`, and proves that the remaining balance
//! `m = c_bal - s` is non‑negative via a 32‑bit Bulletproof.
//!
//! The proof is bound to a session nonce `η` to prevent replay attacks.
//! The server verifies the proof, checks nullifier freshness, and issues a blind
//! Refund Token under the daily signing key.


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
use crate::batched_eq::{prove_batched_equality, verify_batched_equality, BatchedEqualityProof};
use crate::error::{ActError, Result};
use crate::hash::{hash_to_scalar_from_hasher, HasherWriter};
use crate::setup::{Generators, ServerKeys};
use crate::types::Scalar;

/// Efficient MSM using precomputed affine bases (no projective→affine conversion).
fn msm_projective(bases: &[G1Projective], scalars: &[Fr]) -> G1Projective {
    let affine = G1Projective::normalize_batch(bases);
    G1Projective::msm(&affine, scalars).expect("MSM length mismatch")
}

// ============================================================================
// Spend Proof Structure
// ============================================================================

/// The complete spend proof sent by the client.
#[derive(Clone, Debug)]
pub struct SpendProof {
    // BBS+ core proof elements
    pub a_prime: G1Projective,
    pub a_bar: G1Projective,
    pub t_bbs: G1Projective,

    // Bridging commitments
    pub t_scale_t: G1Projective,
    pub t_total: G1Projective,
    pub t_scale_r: G1Projective,
    pub t_refund: G1Projective,
    pub t_scale_bp: G1Projective,
    pub t_bp: G1Projective,

    // Responses
    pub z_e: Scalar,
    pub z_r1: Scalar,
    pub z_s_tilde: Scalar,
    pub z_c_tilde: Scalar,
    pub z_u: Scalar,
    pub z_v: Scalar,
    pub z_w: Scalar,

    /// Dual-curve equality proof for remaining balance, embedding the Dalek
    /// range proof for `m ∈ [0, 2³²−1]`.
    pub batched_eq: BatchedEqualityProof,

    // Public values (sent separately but included for convenience)
    pub s: u32,
    pub k_cur: Scalar,
    pub t_issue: u32,
    pub k_prime: G1Projective,
    pub c_bp: G1Projective,
}

/// Server response containing the blind Refund Token.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SpendResponse {
    #[serde(with = "crate::types::g1_serde")]
    pub a_refund: G1Projective,
    pub e_refund: Scalar,
    pub s_prime_refund: Scalar,
}

// ============================================================================
// Combined Spend Prover
// ============================================================================

/// Client state for spending.
pub struct SpendClient {
    /// The token being spent.
    token: BbsSignature,
    /// Token nullifier (disclosed).
    k_cur: Scalar,
    /// Current balance before spend.
    c_bal: u32,
    /// Epoch of issuance.
    t_issue: u32,
    /// Secret for the new Refund Token.
    k_star: Scalar,
    /// Blinding for the Refund Token commitment.
    pub r_star: Scalar,
    /// Blinding for the range proof commitment.
    r_bp: Scalar,
}

/// A prover that generates the complete spend proof.
pub struct SpendProver {
    // BBS+ core
    r1: Scalar,
    a_prime: G1Projective,
    a_bar: G1Projective,
    t_bbs: G1Projective,
    // Scaled secrets
    s_tilde: Scalar,
    c_tilde: Scalar,
    // BBS+ blinders
    rho_e: Scalar,
    rho_r1: Scalar,
    rho_s: Scalar,
    rho_c: Scalar,
    // External blinders
    rho_u: Scalar,
    rho_v: Scalar,
    rho_w: Scalar,
}

impl SpendProver {
    /// Generate the spend proof and return the client state.
    #[allow(clippy::too_many_arguments)]
    pub fn prove(
        rng: &mut (impl CryptoRng + RngCore),
        token: &BbsSignature,
        k_cur: Scalar,
        c_bal: u32,
        t_issue: u32,
        spend_amount: u32,
        nonce: &[u8; 16],
        generators: &Generators,
        pk_daily: &G2Projective,
        h_ctx: Scalar,
    ) -> Result<(SpendClient, SpendProof)> {
        // 1. Validate spend amount and compute remaining balance
        if spend_amount == 0 {
            return Err(ActError::ProtocolError("Spend amount must be positive".into()));
        }
        if spend_amount > c_bal {
            return Err(ActError::ProtocolError("Insufficient balance".into()));
        }
        let m = c_bal - spend_amount;

        // 2. Refund commitment
        let k_star = Scalar::rand_nonzero(rng);
        let r_star = Scalar::rand(rng);
        // K' = m * h4 + k_star * h1 + T_issue * h2 + r_star * h0
        let k_prime = generators.h[4] * Scalar::from(m).0
            + generators.h[1] * k_star.0
            + generators.h[2] * Scalar::from(t_issue).0
            + generators.h[0] * r_star.0;

        // 3. Range proof commitment for remaining balance
        let r_bp = Scalar::rand(rng);
        let c_bp = generators.h[4] * Scalar::from(m).0 + generators.h[0] * r_bp.0;

        // 4. BBS+ randomization and scaled secrets
        let r1 = Scalar::rand_nonzero(rng);
        let a_prime = token.a * r1.0;

        // Message part M = g1^1 * h0^s * h4^{c_bal} * h1^{k_cur} * h2^{T_issue}
        // Use pre-cached affine generators — no field inversions needed.
        let msg_part = {
            let bases = [
                generators.g1_affine,
                generators.h_affine[0],
                generators.h_affine[4],
                generators.h_affine[1],
                generators.h_affine[2],
            ];
            let scalars = [
                Fr::from(1u64),
                token.s.0,
                Fr::from(c_bal as u64),
                k_cur.0,
                Fr::from(t_issue as u64),
            ];
            G1Projective::msm(&bases, &scalars).expect("msg_part MSM length mismatch")
        };
        let a_bar = a_prime * (-token.e.0) + msg_part * r1.0;

        let s_tilde = token.s * r1;
        let c_tilde = Scalar::from(c_bal) * r1;

        // 5. BBS+ blinders
        let rho_e = Scalar::rand(rng);
        let rho_r1 = Scalar::rand(rng);
        let rho_s = Scalar::rand(rng);
        let rho_c = Scalar::rand(rng);

        // T_BBS includes disclosed messages: h1^{k_cur * rho_r1} and h2^{T_issue * rho_r1}
        // Use pre-cached affine generators for static bases.
        let t_bbs = {
            let a_prime_affine = a_prime.into_affine();
            let bases = [
                a_prime_affine,
                generators.g1_affine,
                generators.h_affine[0],
                generators.h_affine[4],
                generators.h_affine[1],
                generators.h_affine[2],
            ];
            let scalars = [
                -rho_e.0,
                rho_r1.0,
                rho_s.0,
                rho_c.0,
                (k_cur * rho_r1).0,
                (Scalar::from(t_issue) * rho_r1).0,
            ];
            G1Projective::msm(&bases, &scalars).expect("T_BBS MSM length mismatch")
        };

        // 6. External blinders
        let rho_u = Scalar::rand(rng);
        let rho_v = Scalar::rand(rng);
        let rho_w = Scalar::rand(rng);

        // 7. Bridging commitments
        // C_total = K' + s * h4
        let c_total = k_prime + generators.h[4] * Scalar::from(spend_amount).0;

        // T_scale_T = rho_r1 * C_total
        let t_scale_t = c_total * rho_r1.0;
        // T_total = rho_c * h4 + rho_u * h1 + rho_r1 * T_issue * h2 + rho_v * h0
        // (4-base MSM with cached affine generators)
        let t_total = {
            let bases = [
                generators.h_affine[4],
                generators.h_affine[1],
                generators.h_affine[2],
                generators.h_affine[0],
            ];
            let scalars = [
                rho_c.0,
                rho_u.0,
                (rho_r1 * Scalar::from(t_issue)).0,
                rho_v.0,
            ];
            G1Projective::msm(&bases, &scalars).expect("T_total MSM length mismatch")
        };

        // T_scale_R = rho_r1 * K'
        let t_scale_r = k_prime * rho_r1.0;
        // rho_m = rho_c - s * rho_r1
        let rho_m = rho_c - Scalar::from(spend_amount) * rho_r1;
        // T_refund = rho_m * h4 + rho_u * h1 + rho_r1 * T_issue * h2 + rho_v * h0
        let t_refund = {
            let bases = [
                generators.h_affine[4],
                generators.h_affine[1],
                generators.h_affine[2],
                generators.h_affine[0],
            ];
            let scalars = [
                rho_m.0,
                rho_u.0,
                (rho_r1 * Scalar::from(t_issue)).0,
                rho_v.0,
            ];
            G1Projective::msm(&bases, &scalars).expect("T_refund MSM length mismatch")
        };

        // T_scale_BP = rho_r1 * C_BP
        let t_scale_bp = c_bp * rho_r1.0;
        // T_BP = rho_m * h4 + rho_w * h0
        let t_bp = {
            let bases = [generators.h_affine[4], generators.h_affine[0]];
            let scalars = [rho_m.0, rho_w.0];
            G1Projective::msm(&bases, &scalars).expect("T_BP MSM length mismatch")
        };

        // 8. BatchedEqualityProof: prove m in C_BP (BLS12-381) equals m in
        //    C_25519 (Curve25519), and that m ∈ [0, 2³²−1] via Dalek Bulletproof.
        //
        // The context binds the proof to this specific spend session, preventing
        // transcript-splicing attacks as required by Section 9.2.
        let mut beq_context = Vec::new();
        beq_context.extend_from_slice(&h_ctx.to_bytes());
        beq_context.extend_from_slice(&spend_amount.to_le_bytes());
        beq_context.extend_from_slice(&k_cur.to_bytes());
        beq_context.extend_from_slice(&t_issue.to_le_bytes());
        beq_context.extend_from_slice(nonce);
        k_prime.serialize_compressed(&mut beq_context).unwrap();
        c_total.serialize_compressed(&mut beq_context).unwrap();
        a_prime.serialize_compressed(&mut beq_context).unwrap();
        a_bar.serialize_compressed(&mut beq_context).unwrap();
        t_bbs.serialize_compressed(&mut beq_context).unwrap();

        let (batched_eq, c_bp_from_beq) = prove_batched_equality(
            rng,
            m,
            r_bp.0,
            generators.h[4],
            generators.h[0],
            &beq_context,
        )?;
        // Sanity: c_bp_from_beq must match c_bp (same m and r_bp).
        debug_assert_eq!(c_bp, c_bp_from_beq, "c_bp mismatch");
        let beq_bytes = batched_eq.to_bytes();

        // 9. Challenge — feed all elements directly into SHA-256, no intermediate Vec.
        let c = {
            let mut hasher = sha2::Sha256::new();
            let mut w = HasherWriter(&mut hasher);
            w.write_all(&h_ctx.to_bytes()).unwrap();
            pk_daily.serialize_compressed(&mut w).unwrap();
            w.write_all(&spend_amount.to_le_bytes()).unwrap();
            w.write_all(&k_cur.to_bytes()).unwrap();
            w.write_all(&t_issue.to_le_bytes()).unwrap();
            w.write_all(nonce).unwrap();
            k_prime.serialize_compressed(&mut w).unwrap();
            c_total.serialize_compressed(&mut w).unwrap();
            c_bp.serialize_compressed(&mut w).unwrap();
            w.write_all(&beq_bytes).unwrap();
            a_prime.serialize_compressed(&mut w).unwrap();
            a_bar.serialize_compressed(&mut w).unwrap();
            t_bbs.serialize_compressed(&mut w).unwrap();
            t_scale_t.serialize_compressed(&mut w).unwrap();
            t_total.serialize_compressed(&mut w).unwrap();
            t_scale_r.serialize_compressed(&mut w).unwrap();
            t_refund.serialize_compressed(&mut w).unwrap();
            t_scale_bp.serialize_compressed(&mut w).unwrap();
            t_bp.serialize_compressed(&mut w).unwrap();
            w.write_all(b"Spend").unwrap();
            drop(w);
            hash_to_scalar_from_hasher(hasher)
        };

        // 10. Responses
        let z_e = rho_e + c * token.e;
        let z_r1 = rho_r1 + c * r1;
        let z_s_tilde = rho_s + c * s_tilde;
        let z_c_tilde = rho_c + c * c_tilde;
        let z_u = rho_u + c * (k_star * r1);
        let z_v = rho_v + c * (r_star * r1);
        let z_w = rho_w + c * (r_bp * r1);

        let proof = SpendProof {
            a_prime,
            a_bar,
            t_bbs,
            t_scale_t,
            t_total,
            t_scale_r,
            t_refund,
            t_scale_bp,
            t_bp,
            z_e,
            z_r1,
            z_s_tilde,
            z_c_tilde,
            z_u,
            z_v,
            z_w,
            batched_eq,
            s: spend_amount,
            k_cur,
            t_issue,
            k_prime,
            c_bp,
        };

        let client = SpendClient {
            token: token.clone(),
            k_cur,
            c_bal,
            t_issue,
            k_star,
            r_star,
            r_bp,
        };

        Ok((client, proof))
    }
}

// ============================================================================
// Server Verification
// ============================================================================

/// Verify a spend proof and issue a Refund Token.
pub fn verify_spend(
    proof: &SpendProof,
    current_epoch: u32,
    nonce: &[u8; 16],
    generators: &Generators,
    pk_daily: &G2Projective,
    keys: &ServerKeys,
    h_ctx: Scalar,
    rng: &mut impl RngCore,
) -> Result<SpendResponse> {
    // 1. Spend amount validation
    if proof.s == 0 {
        return Err(ActError::VerificationFailed("Spend amount must be positive".into()));
    }

    // 2. Epoch check (with grace period)
    if proof.t_issue != current_epoch && proof.t_issue != current_epoch - 1 {
        return Err(ActError::VerificationFailed("Epoch mismatch".into()));
    }

    // 3. Basic bounds
    if proof.a_prime.is_zero() || proof.t_bbs.is_zero() {
        return Err(ActError::VerificationFailed("Zero point in proof".into()));
    }

    // 4. Spend bridge: C_total = K' + s * h4
    let c_total = proof.k_prime + generators.h[4] * Scalar::from(proof.s).0;

    // 5. Recompute challenge — feed all elements directly into SHA-256.
    let beq_bytes = proof.batched_eq.to_bytes();
    let c = {
        let mut hasher = sha2::Sha256::new();
        let mut w = HasherWriter(&mut hasher);
        w.write_all(&h_ctx.to_bytes()).unwrap();
        pk_daily.serialize_compressed(&mut w).unwrap();
        w.write_all(&proof.s.to_le_bytes()).unwrap();
        w.write_all(&proof.k_cur.to_bytes()).unwrap();
        w.write_all(&proof.t_issue.to_le_bytes()).unwrap();
        w.write_all(nonce).unwrap();
        proof.k_prime.serialize_compressed(&mut w).unwrap();
        c_total.serialize_compressed(&mut w).unwrap();
        proof.c_bp.serialize_compressed(&mut w).unwrap();
        w.write_all(&beq_bytes).unwrap();
        proof.a_prime.serialize_compressed(&mut w).unwrap();
        proof.a_bar.serialize_compressed(&mut w).unwrap();
        proof.t_bbs.serialize_compressed(&mut w).unwrap();
        proof.t_scale_t.serialize_compressed(&mut w).unwrap();
        proof.t_total.serialize_compressed(&mut w).unwrap();
        proof.t_scale_r.serialize_compressed(&mut w).unwrap();
        proof.t_refund.serialize_compressed(&mut w).unwrap();
        proof.t_scale_bp.serialize_compressed(&mut w).unwrap();
        proof.t_bp.serialize_compressed(&mut w).unwrap();
        w.write_all(b"Spend").unwrap();
        drop(w);
        hash_to_scalar_from_hasher(hasher)
    };

    // 6. Derived response z_m = z_c_tilde - s * z_r1
    let z_m = proof.z_c_tilde - Scalar::from(proof.s) * proof.z_r1;

    // 7. Combined batch check for all four bridge + Schnorr equations.
    //
    // Rather than checking separately:
    //   Eq1 (Total):   h[4]*z_c + h[1]*z_u + h[2]*(z_r1·T) + h[0]*z_v - c_total*z_r1 - t_total + t_scale_t = 0
    //   Eq2 (Refund):  h[4]*z_m + h[1]*z_u + h[2]*(z_r1·T) + h[0]*z_v - k_prime*z_r1 - t_refund + t_scale_r = 0
    //   Eq3 (Range):   h[4]*z_m + h[0]*z_w - c_bp*z_r1 - t_bp + t_scale_bp = 0
    //   Eq4 (Schnorr): a'*(-z_e) + g1*z_r1 + h[0]*z_s + h[4]*z_c + h[1]*(k_cur·z_r1)
    //                  + h[2]*(T·z_r1) - t_bbs - a_bar*c = 0
    //
    // We combine with multipliers (c, c², c³, 1). Soundness error ≤ 4/|Fr| ≈ 2⁻²⁵².
    // This replaces ~4 separate checks (and ~19 scalar muls) with a single 17-base
    // Pippenger MSM.
    {
        let c_fr  = c.0;
        let c2_fr = c_fr * c_fr;
        let c3_fr = c2_fr * c_fr;
        let t_issue_fr = Fr::from(proof.t_issue as u64);
        let s_fr       = Fr::from(proof.s as u64);
        let fr_one = Fr::from(1u64);

        // z_m in field form
        let z_m_fr = z_m.0;

        // Scalar coefficient for each basis:
        // h[0]: c·z_v + c²·z_v + c³·z_w + z_s_tilde = (c+c²)·z_v + c³·z_w + z_s_tilde
        let sc_h0 = (c_fr + c2_fr) * proof.z_v.0 + c3_fr * proof.z_w.0 + proof.z_s_tilde.0;
        // h[1]: c·z_u + c²·z_u + k_cur·z_r1 = (c+c²)·z_u + k_cur·z_r1
        let sc_h1 = (c_fr + c2_fr) * proof.z_u.0 + proof.k_cur.0 * proof.z_r1.0;
        // h[2]: c·(z_r1·T) + c²·(z_r1·T) + T·z_r1 = (c+c²+1)·T·z_r1
        let sc_h2 = (c_fr + c2_fr + fr_one) * t_issue_fr * proof.z_r1.0;
        // h[4]: c·z_c + c²·z_m + c³·z_m + z_c
        //      = (c+1)·z_c + (c²+c³)·z_m
        //      = (c+1)·z_c + (c²+c³)·(z_c - s·z_r1)
        //      = (c+1+c²+c³)·z_c - (c²+c³)·s·z_r1
        let sc_h4 = (c_fr + fr_one + c2_fr + c3_fr) * proof.z_c_tilde.0
                    - (c2_fr + c3_fr) * s_fr * proof.z_r1.0;
        let sc_g1     = proof.z_r1.0;
        let sc_aprime = -proof.z_e.0;
        let sc_ctotal = -(c_fr * proof.z_r1.0);
        let sc_kprime = -(c2_fr * proof.z_r1.0);
        let sc_cbp    = -(c3_fr * proof.z_r1.0);
        let sc_abar   = -c_fr;
        let sc_ttotal    = -c_fr;
        let sc_tscale_t  =  c_fr;
        let sc_trefund   = -c2_fr;
        let sc_tscale_r  =  c2_fr;
        let sc_tbp       = -c3_fr;
        let sc_tscale_bp =  c3_fr;
        let sc_tbbs      = -fr_one;

        // Suppress unused z_m_fr warning; it was expanded inline above.
        let _ = z_m_fr;

        // Batch-normalize the 11 dynamic proof points in one field inversion.
        let dyn_pts = G1Projective::normalize_batch(&[
            proof.a_prime,
            c_total,
            proof.k_prime,
            proof.c_bp,
            proof.a_bar,
            proof.t_total,
            proof.t_scale_t,
            proof.t_refund,
            proof.t_scale_r,
            proof.t_bp,
            proof.t_scale_bp,
            proof.t_bbs,
        ]);

        // Build the combined MSM (17 bases total: 11 dynamic + 6 static).
        let bases = [
            generators.h_affine[0], // h[0]
            generators.h_affine[1], // h[1]
            generators.h_affine[2], // h[2]
            generators.h_affine[4], // h[4]
            generators.g1_affine,   // g1
            dyn_pts[0],              // a_prime
            dyn_pts[1],              // c_total
            dyn_pts[2],              // k_prime
            dyn_pts[3],              // c_bp
            dyn_pts[4],              // a_bar
            dyn_pts[5],              // t_total
            dyn_pts[6],              // t_scale_t
            dyn_pts[7],              // t_refund
            dyn_pts[8],              // t_scale_r
            dyn_pts[9],              // t_bp
            dyn_pts[10],             // t_scale_bp
            dyn_pts[11],             // t_bbs
        ];
        let scalars = [
            sc_h0, sc_h1, sc_h2, sc_h4, sc_g1,
            sc_aprime, sc_ctotal, sc_kprime, sc_cbp, sc_abar,
            sc_ttotal, sc_tscale_t, sc_trefund, sc_tscale_r,
            sc_tbp, sc_tscale_bp, sc_tbbs,
        ];

        let combined = G1Projective::msm(&bases, &scalars)
            .map_err(|e| ActError::VerificationFailed(alloc::format!("MSM failed: {:?}", e)))?;
        if !combined.is_zero() {
            return Err(ActError::VerificationFailed(
                "Combined bridge+Schnorr check failed".into(),
            ));
        }
    }

    // 8. BatchedEqualityProof verification: checks that m in C_BP (BLS12-381)
    //    equals m in C_25519 (Curve25519), and that m ∈ [0, 2³²−1] via Dalek.
    //
    //    The beq_context mirrors what the prover bound into the inner challenge.
    let mut beq_context = Vec::new();
    beq_context.extend_from_slice(&h_ctx.to_bytes());
    beq_context.extend_from_slice(&proof.s.to_le_bytes());
    beq_context.extend_from_slice(&proof.k_cur.to_bytes());
    beq_context.extend_from_slice(&proof.t_issue.to_le_bytes());
    beq_context.extend_from_slice(nonce);
    proof.k_prime.serialize_compressed(&mut beq_context).unwrap();
    c_total.serialize_compressed(&mut beq_context).unwrap();
    proof.a_prime.serialize_compressed(&mut beq_context).unwrap();
    proof.a_bar.serialize_compressed(&mut beq_context).unwrap();
    proof.t_bbs.serialize_compressed(&mut beq_context).unwrap();
    verify_batched_equality(
        &proof.batched_eq,
        proof.c_bp,
        generators.h[4],
        generators.h[0],
        &beq_context,
    )?;

    // 9. Pairing check: e(A', pk_daily) == e(A_bar, g2).
    // Combined into a single multi-pairing (one shared Miller loop + one final
    // exponentiation) rather than two separate pairings.
    // Uses precomputed G2Prepared line functions to skip per-call preparation.
    let pairing_check = ark_bls12_381::Bls12_381::multi_pairing(
        [proof.a_prime.into_affine(), (-proof.a_bar).into_affine()],
        [keys.pk_daily_prepared.clone(), generators.g2_prepared.clone()],
    );
    if pairing_check.0 != Fq12::ONE {
        return Err(ActError::VerificationFailed("Pairing check failed".into()));
    }

    // 10. Issue Refund Token — use cached affines for the 3-base MSM.
    let e_refund = Scalar::rand(rng);
    let s_prime_refund = Scalar::rand(rng);
    let a_refund = {
        let k_prime_affine = proof.k_prime.into_affine();
        let bases = [generators.g1_affine, k_prime_affine, generators.h_affine[0]];
        let scalars = [Fr::from(1u64), Fr::from(1u64), s_prime_refund.0];
        let msg_part = G1Projective::msm(&bases, &scalars).expect("issue MSM length mismatch");
        let denom = e_refund + keys.sk_daily;
        let denom_inv = denom.0.inverse().unwrap();
        msg_part * denom_inv
    };

    Ok(SpendResponse {
        a_refund,
        e_refund,
        s_prime_refund,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bbs_proof::BbsSignature;
    use crate::hash::compute_h_ctx;
    use crate::setup::{Generators, ServerKeys};
    use crate::types::Scalar;
    use ark_std::rand::thread_rng;

    fn create_daily_signature(
        rng: &mut impl RngCore,
        k_daily: Scalar,
        c_bal: u32,
        t_issue: u32,
        generators: &Generators,
        keys: &ServerKeys,
    ) -> BbsSignature {
        let r_daily = Scalar::rand(rng);
        let k_daily_commit = generators.h[4] * Scalar::from(c_bal).0
            + generators.h[1] * k_daily.0
            + generators.h[2] * Scalar::from(t_issue).0
            + generators.h[0] * r_daily.0;
        let e_daily = Scalar::rand(rng);
        let s_prime_daily = Scalar::rand(rng);
        let msg_part = generators.g1 + k_daily_commit + generators.h[0] * s_prime_daily.0;
        let denom = e_daily + keys.sk_daily;
        let a_daily = msg_part * denom.0.inverse().unwrap();
        let s_daily = r_daily + s_prime_daily;
        BbsSignature { a: a_daily, e: e_daily, s: s_daily }
    }

    #[test]
    fn spend_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx(
            "test-app",
            &keys.pk_master,
            &keys.pk_daily,
            &generators,
        );

        let k_cur = Scalar::rand_nonzero(&mut rng);
        let c_bal = 100u32;
        let t_issue = 42u32;
        let token = create_daily_signature(
            &mut rng,
            k_cur,
            c_bal,
            t_issue,
            &generators,
            &keys,
        );

        let spend_amount = 30u32;
        let nonce = [0xAAu8; 16];

        // Client prepares proof
        let (client, proof) = SpendProver::prove(
            &mut rng,
            &token,
            k_cur,
            c_bal,
            t_issue,
            spend_amount,
            &nonce,
            &generators,
            &keys.pk_daily,
            h_ctx,
        )
        .unwrap();

        // Server verifies
        let response = verify_spend(
            &proof,
            t_issue,
            &nonce,
            &generators,
            &keys.pk_daily,
            &keys,
            h_ctx,
            &mut rng,
        )
        .unwrap();

        // Client finalizes
        let s_refund = client.r_star + response.s_prime_refund;
        let refund_sig = BbsSignature {
            a: response.a_refund,
            e: response.e_refund,
            s: s_refund,
        };
        assert!(!refund_sig.a.is_zero());
        assert_eq!(client.c_bal - spend_amount, 70);
    }

    #[test]
    fn overspend_rejected() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx(
            "test-app",
            &keys.pk_master,
            &keys.pk_daily,
            &generators,
        );

        let k_cur = Scalar::rand_nonzero(&mut rng);
        let c_bal = 50u32;
        let t_issue = 42u32;
        let token = create_daily_signature(
            &mut rng,
            k_cur,
            c_bal,
            t_issue,
            &generators,
            &keys,
        );

        let spend_amount = 100u32;
        let nonce = [0xAAu8; 16];

        let result = SpendProver::prove(
            &mut rng,
            &token,
            k_cur,
            c_bal,
            t_issue,
            spend_amount,
            &nonce,
            &generators,
            &keys.pk_daily,
            h_ctx,
        );
        assert!(result.is_err());
    }

    #[test]
    fn tampered_nonce_fails() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx(
            "test-app",
            &keys.pk_master,
            &keys.pk_daily,
            &generators,
        );

        let k_cur = Scalar::rand_nonzero(&mut rng);
        let c_bal = 100u32;
        let t_issue = 42u32;
        let token = create_daily_signature(
            &mut rng,
            k_cur,
            c_bal,
            t_issue,
            &generators,
            &keys,
        );

        let spend_amount = 30u32;
        let nonce = [0xAAu8; 16];

        let (_client, proof) = SpendProver::prove(
            &mut rng,
            &token,
            k_cur,
            c_bal,
            t_issue,
            spend_amount,
            &nonce,
            &generators,
            &keys.pk_daily,
            h_ctx,
        )
        .unwrap();

        let wrong_nonce = [0xBBu8; 16];
        let result = verify_spend(
            &proof,
            t_issue,
            &wrong_nonce,
            &generators,
            &keys.pk_daily,
            &keys,
            h_ctx,
            &mut rng,
        );
        assert!(result.is_err());
    }
}
