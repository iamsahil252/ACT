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
use ark_std::vec;
use ark_bls12_381::{G1Projective, G2Projective};
use ark_ec::{CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{Field, PrimeField};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::RngCore;
use ark_std::Zero;
use crate::bbs_proof::{BbsProof, BbsProofContext, BbsSignature};
use crate::bulletproofs::{prove_range, verify_range, RangeProof};
use crate::commitments::{verify_bridge, verify_bridge_single_base};
use crate::error::{ActError, Result};
use crate::hash::{hash_to_scalar};
use crate::setup::{Generators, ServerKeys};
use crate::types::Scalar;

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

    // Range proof for remaining balance
    pub bp_spend: RangeProof,

    // Public values (sent separately but included for convenience)
    pub s: u32,
    pub k_cur: Scalar,
    pub t_issue: u32,
    pub k_prime: G1Projective,
    pub c_bp: G1Projective,
}

/// Server response containing the blind Refund Token.
#[derive(Clone, Debug)]
pub struct SpendResponse {
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
        rng: &mut impl RngCore,
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

        // Message part M = g1 * h0^s * h4^{c_bal} * h1^{k_cur} * h2^{T_issue}
        let msg_part = {
            let bases = vec![
                generators.g1,
                generators.h[0],
                generators.h[4],
                generators.h[1],
                generators.h[2],
            ];
            let scalars = vec![
                Scalar::ONE.0,
                token.s.0,
                Scalar::from(c_bal).0,
                k_cur.0,
                Scalar::from(t_issue).0,
            ];
            G1Projective::msm(&bases, &scalars).unwrap()
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
        let t_bbs = {
            let bases = vec![
                a_prime.into_affine(),
                generators.g1.into_affine(),
                generators.h[0].into_affine(),
                generators.h[4].into_affine(),
                generators.h[1].into_affine(),
                generators.h[2].into_affine(),
            ];
            let scalars = vec![
                -rho_e.0,
                rho_r1.0,
                rho_s.0,
                rho_c.0,
                (k_cur * rho_r1).0,
                (Scalar::from(t_issue) * rho_r1).0,
            ];
            G1Projective::msm(&bases, &scalars).unwrap()
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
        let t_total = generators.h[4] * rho_c.0
            + generators.h[1] * rho_u.0
            + generators.h[2] * (rho_r1 * Scalar::from(t_issue)).0
            + generators.h[0] * rho_v.0;

        // T_scale_R = rho_r1 * K'
        let t_scale_r = k_prime * rho_r1.0;
        // rho_m = rho_c - s * rho_r1
        let rho_m = rho_c - Scalar::from(spend_amount) * rho_r1;
        // T_refund = rho_m * h4 + rho_u * h1 + rho_r1 * T_issue * h2 + rho_v * h0
        let t_refund = generators.h[4] * rho_m.0
            + generators.h[1] * rho_u.0
            + generators.h[2] * (rho_r1 * Scalar::from(t_issue)).0
            + generators.h[0] * rho_v.0;

        // T_scale_BP = rho_r1 * C_BP
        let t_scale_bp = c_bp * rho_r1.0;
        // T_BP = rho_m * h4 + rho_w * h0
        let t_bp = generators.h[4] * rho_m.0 + generators.h[0] * rho_w.0;

        // 8. Generate Bulletproof (needs BBS+ commitments in extra data)
        let mut bp_extra = Vec::new();
        bp_extra.extend_from_slice(&h_ctx.to_bytes());
        bp_extra.extend_from_slice(&spend_amount.to_le_bytes());
        bp_extra.extend_from_slice(&k_cur.0.into_bigint().to_bytes_le());
        bp_extra.extend_from_slice(&t_issue.to_le_bytes());
        bp_extra.extend_from_slice(nonce);
        k_prime.serialize_compressed(&mut bp_extra).unwrap();
        c_total.serialize_compressed(&mut bp_extra).unwrap();
        c_bp.serialize_compressed(&mut bp_extra).unwrap();
        a_prime.serialize_compressed(&mut bp_extra).unwrap();
        a_bar.serialize_compressed(&mut bp_extra).unwrap();
        t_bbs.serialize_compressed(&mut bp_extra).unwrap();
        let (bp_spend, _) = prove_range(
            rng,
            m as u64,
            r_bp,
            32,
            generators.h[4],
            generators.h[0],
            b"ACT:Spend",
            &bp_extra,
        )?;

        // 9. Challenge
        let mut preimage = Vec::new();
        preimage.extend_from_slice(&h_ctx.to_bytes());
        pk_daily.serialize_compressed(&mut preimage).unwrap();
        preimage.extend_from_slice(&spend_amount.to_le_bytes());
        preimage.extend_from_slice(&k_cur.0.into_bigint().to_bytes_le());
        preimage.extend_from_slice(&t_issue.to_le_bytes());
        preimage.extend_from_slice(nonce);
        k_prime.serialize_compressed(&mut preimage).unwrap();
        c_total.serialize_compressed(&mut preimage).unwrap();
        c_bp.serialize_compressed(&mut preimage).unwrap();
        bp_spend.serialize_compressed(&mut preimage).unwrap();
        a_prime.serialize_compressed(&mut preimage).unwrap();
        a_bar.serialize_compressed(&mut preimage).unwrap();
        t_bbs.serialize_compressed(&mut preimage).unwrap();
        t_scale_t.serialize_compressed(&mut preimage).unwrap();
        t_total.serialize_compressed(&mut preimage).unwrap();
        t_scale_r.serialize_compressed(&mut preimage).unwrap();
        t_refund.serialize_compressed(&mut preimage).unwrap();
        t_scale_bp.serialize_compressed(&mut preimage).unwrap();
        t_bp.serialize_compressed(&mut preimage).unwrap();
        preimage.extend_from_slice(b"Spend");
        let c = hash_to_scalar(&preimage);

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
            bp_spend,
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

    // 5. Recompute challenge
    let mut preimage = Vec::new();
    preimage.extend_from_slice(&h_ctx.to_bytes());
    pk_daily.serialize_compressed(&mut preimage).unwrap();
    preimage.extend_from_slice(&proof.s.to_le_bytes());
    preimage.extend_from_slice(&proof.k_cur.0.into_bigint().to_bytes_le());
    preimage.extend_from_slice(&proof.t_issue.to_le_bytes());
    preimage.extend_from_slice(nonce);
    proof.k_prime.serialize_compressed(&mut preimage).unwrap();
    c_total.serialize_compressed(&mut preimage).unwrap();
    proof.c_bp.serialize_compressed(&mut preimage).unwrap();
    proof.bp_spend.serialize_compressed(&mut preimage).unwrap();
    proof.a_prime.serialize_compressed(&mut preimage).unwrap();
    proof.a_bar.serialize_compressed(&mut preimage).unwrap();
    proof.t_bbs.serialize_compressed(&mut preimage).unwrap();
    proof.t_scale_t.serialize_compressed(&mut preimage).unwrap();
    proof.t_total.serialize_compressed(&mut preimage).unwrap();
    proof.t_scale_r.serialize_compressed(&mut preimage).unwrap();
    proof.t_refund.serialize_compressed(&mut preimage).unwrap();
    proof.t_scale_bp.serialize_compressed(&mut preimage).unwrap();
    proof.t_bp.serialize_compressed(&mut preimage).unwrap();
    preimage.extend_from_slice(b"Spend");
    let c = hash_to_scalar(&preimage);

    // 6. Derived response z_m = z_c_tilde - s * z_r1
    let z_m = proof.z_c_tilde - Scalar::from(proof.s) * proof.z_r1;

    // 7. Bridging equalities

    // Total bridge
    let lhs_t = generators.h[4] * proof.z_c_tilde.0
        + generators.h[1] * proof.z_u.0
        + generators.h[2] * (proof.z_r1 * Scalar::from(proof.t_issue)).0
        + generators.h[0] * proof.z_v.0
        - proof.t_total;
    let rhs_t = c_total * proof.z_r1.0 - proof.t_scale_t;
    if lhs_t != rhs_t {
        return Err(ActError::VerificationFailed("Total bridge failed".into()));
    }

    // Refund bridge
    let lhs_r = generators.h[4] * z_m.0
        + generators.h[1] * proof.z_u.0
        + generators.h[2] * (proof.z_r1 * Scalar::from(proof.t_issue)).0
        + generators.h[0] * proof.z_v.0
        - proof.t_refund;
    let rhs_r = proof.k_prime * proof.z_r1.0 - proof.t_scale_r;
    if lhs_r != rhs_r {
        return Err(ActError::VerificationFailed("Refund bridge failed".into()));
    }

    // Range bridge
    let lhs_bp = generators.h[4] * z_m.0 + generators.h[0] * proof.z_w.0 - proof.t_bp;
    let rhs_bp = proof.c_bp * proof.z_r1.0 - proof.t_scale_bp;
    if lhs_bp != rhs_bp {
        return Err(ActError::VerificationFailed("Range bridge failed".into()));
    }

    // 8. Schnorr MSM (BBS+ core with disclosed messages)
    let lhs_msm = {
        let bases = vec![
            proof.a_prime.into_affine(),
            generators.g1.into_affine(),
            generators.h[0].into_affine(),
            generators.h[4].into_affine(),
            generators.h[1].into_affine(),
            generators.h[2].into_affine(),
        ];
        let scalars = vec![
            -proof.z_e.0,
            proof.z_r1.0,
            proof.z_s_tilde.0,
            proof.z_c_tilde.0,
            (proof.k_cur * proof.z_r1).0,
            (Scalar::from(proof.t_issue) * proof.z_r1).0,
        ];
        G1Projective::msm(&bases, &scalars).unwrap()
    };
    let rhs_msm = proof.t_bbs + proof.a_bar * c.0;
    if lhs_msm != rhs_msm {
        return Err(ActError::VerificationFailed("Schnorr check failed".into()));
    }

    // 9. Bulletproof verification
    let mut bp_extra = Vec::new();
    bp_extra.extend_from_slice(&h_ctx.to_bytes());
    bp_extra.extend_from_slice(&proof.s.to_le_bytes());
    bp_extra.extend_from_slice(&proof.k_cur.0.into_bigint().to_bytes_le());
    bp_extra.extend_from_slice(&proof.t_issue.to_le_bytes());
    bp_extra.extend_from_slice(nonce);
    proof.k_prime.serialize_compressed(&mut bp_extra).unwrap();
    c_total.serialize_compressed(&mut bp_extra).unwrap();
    proof.c_bp.serialize_compressed(&mut bp_extra).unwrap();
    proof.a_prime.serialize_compressed(&mut bp_extra).unwrap();
    proof.a_bar.serialize_compressed(&mut bp_extra).unwrap();
    proof.t_bbs.serialize_compressed(&mut bp_extra).unwrap();
    verify_range(
        &proof.bp_spend,
        proof.c_bp,
        32,
        generators.h[4],
        generators.h[0],
        b"ACT:Spend",
        &bp_extra,
    )?;

    // 10. Pairing check
    let pairing_left = ark_bls12_381::Bls12_381::pairing(proof.a_prime, *pk_daily);
    let pairing_right = ark_bls12_381::Bls12_381::pairing(proof.a_bar, generators.g2);
    if pairing_left.0 != pairing_right.0 {
        return Err(ActError::VerificationFailed("Pairing check failed".into()));
    }

    // 11. Issue Refund Token
    let e_refund = Scalar::rand(rng);
    let s_prime_refund = Scalar::rand(rng);
    let a_refund = {
        let bases = vec![
            generators.g1,
            proof.k_prime,
            generators.h[0],
        ];
        let scalars = vec![
            Scalar::ONE.0,
            Scalar::ONE.0,
            s_prime_refund.0,
        ];
        let msg_part = G1Projective::msm(&bases, &scalars).unwrap();
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
    use crate::commitments::commit;
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
