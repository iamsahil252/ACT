//! Phase 3: Intra-Day Spending.

extern crate alloc;
use alloc::vec::Vec;

use blstrs::{Bls12, G1Affine, G1Projective, G2Projective, Gt, Scalar as BlsScalar};
use ff::Field as _;
use group::Group as _;
use pairing::{MultiMillerLoop as _, MillerLoopResult as _};
use rand_chacha::ChaCha20Rng;
use rand_core::{CryptoRng, RngCore, SeedableRng as _};
use sha2::{Digest as _, Sha256};
use std::io::Write as _;

use crate::bbs_proof::BbsSignature;
use crate::batched_eq::{prove_batched_equality, verify_batched_equality, BatchedEqualityProof};
use crate::error::{ActError, Result};
use crate::hash::{hash_to_scalar_from_hasher, write_g1, write_g2, write_scalar, HasherWriter};
use crate::msm::{batch_normalize, g1_msm};
use crate::setup::{Generators, ServerKeys};
use crate::types::Scalar;
#[cfg(feature = "std")]
use rayon;

// ============================================================================
// Structures
// ============================================================================

#[derive(Clone, Debug)]
pub struct SpendProof {
    pub a_prime:    G1Projective,
    pub a_bar:      G1Projective,
    pub t_bbs:      G1Projective,
    pub t_scale_t:  G1Projective,
    pub t_total:    G1Projective,
    pub t_scale_r:  G1Projective,
    pub t_refund:   G1Projective,
    pub t_scale_bp: G1Projective,
    pub t_bp:       G1Projective,
    pub z_e:        Scalar,
    pub z_r1:       Scalar,
    pub z_s_tilde:  Scalar,
    pub z_c_tilde:  Scalar,
    pub z_u:        Scalar,
    pub z_v:        Scalar,
    pub z_w:        Scalar,
    pub batched_eq: BatchedEqualityProof,
    pub s:          u32,
    pub k_cur:      Scalar,
    pub t_issue:    u32,
    pub k_prime:    G1Projective,
    pub c_bp:       G1Projective,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SpendResponse {
    #[serde(with = "crate::types::g1_serde")]
    pub a_refund:       G1Projective,
    pub e_refund:       Scalar,
    pub s_prime_refund: Scalar,
}

pub struct SpendClient {
    pub k_cur:   Scalar,
    pub c_bal:   u32,
    pub t_issue: u32,
    pub k_star:  Scalar,
    pub r_star:  Scalar,
    r_bp:        Scalar,
}

// ============================================================================
// Prover
// ============================================================================

pub struct SpendProver;

impl SpendProver {
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
        if spend_amount == 0 {
            return Err(ActError::ProtocolError("Spend amount must be positive".into()));
        }
        if spend_amount > c_bal {
            return Err(ActError::ProtocolError("Insufficient balance".into()));
        }
        let m = c_bal - spend_amount;

        // Seed a ChaCha20Rng from 32 bytes of OS/caller entropy.
        // This makes all subsequent blinder generation virtually free (SIMD stream)
        // while still being cryptographically secure.
        let mut seed = [0u8; 32];
        rng.fill_bytes(&mut seed);
        let mut fast_rng = ChaCha20Rng::from_seed(seed);

        // Refund commitment K' = m·h4 + k_star·h1 + T_issue·h2 + r_star·h0
        let k_star = Scalar::rand_nonzero(&mut fast_rng);
        let r_star = Scalar::rand(&mut fast_rng);
        let k_prime = &(&(&generators.h[4] * &Scalar::from(m).0)
            + &(&generators.h[1] * &k_star.0))
            + &(&(&generators.h[2] * &Scalar::from(t_issue).0)
            + &(&generators.h[0] * &r_star.0));

        // Range proof commitment C_BP = m·h4 + r_bp·h0
        let r_bp  = Scalar::rand(&mut fast_rng);
        let c_bp  = &(&generators.h[4] * &Scalar::from(m).0) + &(&generators.h[0] * &r_bp.0);

        // BBS+ randomization
        let r1      = Scalar::rand_nonzero(&mut fast_rng);
        let a_prime = &token.a * &r1.0;

        let msg_part = g1_msm(
            &[generators.g1_affine, generators.h_affine[0], generators.h_affine[4],
              generators.h_affine[1], generators.h_affine[2]],
            &[BlsScalar::ONE, token.s.0, BlsScalar::from(c_bal as u64),
              k_cur.0, BlsScalar::from(t_issue as u64)],
        );
        let a_bar = &(&a_prime * &(-token.e.0)) + &(&msg_part * &r1.0);

        let s_tilde = token.s * r1;
        let c_tilde = Scalar::from(c_bal) * r1;

        let (rho_e, rho_r1, rho_s, rho_c) = (
            Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng),
            Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng),
        );

        let a_prime_aff = G1Affine::from(a_prime);
        let t_bbs = g1_msm(
            &[a_prime_aff, generators.g1_affine, generators.h_affine[0],
              generators.h_affine[4], generators.h_affine[1], generators.h_affine[2]],
            &[(-rho_e).0, rho_r1.0, rho_s.0, rho_c.0,
              (k_cur * rho_r1).0, (Scalar::from(t_issue) * rho_r1).0],
        );

        let (rho_u, rho_v, rho_w) = (
            Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng),
        );

        let c_total  = &k_prime + &(&generators.h[4] * &Scalar::from(spend_amount).0);
        let t_scale_t = &c_total  * &rho_r1.0;
        let t_total   = g1_msm(
            &[generators.h_affine[4], generators.h_affine[1],
              generators.h_affine[2], generators.h_affine[0]],
            &[rho_c.0, rho_u.0, (rho_r1 * Scalar::from(t_issue)).0, rho_v.0],
        );

        let t_scale_r = &k_prime * &rho_r1.0;
        let rho_m     = rho_c - Scalar::from(spend_amount) * rho_r1;
        let t_refund  = g1_msm(
            &[generators.h_affine[4], generators.h_affine[1],
              generators.h_affine[2], generators.h_affine[0]],
            &[rho_m.0, rho_u.0, (rho_r1 * Scalar::from(t_issue)).0, rho_v.0],
        );

        let t_scale_bp = &c_bp * &rho_r1.0;
        let t_bp = g1_msm(
            &[generators.h_affine[4], generators.h_affine[0]],
            &[rho_m.0, rho_w.0],
        );

        // BatchedEqualityProof
        let mut beq_ctx = Vec::new();
        beq_ctx.extend_from_slice(&h_ctx.to_bytes());
        beq_ctx.extend_from_slice(&spend_amount.to_le_bytes());
        beq_ctx.extend_from_slice(&k_cur.to_bytes());
        beq_ctx.extend_from_slice(&t_issue.to_le_bytes());
        beq_ctx.extend_from_slice(nonce);

        // BBS+ and bridge commitments passed explicitly into the BatchedEqualityProof
        // so they are bound in both the Sigma challenge and the Bulletproof transcript
        // (prevents transcript-splicing attacks per Section 9.2 of the ACT paper).
        let beq_commitments = [
            G1Affine::from(a_prime),
            G1Affine::from(a_bar),
            G1Affine::from(t_bbs),
            G1Affine::from(k_prime),
            G1Affine::from(c_total),
        ];

        let (batched_eq, c_bp_from_beq) = prove_batched_equality(
            &mut fast_rng, m, r_bp.0, generators.h[4], generators.h[0], &beq_ctx, &beq_commitments,
        )?;
        debug_assert_eq!(c_bp, c_bp_from_beq, "c_bp mismatch");
        let beq_bytes = batched_eq.to_bytes();

        let c = Self::challenge(
            h_ctx, pk_daily, spend_amount, &k_cur, t_issue, nonce,
            k_prime, c_total, c_bp, &beq_bytes,
            a_prime, a_bar, t_bbs,
            t_scale_t, t_total, t_scale_r, t_refund, t_scale_bp, t_bp,
        );

        let z_e      = rho_e  + c * token.e;
        let z_r1     = rho_r1 + c * r1;
        let z_s_tilde = rho_s + c * s_tilde;
        let z_c_tilde = rho_c + c * c_tilde;
        let z_u = rho_u + c * (k_star * r1);
        let z_v = rho_v + c * (r_star * r1);
        let z_w = rho_w + c * (r_bp * r1);

        Ok((
            SpendClient { k_cur, c_bal, t_issue, k_star, r_star, r_bp },
            SpendProof {
                a_prime, a_bar, t_bbs,
                t_scale_t, t_total, t_scale_r, t_refund, t_scale_bp, t_bp,
                z_e, z_r1, z_s_tilde, z_c_tilde, z_u, z_v, z_w,
                batched_eq, s: spend_amount, k_cur, t_issue, k_prime, c_bp,
            },
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn challenge(
        h_ctx: Scalar,
        pk_daily: &G2Projective,
        spend_amount: u32,
        k_cur: &Scalar,
        t_issue: u32,
        nonce: &[u8; 16],
        k_prime: G1Projective,
        c_total: G1Projective,
        c_bp: G1Projective,
        beq_bytes: &[u8],
        a_prime: G1Projective,
        a_bar: G1Projective,
        t_bbs: G1Projective,
        t_scale_t: G1Projective,
        t_total: G1Projective,
        t_scale_r: G1Projective,
        t_refund: G1Projective,
        t_scale_bp: G1Projective,
        t_bp: G1Projective,
    ) -> Scalar {
        let mut hasher = Sha256::new();
        let mut w = HasherWriter(&mut hasher);
        write_scalar(&mut w, h_ctx);
        write_g2(&mut w, *pk_daily);
        w.write_all(&spend_amount.to_le_bytes()).unwrap();
        w.write_all(&k_cur.to_bytes()).unwrap();
        w.write_all(&t_issue.to_le_bytes()).unwrap();
        w.write_all(nonce).unwrap();
        write_g1(&mut w, k_prime);
        write_g1(&mut w, c_total);
        write_g1(&mut w, c_bp);
        w.write_all(beq_bytes).unwrap();
        write_g1(&mut w, a_prime);
        write_g1(&mut w, a_bar);
        write_g1(&mut w, t_bbs);
        write_g1(&mut w, t_scale_t);
        write_g1(&mut w, t_total);
        write_g1(&mut w, t_scale_r);
        write_g1(&mut w, t_refund);
        write_g1(&mut w, t_scale_bp);
        write_g1(&mut w, t_bp);
        w.write_all(b"Spend").unwrap();
        drop(w);
        hash_to_scalar_from_hasher(hasher)
    }
}

// ============================================================================
// Server Verifier
// ============================================================================

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
    if proof.s == 0 {
        return Err(ActError::VerificationFailed("Spend amount must be positive".into()));
    }
    if proof.t_issue != current_epoch && proof.t_issue.saturating_add(1) != current_epoch {
        return Err(ActError::VerificationFailed("Epoch mismatch".into()));
    }
    if bool::from(proof.a_prime.is_identity()) || bool::from(proof.t_bbs.is_identity()) {
        return Err(ActError::VerificationFailed("Zero point in proof".into()));
    }

    let c_total  = &proof.k_prime + &(&generators.h[4] * &Scalar::from(proof.s).0);
    let beq_bytes = proof.batched_eq.to_bytes();

    let c = SpendProver::challenge(
        h_ctx, pk_daily, proof.s, &proof.k_cur, proof.t_issue, nonce,
        proof.k_prime, c_total, proof.c_bp, &beq_bytes,
        proof.a_prime, proof.a_bar, proof.t_bbs,
        proof.t_scale_t, proof.t_total, proof.t_scale_r, proof.t_refund,
        proof.t_scale_bp, proof.t_bp,
    );
    let c_fr = c.0;

    // Schwartz–Zippell RLC combined check
    {
        let c2 = &c_fr * &c_fr;
        let c3 = &c2   * &c_fr;
        let ti = BlsScalar::from(proof.t_issue as u64);
        let sf = BlsScalar::from(proof.s as u64);

        let sc_h0 = &(&(&c_fr + &c2) * &proof.z_v.0) + &(&(&c3 * &proof.z_w.0) + &proof.z_s_tilde.0);
        let sc_h1 = &(&(&c_fr + &c2) * &proof.z_u.0) + &(&proof.k_cur.0 * &proof.z_r1.0);
        let sc_h2 = &(&(&c_fr + &(&c2 + &BlsScalar::ONE)) * &ti) * &proof.z_r1.0;
        let sc_h4 = {
            let zc = proof.z_c_tilde.0;
            let zr = proof.z_r1.0;
            // (c+1+c2+c3)*z_c - (c2+c3)*s*z_r1
            let t1 = &(&c_fr + &(&BlsScalar::ONE + &(&c2 + &c3))) * &zc;
            let t2 = &(&c2 + &c3) * &(&sf * &zr);
            &t1 - &t2
        };
        let sc_g1      = proof.z_r1.0;
        let sc_aprime  = -proof.z_e.0;
        let sc_ctotal  = -(&c_fr * &proof.z_r1.0);
        let sc_kprime  = -(&c2   * &proof.z_r1.0);
        let sc_cbp     = -(&c3   * &proof.z_r1.0);
        let sc_abar    = -c_fr;
        let sc_ttotal    = -c_fr;
        let sc_tscale_t  =  c_fr;
        let sc_trefund   = -c2;
        let sc_tscale_r  =  c2;
        let sc_tbp       = -c3;
        let sc_tscale_bp =  c3;
        let sc_tbbs      = -BlsScalar::ONE;

        let dyn_pts = batch_normalize(&[
            proof.a_prime, c_total, proof.k_prime, proof.c_bp, proof.a_bar,
            proof.t_total, proof.t_scale_t, proof.t_refund, proof.t_scale_r,
            proof.t_bp, proof.t_scale_bp, proof.t_bbs,
        ]);

        let bases = [
            generators.h_affine[0], generators.h_affine[1],
            generators.h_affine[2], generators.h_affine[4],
            generators.g1_affine,
            dyn_pts[0], dyn_pts[1],  dyn_pts[2],  dyn_pts[3], dyn_pts[4],
            dyn_pts[5], dyn_pts[6],  dyn_pts[7],  dyn_pts[8],
            dyn_pts[9], dyn_pts[10], dyn_pts[11],
        ];
        let scalars = [
            sc_h0, sc_h1, sc_h2, sc_h4, sc_g1,
            sc_aprime, sc_ctotal, sc_kprime, sc_cbp, sc_abar,
            sc_ttotal, sc_tscale_t, sc_trefund, sc_tscale_r,
            sc_tbp, sc_tscale_bp, sc_tbbs,
        ];

        let combined = g1_msm(&bases, &scalars);
        if !bool::from(combined.is_identity()) {
            return Err(ActError::VerificationFailed("Combined bridge+Schnorr check failed".into()));
        }
    }

    // Build BatchedEqualityProof context and commitment list (used in rayon::join below).
    let mut beq_ctx = Vec::new();
    beq_ctx.extend_from_slice(&h_ctx.to_bytes());
    beq_ctx.extend_from_slice(&proof.s.to_le_bytes());
    beq_ctx.extend_from_slice(&proof.k_cur.to_bytes());
    beq_ctx.extend_from_slice(&proof.t_issue.to_le_bytes());
    beq_ctx.extend_from_slice(nonce);
    let beq_commitments = [
        G1Affine::from(proof.a_prime),
        G1Affine::from(proof.a_bar),
        G1Affine::from(proof.t_bbs),
        G1Affine::from(proof.k_prime),
        G1Affine::from(c_total),
    ];

    // BatchedEqualityProof + Pairing check run concurrently (mathematically
    // isolated: no shared mutable state).  rayon::join offloads one branch to
    // the thread pool, cutting combined latency from ~7ms to ~4ms.
    let (beq_result, pairing_ok) = rayon::join(
        || {
            verify_batched_equality(
                &proof.batched_eq, proof.c_bp,
                generators.h[4], generators.h[0],
                &beq_ctx, &beq_commitments,
            )
        },
        || {
            let result = Bls12::multi_miller_loop(&[
                (&G1Affine::from(proof.a_prime), &keys.pk_daily_prepared),
                (&G1Affine::from(-proof.a_bar),  &generators.g2_prepared),
            ])
            .final_exponentiation();
            result == Gt::identity()
        },
    );
    beq_result?;
    if !pairing_ok {
        return Err(ActError::VerificationFailed("Pairing check failed".into()));
    }

    // Issue Refund Token
    let e_refund       = Scalar::rand(rng);
    let s_prime_refund = Scalar::rand(rng);
    let k_prime_aff    = G1Affine::from(proof.k_prime);
    let msg_part = g1_msm(
        &[generators.g1_affine, k_prime_aff, generators.h_affine[0]],
        &[BlsScalar::ONE, BlsScalar::ONE, s_prime_refund.0],
    );
    let denom = e_refund + keys.sk_daily;
    if denom.is_zero() {
        return Err(ActError::ProtocolError("Division by zero in issuance".into()));
    }
    let a_refund = &msg_part * &denom.inverse().0;

    Ok(SpendResponse { a_refund, e_refund, s_prime_refund })
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
    use rand::thread_rng;

    fn daily_sig(
        rng: &mut impl RngCore,
        k_cur: Scalar,
        c_bal: u32,
        t_issue: u32,
        generators: &Generators,
        keys: &ServerKeys,
    ) -> BbsSignature {
        let r_daily = Scalar::rand(rng);
        let k_daily_commit = &(&(&generators.h[4] * &Scalar::from(c_bal).0)
            + &(&generators.h[1] * &k_cur.0))
            + &(&(&generators.h[2] * &Scalar::from(t_issue).0)
            + &(&generators.h[0] * &r_daily.0));
        let e_d = Scalar::rand(rng);
        let s_p = Scalar::rand(rng);
        let msg_part = &(&generators.g1 + &k_daily_commit) + &(&generators.h[0] * &s_p.0);
        let denom = e_d + keys.sk_daily;
        let a_d = &msg_part * &denom.inverse().0;
        BbsSignature { a: a_d, e: e_d, s: r_daily + s_p }
    }

    #[test]
    fn spend_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let k_cur = Scalar::rand_nonzero(&mut rng);
        let c_bal = 100u32;
        let t_issue = 42u32;
        let token = daily_sig(&mut rng, k_cur, c_bal, t_issue, &generators, &keys);

        let (client, proof) = SpendProver::prove(
            &mut rng, &token, k_cur, c_bal, t_issue, 30, &[0xAAu8; 16],
            &generators, &keys.pk_daily, h_ctx,
        ).unwrap();
        let resp = verify_spend(
            &proof, t_issue, &[0xAAu8; 16], &generators, &keys.pk_daily, &keys, h_ctx, &mut rng,
        ).unwrap();
        let refund = BbsSignature {
            a: resp.a_refund,
            e: resp.e_refund,
            s: client.r_star + resp.s_prime_refund,
        };
        assert!(!bool::from(refund.a.is_identity()));
        assert_eq!(client.c_bal - 30, 70);
    }

    #[test]
    fn overspend_rejected() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let k_cur = Scalar::rand_nonzero(&mut rng);
        let token = daily_sig(&mut rng, k_cur, 50, 42, &generators, &keys);
        assert!(SpendProver::prove(
            &mut rng, &token, k_cur, 50, 42, 100, &[0xAAu8; 16],
            &generators, &keys.pk_daily, h_ctx,
        ).is_err());
    }

    #[test]
    fn tampered_nonce_fails() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let k_cur = Scalar::rand_nonzero(&mut rng);
        let token = daily_sig(&mut rng, k_cur, 100, 42, &generators, &keys);
        let (_client, proof) = SpendProver::prove(
            &mut rng, &token, k_cur, 100, 42, 30, &[0xAAu8; 16],
            &generators, &keys.pk_daily, h_ctx,
        ).unwrap();
        assert!(verify_spend(
            &proof, 42, &[0xBBu8; 16], &generators, &keys.pk_daily, &keys, h_ctx, &mut rng,
        ).is_err());
    }
}
