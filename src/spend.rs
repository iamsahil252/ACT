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

        // Fixed-base part: use precomputed tables for the 5 protocol generators.
        let mut fixed_sum = generators.h_tables[0].mul(&sc_h0);
        fixed_sum = &fixed_sum + &generators.h_tables[1].mul(&sc_h1);
        fixed_sum = &fixed_sum + &generators.h_tables[2].mul(&sc_h2);
        fixed_sum = &fixed_sum + &generators.h_tables[4].mul(&sc_h4);
        fixed_sum = &fixed_sum + &generators.g1_table.mul(&sc_g1);

        // Variable-base part: 12 dynamic proof points via Pippenger MSM.
        let var_scalars = [
            sc_aprime, sc_ctotal, sc_kprime, sc_cbp, sc_abar,
            sc_ttotal, sc_tscale_t, sc_trefund, sc_tscale_r,
            sc_tbp, sc_tscale_bp, sc_tbbs,
        ];
        let combined = &fixed_sum + &g1_msm(&dyn_pts, &var_scalars);
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
// Batch Server Verifier
// ============================================================================

/// Batch-verify a slice of [`SpendProof`]s sharing the same epoch and keys.
///
/// `nonces` must be the same length as `proofs`; each entry is the anti-replay
/// nonce for the corresponding proof.
///
/// # Batching strategy
///
/// * **Schnorr MSM** – per-proof Schwartz–Zippel equations combined into one
///   Pippenger MSM via RLC weights `ρ_i` derived from the per-proof challenges.
///
/// * **Pairing check** – G1 points aggregated via the same RLC weights;
///   a single 2-pair `multi_miller_loop` + one `final_exponentiation` replaces
///   N individual pairing checks.
///
/// * **BEQ range proofs** – verified concurrently via `rayon`.
///
/// Returns `Ok(Vec<SpendResponse>)` on success.  Returns `Err` if any proof is
/// invalid.
///
/// Falls back to [`verify_spend`] directly for 0 or 1 proofs.
pub fn verify_spend_batch(
    proofs: &[SpendProof],
    current_epoch: u32,
    nonces: &[[u8; 16]],
    generators: &Generators,
    pk_daily: &G2Projective,
    keys: &ServerKeys,
    h_ctx: Scalar,
    rng: &mut impl RngCore,
) -> Result<Vec<SpendResponse>> {
    use rayon::prelude::*;

    if proofs.len() != nonces.len() {
        return Err(ActError::ProtocolError(
            "verify_spend_batch: proofs and nonces must have the same length".into(),
        ));
    }
    if proofs.is_empty() {
        return Ok(Vec::new());
    }
    if proofs.len() == 1 {
        return verify_spend(&proofs[0], current_epoch, &nonces[0], generators, pk_daily, keys, h_ctx, rng)
            .map(|r| vec![r]);
    }

    let n = proofs.len();

    // ── Step 1: Per-proof basic validation + Fiat–Shamir challenges ──────────
    struct PerProof {
        c_fr:    BlsScalar,
        c_total: G1Projective,
    }
    let mut per_proof = Vec::with_capacity(n);
    for (proof, nonce) in proofs.iter().zip(nonces.iter()) {
        if proof.s == 0 {
            return Err(ActError::VerificationFailed("Spend amount must be positive".into()));
        }
        if proof.t_issue != current_epoch && proof.t_issue.saturating_add(1) != current_epoch {
            return Err(ActError::VerificationFailed("Epoch mismatch".into()));
        }
        if bool::from(proof.a_prime.is_identity()) || bool::from(proof.t_bbs.is_identity()) {
            return Err(ActError::VerificationFailed("Zero point in proof".into()));
        }
        let c_total   = &proof.k_prime + &(&generators.h[4] * &Scalar::from(proof.s).0);
        let beq_bytes = proof.batched_eq.to_bytes();
        let c = SpendProver::challenge(
            h_ctx, pk_daily, proof.s, &proof.k_cur, proof.t_issue, nonce,
            proof.k_prime, c_total, proof.c_bp, &beq_bytes,
            proof.a_prime, proof.a_bar, proof.t_bbs,
            proof.t_scale_t, proof.t_total, proof.t_scale_r, proof.t_refund,
            proof.t_scale_bp, proof.t_bp,
        );
        per_proof.push(PerProof { c_fr: c.0, c_total });
    }

    // ── Step 2: Derive RLC weights ρ_i ──────────────────────────────────────
    let rho_seed: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(b"ACT:BatchVerify:Spend:RLC");
        for pp in &per_proof {
            h.update(pp.c_fr.to_bytes_le());
        }
        h.finalize().into()
    };
    let mut rho_rng = rand_chacha::ChaCha20Rng::from_seed(rho_seed);
    let rhos: Vec<BlsScalar> = (0..n).map(|_| BlsScalar::random(&mut rho_rng)).collect();

    // ── Step 3: Batched Schnorr-bridge MSM ──────────────────────────────────
    // Static bases: h0, h1, h2, h4, g1 (h3 does not appear in spend).
    let mut acc_h0 = BlsScalar::ZERO;
    let mut acc_h1 = BlsScalar::ZERO;
    let mut acc_h2 = BlsScalar::ZERO;
    let mut acc_h4 = BlsScalar::ZERO;
    let mut acc_g1 = BlsScalar::ZERO;

    // Dynamic bases (12 per proof).
    let mut dyn_bases:   Vec<G1Affine>  = Vec::with_capacity(12 * n);
    let mut dyn_scalars: Vec<BlsScalar> = Vec::with_capacity(12 * n);

    for (i, (proof, pp)) in proofs.iter().zip(per_proof.iter()).enumerate() {
        let rho  = rhos[i];
        let c_fr = pp.c_fr;
        let c2   = &c_fr * &c_fr;
        let c3   = &c2   * &c_fr;
        let ti   = BlsScalar::from(proof.t_issue as u64);
        let sf   = BlsScalar::from(proof.s as u64);

        let sc_h0 = &(&(&c_fr + &c2) * &proof.z_v.0)
            + &(&(&c3 * &proof.z_w.0) + &proof.z_s_tilde.0);
        let sc_h1 = &(&(&c_fr + &c2) * &proof.z_u.0)
            + &(&proof.k_cur.0 * &proof.z_r1.0);
        let sc_h2 = &(&(&c_fr + &(&c2 + &BlsScalar::ONE)) * &ti) * &proof.z_r1.0;
        let sc_h4 = {
            let t1 = &(&c_fr + &(&BlsScalar::ONE + &(&c2 + &c3))) * &proof.z_c_tilde.0;
            let t2 = &(&c2 + &c3) * &(&sf * &proof.z_r1.0);
            &t1 - &t2
        };
        let sc_g1       = proof.z_r1.0;
        let sc_aprime   = -proof.z_e.0;
        let sc_ctotal   = -(&c_fr * &proof.z_r1.0);
        let sc_kprime   = -(&c2   * &proof.z_r1.0);
        let sc_cbp      = -(&c3   * &proof.z_r1.0);
        let sc_abar     = -c_fr;
        let sc_ttotal   = -c_fr;
        let sc_tscale_t =  c_fr;
        let sc_trefund  = -c2;
        let sc_tscale_r =  c2;
        let sc_tbp      = -c3;
        let sc_tscale_bp = c3;
        let sc_tbbs     = -BlsScalar::ONE;

        acc_h0 = &acc_h0 + &(&rho * &sc_h0);
        acc_h1 = &acc_h1 + &(&rho * &sc_h1);
        acc_h2 = &acc_h2 + &(&rho * &sc_h2);
        acc_h4 = &acc_h4 + &(&rho * &sc_h4);
        acc_g1 = &acc_g1 + &(&rho * &sc_g1);

        let dyn_pts = batch_normalize(&[
            proof.a_prime, pp.c_total, proof.k_prime, proof.c_bp, proof.a_bar,
            proof.t_total, proof.t_scale_t, proof.t_refund, proof.t_scale_r,
            proof.t_bp, proof.t_scale_bp, proof.t_bbs,
        ]);
        for (sc, pt) in [
            (sc_aprime,    dyn_pts[0]),
            (sc_ctotal,    dyn_pts[1]),
            (sc_kprime,    dyn_pts[2]),
            (sc_cbp,       dyn_pts[3]),
            (sc_abar,      dyn_pts[4]),
            (sc_ttotal,    dyn_pts[5]),
            (sc_tscale_t,  dyn_pts[6]),
            (sc_trefund,   dyn_pts[7]),
            (sc_tscale_r,  dyn_pts[8]),
            (sc_tbp,       dyn_pts[9]),
            (sc_tscale_bp, dyn_pts[10]),
            (sc_tbbs,      dyn_pts[11]),
        ] {
            dyn_bases.push(pt);
            dyn_scalars.push(&rho * &sc);
        }
    }

    // Fixed-base part: use precomputed tables for the 5 accumulated scalars.
    let mut fixed_sum = generators.h_tables[0].mul(&acc_h0);
    fixed_sum = &fixed_sum + &generators.h_tables[1].mul(&acc_h1);
    fixed_sum = &fixed_sum + &generators.h_tables[2].mul(&acc_h2);
    fixed_sum = &fixed_sum + &generators.h_tables[4].mul(&acc_h4);
    fixed_sum = &fixed_sum + &generators.g1_table.mul(&acc_g1);

    // Variable-base part: N×12 dynamic points via Pippenger MSM.
    let combined = &fixed_sum + &g1_msm(&dyn_bases, &dyn_scalars);
    if !bool::from(combined.is_identity()) {
        return Err(ActError::VerificationFailed("Batched Schnorr check failed".into()));
    }

    // ── Step 4: Batched pairing check ────────────────────────────────────────
    let a_prime_aff: Vec<G1Affine>    = proofs.iter().map(|p| G1Affine::from(p.a_prime)).collect();
    let a_bar_neg_aff: Vec<G1Affine>  = proofs.iter().map(|p| G1Affine::from(-p.a_bar)).collect();
    let a_prime_agg = g1_msm(&a_prime_aff,   &rhos);
    let a_bar_agg   = g1_msm(&a_bar_neg_aff, &rhos);
    let pairing_result = Bls12::multi_miller_loop(&[
        (&G1Affine::from(a_prime_agg), &keys.pk_daily_prepared),
        (&G1Affine::from(a_bar_agg),   &generators.g2_prepared),
    ])
    .final_exponentiation();
    if pairing_result != Gt::identity() {
        return Err(ActError::VerificationFailed("Batched pairing check failed".into()));
    }

    // ── Step 5: Verify all BEQ proofs concurrently ───────────────────────────
    let beq_check_results: Vec<Result<()>> = proofs
        .par_iter()
        .zip(nonces.par_iter())
        .zip(per_proof.par_iter())
        .map(|((proof, nonce), pp)| {
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
                G1Affine::from(pp.c_total),
            ];
            verify_batched_equality(
                &proof.batched_eq, proof.c_bp,
                generators.h[4], generators.h[0],
                &beq_ctx, &beq_commitments,
            )
        })
        .collect();
    for r in beq_check_results {
        r?;
    }

    // ── Step 6: Issue refund responses individually ───────────────────────────
    let mut responses = Vec::with_capacity(n);
    for proof in proofs {
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
        responses.push(SpendResponse { a_refund, e_refund, s_prime_refund });
    }

    Ok(responses)
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

    #[test]
    fn batch_spend_empty() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let responses = verify_spend_batch(
            &[], 42, &[], &generators, &keys.pk_daily, &keys, h_ctx, &mut rng,
        ).unwrap();
        assert!(responses.is_empty());
    }

    #[test]
    fn batch_spend_single() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let k_cur = Scalar::rand_nonzero(&mut rng);
        let t_issue = 42u32;
        let token = daily_sig(&mut rng, k_cur, 100, t_issue, &generators, &keys);
        let nonce = [0xAAu8; 16];
        let (_client, proof) = SpendProver::prove(
            &mut rng, &token, k_cur, 100, t_issue, 30, &nonce,
            &generators, &keys.pk_daily, h_ctx,
        ).unwrap();
        let responses = verify_spend_batch(
            &[proof], t_issue, &[nonce], &generators, &keys.pk_daily, &keys, h_ctx, &mut rng,
        ).unwrap();
        assert_eq!(responses.len(), 1);
        assert!(!bool::from(responses[0].a_refund.is_identity()));
    }

    #[test]
    fn batch_spend_multiple() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let t_issue = 42u32;

        const BATCH: usize = 4;
        let mut proofs = Vec::with_capacity(BATCH);
        let mut nonces: Vec<[u8; 16]> = Vec::with_capacity(BATCH);
        for i in 0..BATCH {
            let k_cur = Scalar::rand_nonzero(&mut rng);
            let token = daily_sig(&mut rng, k_cur, 100, t_issue, &generators, &keys);
            let mut nonce = [0u8; 16];
            nonce[0] = i as u8;
            let (_client, proof) = SpendProver::prove(
                &mut rng, &token, k_cur, 100, t_issue, 20, &nonce,
                &generators, &keys.pk_daily, h_ctx,
            ).unwrap();
            proofs.push(proof);
            nonces.push(nonce);
        }

        let responses = verify_spend_batch(
            &proofs, t_issue, &nonces, &generators, &keys.pk_daily, &keys, h_ctx, &mut rng,
        ).unwrap();
        assert_eq!(responses.len(), BATCH);
        for r in &responses {
            assert!(!bool::from(r.a_refund.is_identity()));
        }
    }

    #[test]
    fn batch_spend_rejects_bad_proof() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let keys2 = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let t_issue = 42u32;

        let mut proofs = Vec::new();
        let mut nonces: Vec<[u8; 16]> = Vec::new();
        for i in 0..3usize {
            let k_cur = Scalar::rand_nonzero(&mut rng);
            let token = daily_sig(&mut rng, k_cur, 100, t_issue, &generators, &keys);
            let mut nonce = [0u8; 16];
            nonce[0] = i as u8;
            let (_client, proof) = SpendProver::prove(
                &mut rng, &token, k_cur, 100, t_issue, 20, &nonce,
                &generators, &keys.pk_daily, h_ctx,
            ).unwrap();
            proofs.push(proof);
            nonces.push(nonce);
        }
        // Add a proof from different keys → batch must fail.
        {
            let k_cur = Scalar::rand_nonzero(&mut rng);
            let token = daily_sig(&mut rng, k_cur, 100, t_issue, &generators, &keys2);
            let nonce = [0xFFu8; 16];
            let (_client, bad_proof) = SpendProver::prove(
                &mut rng, &token, k_cur, 100, t_issue, 20, &nonce,
                &generators, &keys2.pk_daily, h_ctx,
            ).unwrap();
            proofs.push(bad_proof);
            nonces.push(nonce);
        }
        assert!(verify_spend_batch(
            &proofs, t_issue, &nonces, &generators, &keys.pk_daily, &keys, h_ctx, &mut rng,
        ).is_err());
    }
}
