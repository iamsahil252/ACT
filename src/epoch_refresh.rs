//! Phase 2: Automated Epoch Refresh.

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

use crate::batched_eq::{prove_batched_equality, verify_batched_equality, BatchedEqualityProof};
use crate::bbs_proof::BbsSignature;
use crate::error::{ActError, Result};
use crate::hash::{hash_to_g1, hash_to_scalar_from_hasher, write_g1, write_g2, write_scalar, HasherWriter};
use crate::msm::{batch_normalize, g1_msm};
use crate::setup::{Generators, ServerKeys};
use crate::types::Scalar;
#[cfg(feature = "std")]
use rayon;

// ============================================================================
// Proof / Response structures
// ============================================================================

#[derive(Clone, Debug)]
pub struct RefreshProof {
    pub a_prime: G1Projective,
    pub a_bar: G1Projective,
    pub t_bbs: G1Projective,
    pub t_scale_n: G1Projective,
    pub t_n: G1Projective,
    pub t_scale_d: G1Projective,
    pub t_d: G1Projective,
    pub t_scale_b: G1Projective,
    pub t_b: G1Projective,
    pub z_e: Scalar,
    pub z_r1: Scalar,
    pub z_s_tilde: Scalar,
    pub z_k_tilde: Scalar,
    pub z_c_tilde: Scalar,
    pub z_e_tilde: Scalar,
    pub z_u: Scalar,
    pub z_v: Scalar,
    pub z_w: Scalar,
    pub batched_eq: BatchedEqualityProof,
    pub n_t: G1Projective,
    pub k_daily: G1Projective,
    pub c_delta: G1Projective,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RefreshResponse {
    #[serde(with = "crate::types::g1_serde")]
    pub a_daily: G1Projective,
    pub e_daily: Scalar,
    pub s_prime_daily: Scalar,
}

// ============================================================================
// Client
// ============================================================================

pub struct RefreshClient {
    pub k_sub: Scalar,
    pub c_max: u32,
    pub e_max: u32,
    pub t: u32,
    pub k_daily: Scalar,
    pub r_daily: Scalar,
    pub r_delta: Scalar,
}

impl RefreshClient {
    pub fn finalize(self, response: RefreshResponse) -> (BbsSignature, Scalar) {
        let s_daily = self.r_daily + response.s_prime_daily;
        (BbsSignature { a: response.a_daily, e: response.e_daily, s: s_daily }, self.k_daily)
    }
}

// ============================================================================
// Prover
// ============================================================================

pub struct RefreshProver;

impl RefreshProver {
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
        if e_max < t {
            return Err(ActError::ProtocolError("Master token expired".into()));
        }
        let delta = e_max - t;

        // Seed a ChaCha20Rng from 32 bytes of OS/caller entropy.
        // All blinder scalars are generated from this fast SIMD PRNG.
        let mut seed = [0u8; 32];
        rng.fill_bytes(&mut seed);
        let mut fast_rng = ChaCha20Rng::from_seed(seed);

        // Epoch nullifier
        let h_t = hash_to_g1(b"ACT:Epoch:", &t.to_le_bytes());
        let n_t  = &h_t * &k_sub.0;

        // Daily commitment
        let k_daily   = Scalar::rand_nonzero(&mut fast_rng);
        let r_daily   = Scalar::rand(&mut fast_rng);
        let k_daily_commit = &(&(&generators.h[4] * &Scalar::from(c_max).0)
            + &(&generators.h[1] * &k_daily.0))
            + &(&(&generators.h[2] * &Scalar::from(t).0)
            + &(&generators.h[0] * &r_daily.0));

        // Expiry commitment
        let r_delta = Scalar::rand(&mut fast_rng);
        let c_delta = &(&generators.h[3] * &Scalar::from(delta).0) + &(&generators.h[0] * &r_delta.0);

        // BBS+ randomization
        let r1      = Scalar::rand_nonzero(&mut fast_rng);
        let a_prime = &master.a * &r1.0;

        let msg_part = g1_msm(
            &[generators.g1_affine, generators.h_affine[0], generators.h_affine[1],
              generators.h_affine[2], generators.h_affine[3]],
            &[BlsScalar::ONE, master.s.0, k_sub.0,
              BlsScalar::from(c_max as u64), BlsScalar::from(e_max as u64)],
        );
        let a_bar = &(&a_prime * &(-master.e.0)) + &(&msg_part * &r1.0);

        let s_tilde = master.s * r1;
        let k_tilde = k_sub * r1;
        let c_tilde = Scalar::from(c_max) * r1;
        let e_tilde = Scalar::from(e_max) * r1;

        // BBS+ blinders
        let (rho_e, rho_r1, rho_s, rho_k, rho_c, rho_e_msg) = (
            Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng),
            Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng),
        );

        let a_prime_aff = G1Affine::from(a_prime);
        let t_bbs = g1_msm(
            &[a_prime_aff, generators.g1_affine, generators.h_affine[0],
              generators.h_affine[1], generators.h_affine[2], generators.h_affine[3]],
            &[(-rho_e).0, rho_r1.0, rho_s.0, rho_k.0, rho_c.0, rho_e_msg.0],
        );

        // External blinders
        let (rho_u, rho_v, rho_w) = (
            Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng), Scalar::rand(&mut fast_rng),
        );

        // Bridging commitments
        let t_scale_n = &n_t * &rho_r1.0;
        let t_n       = &h_t * &rho_k.0;
        let t_scale_d = &k_daily_commit * &rho_r1.0;
        let t_d = g1_msm(
            &[generators.h_affine[4], generators.h_affine[1],
              generators.h_affine[2], generators.h_affine[0]],
            &[rho_c.0, rho_u.0, (rho_r1 * Scalar::from(t)).0, rho_v.0],
        );
        let c_bridge  = &c_delta + &(&generators.h[3] * &Scalar::from(t).0);
        let t_scale_b = &c_bridge * &rho_r1.0;
        let t_b = g1_msm(
            &[generators.h_affine[3], generators.h_affine[0]],
            &[rho_e_msg.0, rho_w.0],
        );

        // BatchedEqualityProof for delta
        let mut beq_ctx = Vec::new();
        beq_ctx.extend_from_slice(&h_ctx.to_bytes());
        beq_ctx.extend_from_slice(&t.to_le_bytes());

        // BBS+ and bridge commitments passed explicitly to prevent splicing attacks.
        let beq_commitments = [
            G1Affine::from(a_prime),
            G1Affine::from(a_bar),
            G1Affine::from(t_bbs),
            G1Affine::from(n_t),
            G1Affine::from(k_daily_commit),
        ];

        let (batched_eq, c_delta_from_beq) = prove_batched_equality(
            &mut fast_rng, delta, r_delta.0, generators.h[3], generators.h[0], &beq_ctx, &beq_commitments,
        )?;
        debug_assert_eq!(c_delta, c_delta_from_beq, "c_delta mismatch");
        let beq_bytes = batched_eq.to_bytes();

        // Fiat–Shamir challenge
        let c = Self::challenge(
            h_ctx, pk_master, t, n_t, k_daily_commit, c_delta,
            &beq_bytes, a_prime, a_bar, t_bbs,
            t_scale_n, t_n, t_scale_d, t_d, t_scale_b, t_b,
        );

        // Responses
        let z_e      = rho_e      + c * master.e;
        let z_r1     = rho_r1     + c * r1;
        let z_s_tilde = rho_s     + c * s_tilde;
        let z_k_tilde = rho_k     + c * k_tilde;
        let z_c_tilde = rho_c     + c * c_tilde;
        let z_e_tilde = rho_e_msg + c * e_tilde;
        let z_u = rho_u + c * (k_daily * r1);
        let z_v = rho_v + c * (r_daily * r1);
        let z_w = rho_w + c * (r_delta * r1);

        Ok((
            RefreshClient { k_sub, c_max, e_max, t, k_daily, r_daily, r_delta },
            RefreshProof {
                a_prime, a_bar, t_bbs,
                t_scale_n, t_n, t_scale_d, t_d, t_scale_b, t_b,
                z_e, z_r1, z_s_tilde, z_k_tilde, z_c_tilde, z_e_tilde,
                z_u, z_v, z_w, batched_eq,
                n_t, k_daily: k_daily_commit, c_delta,
            },
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn challenge(
        h_ctx: Scalar,
        pk_master: &G2Projective,
        t: u32,
        n_t: G1Projective,
        k_daily: G1Projective,
        c_delta: G1Projective,
        beq_bytes: &[u8],
        a_prime: G1Projective,
        a_bar: G1Projective,
        t_bbs: G1Projective,
        t_scale_n: G1Projective,
        t_n: G1Projective,
        t_scale_d: G1Projective,
        t_d: G1Projective,
        t_scale_b: G1Projective,
        t_b: G1Projective,
    ) -> Scalar {
        let mut hasher = Sha256::new();
        let mut w = HasherWriter(&mut hasher);
        write_scalar(&mut w, h_ctx);
        write_g2(&mut w, *pk_master);
        w.write_all(&t.to_le_bytes()).unwrap();
        write_g1(&mut w, n_t);
        write_g1(&mut w, k_daily);
        write_g1(&mut w, c_delta);
        w.write_all(beq_bytes).unwrap();
        write_g1(&mut w, a_prime);
        write_g1(&mut w, a_bar);
        write_g1(&mut w, t_bbs);
        write_g1(&mut w, t_scale_n);
        write_g1(&mut w, t_n);
        write_g1(&mut w, t_scale_d);
        write_g1(&mut w, t_d);
        write_g1(&mut w, t_scale_b);
        write_g1(&mut w, t_b);
        w.write_all(b"Refresh").unwrap();
        drop(w);
        hash_to_scalar_from_hasher(hasher)
    }
}

// ============================================================================
// Server Verifier
// ============================================================================

pub fn verify_refresh(
    proof: &RefreshProof,
    current_epoch: u32,
    generators: &Generators,
    pk_master: &G2Projective,
    keys: &ServerKeys,
    h_ctx: Scalar,
    rng: &mut impl RngCore,
) -> Result<RefreshResponse> {
    // Basic bounds
    if bool::from(proof.n_t.is_identity()) {
        return Err(ActError::VerificationFailed("N_T is the identity".into()));
    }
    if bool::from(proof.a_prime.is_identity()) || bool::from(proof.t_bbs.is_identity()) {
        return Err(ActError::VerificationFailed("Zero point in proof".into()));
    }

    let c_bridge = &proof.c_delta + &(&generators.h[3] * &Scalar::from(current_epoch).0);
    let beq_bytes = proof.batched_eq.to_bytes();

    let c = RefreshProver::challenge(
        h_ctx, pk_master, current_epoch,
        proof.n_t, proof.k_daily, proof.c_delta,
        &beq_bytes,
        proof.a_prime, proof.a_bar, proof.t_bbs,
        proof.t_scale_n, proof.t_n, proof.t_scale_d, proof.t_d,
        proof.t_scale_b, proof.t_b,
    );
    let c_fr = c.0;

    let h_t = hash_to_g1(b"ACT:Epoch:", &current_epoch.to_le_bytes());

    // Schwartz–Zippell RLC combined MSM check (soundness ≤ 4/|Fr|).
    {
        let c2 = &c_fr * &c_fr;
        let c3 = &c2  * &c_fr;
        let ep = BlsScalar::from(current_epoch as u64);

        let sc_ht       = &c_fr  * &proof.z_k_tilde.0;
        let sc_nt       = -(&c_fr * &proof.z_r1.0);
        let sc_tscale_n = c_fr;
        let sc_tn       = -c_fr;
        let sc_h0       = &(&c2 * &proof.z_v.0) + &(&(&c3 * &proof.z_w.0) + &proof.z_s_tilde.0);
        let sc_h1       = &(&c2 * &proof.z_u.0)   + &proof.z_k_tilde.0;
        let sc_h2       = &(&c2 * &(&proof.z_r1.0 * &ep)) + &proof.z_c_tilde.0;
        let sc_h3       = &(&c3 + &BlsScalar::ONE) * &proof.z_e_tilde.0;
        let sc_h4       = &c2 * &proof.z_c_tilde.0;
        let sc_g1       = proof.z_r1.0;
        let sc_aprime   = -proof.z_e.0;
        let sc_kdaily   = -(&c2 * &proof.z_r1.0);
        let sc_cbridge  = -(&c3 * &proof.z_r1.0);
        let sc_abar     = -c_fr;
        let sc_td       = -c2;
        let sc_tscale_d = c2;
        let sc_tb       = -c3;
        let sc_tscale_b = c3;
        let sc_tbbs     = -BlsScalar::ONE;

        let dyn_pts = batch_normalize(&[
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

        let bases = [
            dyn_pts[0],  dyn_pts[1],  dyn_pts[2],  dyn_pts[3],
            generators.h_affine[0], generators.h_affine[1],
            generators.h_affine[2], generators.h_affine[3],
            generators.h_affine[4], generators.g1_affine,
            dyn_pts[4],  dyn_pts[5],  dyn_pts[6],  dyn_pts[7],
            dyn_pts[8],  dyn_pts[9],  dyn_pts[10], dyn_pts[11], dyn_pts[12],
        ];
        let scalars = [
            sc_ht, sc_nt, sc_tscale_n, sc_tn,
            sc_h0, sc_h1, sc_h2, sc_h3, sc_h4,
            sc_g1, sc_aprime, sc_kdaily, sc_cbridge, sc_abar,
            sc_td, sc_tscale_d, sc_tb, sc_tscale_b, sc_tbbs,
        ];

        let combined = g1_msm(&bases, &scalars);
        if !bool::from(combined.is_identity()) {
            return Err(ActError::VerificationFailed("Combined bridge+Schnorr check failed".into()));
        }
    }

    // BatchedEqualityProof + Pairing check run concurrently (mathematically
    // isolated: no shared mutable state).  rayon::join offloads one branch to
    // the thread pool, cutting combined latency from ~7ms to ~4ms.
    let mut beq_ctx = Vec::new();
    beq_ctx.extend_from_slice(&h_ctx.to_bytes());
    beq_ctx.extend_from_slice(&current_epoch.to_le_bytes());
    let beq_commitments = [
        G1Affine::from(proof.a_prime),
        G1Affine::from(proof.a_bar),
        G1Affine::from(proof.t_bbs),
        G1Affine::from(proof.n_t),
        G1Affine::from(proof.k_daily),
    ];
    let (beq_result, pairing_ok) = rayon::join(
        || {
            verify_batched_equality(
                &proof.batched_eq, proof.c_delta,
                generators.h[3], generators.h[0],
                &beq_ctx, &beq_commitments,
            )
        },
        || {
            let result = Bls12::multi_miller_loop(&[
                (&G1Affine::from(proof.a_prime), &keys.pk_master_prepared),
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

    // Issue Daily Token
    let e_daily       = Scalar::rand(rng);
    let s_prime_daily = Scalar::rand(rng);
    let k_daily_aff   = G1Affine::from(proof.k_daily);
    let msg_part = g1_msm(
        &[generators.g1_affine, k_daily_aff, generators.h_affine[0]],
        &[BlsScalar::ONE, BlsScalar::ONE, s_prime_daily.0],
    );
    let denom = e_daily + keys.sk_daily;
    if denom.is_zero() {
        return Err(ActError::ProtocolError("Division by zero in issuance".into()));
    }
    let a_daily = &msg_part * &denom.inverse().0;

    Ok(RefreshResponse { a_daily, e_daily, s_prime_daily })
}

// ============================================================================
// Batch Server Verifier
// ============================================================================

/// Batch-verify a slice of [`RefreshProof`]s sharing the same epoch and keys.
///
/// # Batching strategy
///
/// * **Schnorr MSM** – all per-proof Schwartz–Zippel equations are combined
///   into a single Pippenger MSM via a random linear combination (RLC) with
///   weights `ρ_i` derived by hashing the per-proof Fiat–Shamir challenges.
///   Soundness error is negligible (one `≤ N/|Fr|` per batch).
///
/// * **Pairing check** – G1 points are aggregated as `∑ ρ_i·A'_i` and
///   `∑ ρ_i·Ā_i`, then checked with a single 2-pair `multi_miller_loop` +
///   one `final_exponentiation` (saves N−1 expensive final exponentiations).
///
/// * **BEQ range proofs** – each [`BatchedEqualityProof`] is independent;
///   they are verified concurrently via `rayon`.
///
/// Returns `Ok(Vec<RefreshResponse>)` where each response corresponds to the
/// proof at the same index.  Returns `Err` if **any** proof is invalid,
/// without revealing which one.
///
/// Falls back to calling [`verify_refresh`] directly for 0 or 1 proofs.
pub fn verify_refresh_batch(
    proofs: &[RefreshProof],
    current_epoch: u32,
    generators: &Generators,
    pk_master: &G2Projective,
    keys: &ServerKeys,
    h_ctx: Scalar,
    rng: &mut impl RngCore,
) -> Result<Vec<RefreshResponse>> {
    use rayon::prelude::*;

    if proofs.is_empty() {
        return Ok(Vec::new());
    }
    if proofs.len() == 1 {
        return verify_refresh(&proofs[0], current_epoch, generators, pk_master, keys, h_ctx, rng)
            .map(|r| vec![r]);
    }

    let n = proofs.len();

    // ── Step 1: Per-proof basic validation + Fiat–Shamir challenge ──────────
    // h_t is the same for all proofs (same current_epoch).
    let h_t = hash_to_g1(b"ACT:Epoch:", &current_epoch.to_le_bytes());
    let ep  = BlsScalar::from(current_epoch as u64);

    struct PerProof {
        c_fr:     BlsScalar,
        c_bridge: G1Projective,
    }
    let mut per_proof = Vec::with_capacity(n);
    for proof in proofs {
        if bool::from(proof.n_t.is_identity()) {
            return Err(ActError::VerificationFailed("N_T is the identity".into()));
        }
        if bool::from(proof.a_prime.is_identity()) || bool::from(proof.t_bbs.is_identity()) {
            return Err(ActError::VerificationFailed("Zero point in proof".into()));
        }
        let c_bridge  = &proof.c_delta + &(&generators.h[3] * &Scalar::from(current_epoch).0);
        let beq_bytes = proof.batched_eq.to_bytes();
        let c = RefreshProver::challenge(
            h_ctx, pk_master, current_epoch,
            proof.n_t, proof.k_daily, proof.c_delta,
            &beq_bytes,
            proof.a_prime, proof.a_bar, proof.t_bbs,
            proof.t_scale_n, proof.t_n, proof.t_scale_d, proof.t_d,
            proof.t_scale_b, proof.t_b,
        );
        per_proof.push(PerProof { c_fr: c.0, c_bridge });
    }

    // ── Step 2: Derive RLC weights ρ_i ──────────────────────────────────────
    // Hash all per-proof challenges so that ρ_i is unpredictable to any prover
    // that submits proofs individually (Schwartz–Zippel soundness).
    let rho_seed: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(b"ACT:BatchVerify:Refresh:RLC");
        for pp in &per_proof {
            h.update(pp.c_fr.to_bytes_le());
        }
        h.finalize().into()
    };
    let mut rho_rng = rand_chacha::ChaCha20Rng::from_seed(rho_seed);
    let rhos: Vec<BlsScalar> = (0..n).map(|_| BlsScalar::random(&mut rho_rng)).collect();

    // ── Step 3: Batched Schnorr-bridge MSM ──────────────────────────────────
    // Static base accumulators: ∑ ρ_i · sc_*_i for h0, h1, h2, h3, h4, g1.
    let mut acc_h0 = BlsScalar::ZERO;
    let mut acc_h1 = BlsScalar::ZERO;
    let mut acc_h2 = BlsScalar::ZERO;
    let mut acc_h3 = BlsScalar::ZERO;
    let mut acc_h4 = BlsScalar::ZERO;
    let mut acc_g1 = BlsScalar::ZERO;

    // Dynamic bases (13 per proof): each gets scalar ρ_i · sc_*_i.
    let mut dyn_bases:   Vec<G1Affine>   = Vec::with_capacity(13 * n);
    let mut dyn_scalars: Vec<BlsScalar>  = Vec::with_capacity(13 * n);

    for (i, (proof, pp)) in proofs.iter().zip(per_proof.iter()).enumerate() {
        let rho   = rhos[i];
        let c_fr  = pp.c_fr;
        let c2    = &c_fr * &c_fr;
        let c3    = &c2   * &c_fr;

        let sc_ht       = &c_fr  * &proof.z_k_tilde.0;
        let sc_nt       = -(&c_fr * &proof.z_r1.0);
        let sc_tscale_n =  c_fr;
        let sc_tn       = -c_fr;
        let sc_h0 = &(&c2 * &proof.z_v.0) + &(&(&c3 * &proof.z_w.0) + &proof.z_s_tilde.0);
        let sc_h1 = &(&c2 * &proof.z_u.0) + &proof.z_k_tilde.0;
        let sc_h2 = &(&c2 * &(&proof.z_r1.0 * &ep)) + &proof.z_c_tilde.0;
        let sc_h3 = &(&c3 + &BlsScalar::ONE) * &proof.z_e_tilde.0;
        let sc_h4 = &c2 * &proof.z_c_tilde.0;
        let sc_g1 = proof.z_r1.0;
        let sc_aprime   = -proof.z_e.0;
        let sc_kdaily   = -(&c2 * &proof.z_r1.0);
        let sc_cbridge  = -(&c3 * &proof.z_r1.0);
        let sc_abar     = -c_fr;
        let sc_td       = -c2;
        let sc_tscale_d =  c2;
        let sc_tb       = -c3;
        let sc_tscale_b =  c3;
        let sc_tbbs     = -BlsScalar::ONE;

        acc_h0 = &acc_h0 + &(&rho * &sc_h0);
        acc_h1 = &acc_h1 + &(&rho * &sc_h1);
        acc_h2 = &acc_h2 + &(&rho * &sc_h2);
        acc_h3 = &acc_h3 + &(&rho * &sc_h3);
        acc_h4 = &acc_h4 + &(&rho * &sc_h4);
        acc_g1 = &acc_g1 + &(&rho * &sc_g1);

        let dyn_pts = batch_normalize(&[
            h_t,
            proof.n_t, proof.t_scale_n, proof.t_n,
            proof.a_prime, proof.k_daily, pp.c_bridge,
            proof.a_bar,
            proof.t_d, proof.t_scale_d, proof.t_b, proof.t_scale_b,
            proof.t_bbs,
        ]);
        for (sc, pt) in [
            (sc_ht,       dyn_pts[0]),
            (sc_nt,       dyn_pts[1]),
            (sc_tscale_n, dyn_pts[2]),
            (sc_tn,       dyn_pts[3]),
            (sc_aprime,   dyn_pts[4]),
            (sc_kdaily,   dyn_pts[5]),
            (sc_cbridge,  dyn_pts[6]),
            (sc_abar,     dyn_pts[7]),
            (sc_td,       dyn_pts[8]),
            (sc_tscale_d, dyn_pts[9]),
            (sc_tb,       dyn_pts[10]),
            (sc_tscale_b, dyn_pts[11]),
            (sc_tbbs,     dyn_pts[12]),
        ] {
            dyn_bases.push(pt);
            dyn_scalars.push(&rho * &sc);
        }
    }

    let mut msm_bases:   Vec<G1Affine>  = Vec::with_capacity(6 + dyn_bases.len());
    let mut msm_scalars: Vec<BlsScalar> = Vec::with_capacity(6 + dyn_scalars.len());
    msm_bases.extend_from_slice(&[
        generators.h_affine[0], generators.h_affine[1], generators.h_affine[2],
        generators.h_affine[3], generators.h_affine[4], generators.g1_affine,
    ]);
    msm_scalars.extend_from_slice(&[acc_h0, acc_h1, acc_h2, acc_h3, acc_h4, acc_g1]);
    msm_bases.extend_from_slice(&dyn_bases);
    msm_scalars.extend_from_slice(&dyn_scalars);

    let combined = g1_msm(&msm_bases, &msm_scalars);
    if !bool::from(combined.is_identity()) {
        return Err(ActError::VerificationFailed("Batched Schnorr check failed".into()));
    }

    // ── Step 4: Batched pairing check ────────────────────────────────────────
    // Aggregate G1: a_prime_agg = ∑ ρ_i · A'_i, a_bar_agg = ∑ ρ_i · (−Ā_i).
    // One 2-pair multi_miller_loop + one final_exponentiation replaces N calls.
    let a_prime_aff: Vec<G1Affine> = proofs.iter().map(|p| G1Affine::from(p.a_prime)).collect();
    let a_bar_neg_aff: Vec<G1Affine> = proofs.iter().map(|p| G1Affine::from(-p.a_bar)).collect();
    let a_prime_agg = g1_msm(&a_prime_aff,   &rhos);
    let a_bar_agg   = g1_msm(&a_bar_neg_aff, &rhos);
    let pairing_result = Bls12::multi_miller_loop(&[
        (&G1Affine::from(a_prime_agg), &keys.pk_master_prepared),
        (&G1Affine::from(a_bar_agg),   &generators.g2_prepared),
    ])
    .final_exponentiation();
    if pairing_result != Gt::identity() {
        return Err(ActError::VerificationFailed("Batched pairing check failed".into()));
    }

    // ── Step 5: Verify all BEQ proofs concurrently ───────────────────────────
    let beq_check_results: Vec<Result<()>> = proofs
        .par_iter()
        .map(|proof| {
            let mut beq_ctx = Vec::new();
            beq_ctx.extend_from_slice(&h_ctx.to_bytes());
            beq_ctx.extend_from_slice(&current_epoch.to_le_bytes());
            let beq_commitments = [
                G1Affine::from(proof.a_prime),
                G1Affine::from(proof.a_bar),
                G1Affine::from(proof.t_bbs),
                G1Affine::from(proof.n_t),
                G1Affine::from(proof.k_daily),
            ];
            verify_batched_equality(
                &proof.batched_eq, proof.c_delta,
                generators.h[3], generators.h[0],
                &beq_ctx, &beq_commitments,
            )
        })
        .collect();
    for r in beq_check_results {
        r?;
    }

    // ── Step 6: Issue responses individually (requires sk_daily) ────────────
    let mut responses = Vec::with_capacity(n);
    for proof in proofs {
        let e_daily       = Scalar::rand(rng);
        let s_prime_daily = Scalar::rand(rng);
        let k_daily_aff   = G1Affine::from(proof.k_daily);
        let msg_part = g1_msm(
            &[generators.g1_affine, k_daily_aff, generators.h_affine[0]],
            &[BlsScalar::ONE, BlsScalar::ONE, s_prime_daily.0],
        );
        let denom = e_daily + keys.sk_daily;
        if denom.is_zero() {
            return Err(ActError::ProtocolError("Division by zero in issuance".into()));
        }
        let a_daily = &msg_part * &denom.inverse().0;
        responses.push(RefreshResponse { a_daily, e_daily, s_prime_daily });
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
    use crate::commitments::commit;
    use crate::hash::compute_h_ctx;
    use crate::msm::g1_msm;
    use crate::setup::{Generators, ServerKeys};
    use crate::types::Scalar;
    use rand::thread_rng;

    fn create_master_sig(
        rng: &mut impl RngCore,
        k_sub: Scalar,
        c_max: u32,
        e_max: u32,
        generators: &Generators,
        keys: &ServerKeys,
    ) -> BbsSignature {
        let r_sub     = Scalar::rand(rng);
        let k_sub_commit = commit(k_sub, r_sub, generators.h[1], generators.h[0]);
        let e_sub     = Scalar::rand(rng);
        let s_prime   = Scalar::rand(rng);
        let msg_part  = g1_msm(
            &[generators.g1_affine, G1Affine::from(k_sub_commit),
              generators.h_affine[0], generators.h_affine[2], generators.h_affine[3]],
            &[BlsScalar::ONE, BlsScalar::ONE, s_prime.0,
              BlsScalar::from(c_max as u64), BlsScalar::from(e_max as u64)],
        );
        let denom = e_sub + keys.sk_master;
        let a_sub = &msg_part * &denom.inverse().0;
        BbsSignature { a: a_sub, e: e_sub, s: r_sub + s_prime }
    }

    #[test]
    fn refresh_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let k_sub = Scalar::rand_nonzero(&mut rng);
        let c_max = 100u32;
        let e_max = 5000u32;
        let epoch = 1000u32;

        let master = create_master_sig(&mut rng, k_sub, c_max, e_max, &generators, &keys);
        let (client, proof) = RefreshProver::prove(
            &mut rng, &master, k_sub, c_max, e_max, epoch, &generators, &keys.pk_master, h_ctx,
        ).unwrap();
        let response = verify_refresh(&proof, epoch, &generators, &keys.pk_master, &keys, h_ctx, &mut rng).unwrap();
        let (daily_sig, k_daily) = client.finalize(response);
        assert!(!bool::from(daily_sig.a.is_identity()));
        assert!(!k_daily.is_zero());
    }

    #[test]
    fn expired_token_rejected() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let k_sub = Scalar::rand_nonzero(&mut rng);
        let master = create_master_sig(&mut rng, k_sub, 100, 1000, &generators, &keys);
        assert!(RefreshProver::prove(
            &mut rng, &master, k_sub, 100, 1000, 2000, &generators, &keys.pk_master, h_ctx,
        ).is_err());
    }

    #[test]
    fn batch_refresh_empty() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let responses = verify_refresh_batch(&[], 1000, &generators, &keys.pk_master, &keys, h_ctx, &mut rng).unwrap();
        assert!(responses.is_empty());
    }

    #[test]
    fn batch_refresh_single() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let k_sub = Scalar::rand_nonzero(&mut rng);
        let epoch = 500u32;
        let master = create_master_sig(&mut rng, k_sub, 100, 5000, &generators, &keys);
        let (_client, proof) = RefreshProver::prove(
            &mut rng, &master, k_sub, 100, 5000, epoch, &generators, &keys.pk_master, h_ctx,
        ).unwrap();
        let responses = verify_refresh_batch(
            &[proof], epoch, &generators, &keys.pk_master, &keys, h_ctx, &mut rng,
        ).unwrap();
        assert_eq!(responses.len(), 1);
        assert!(!bool::from(responses[0].a_daily.is_identity()));
    }

    #[test]
    fn batch_refresh_multiple() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let epoch = 1000u32;

        const BATCH: usize = 4;
        let mut proofs = Vec::with_capacity(BATCH);
        for _ in 0..BATCH {
            let k_sub = Scalar::rand_nonzero(&mut rng);
            let master = create_master_sig(&mut rng, k_sub, 100, 5000, &generators, &keys);
            let (_client, proof) = RefreshProver::prove(
                &mut rng, &master, k_sub, 100, 5000, epoch, &generators, &keys.pk_master, h_ctx,
            ).unwrap();
            proofs.push(proof);
        }

        let responses = verify_refresh_batch(
            &proofs, epoch, &generators, &keys.pk_master, &keys, h_ctx, &mut rng,
        ).unwrap();
        assert_eq!(responses.len(), BATCH);
        for r in &responses {
            assert!(!bool::from(r.a_daily.is_identity()));
        }
    }

    #[test]
    fn batch_refresh_rejects_bad_proof() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let keys2 = ServerKeys::generate(&mut rng); // different keys → wrong sig
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);
        let epoch = 1000u32;

        let mut proofs = Vec::new();
        for _ in 0..3usize {
            let k_sub = Scalar::rand_nonzero(&mut rng);
            let master = create_master_sig(&mut rng, k_sub, 100, 5000, &generators, &keys);
            let (_client, proof) = RefreshProver::prove(
                &mut rng, &master, k_sub, 100, 5000, epoch, &generators, &keys.pk_master, h_ctx,
            ).unwrap();
            proofs.push(proof);
        }
        // Replace one proof with one signed under different keys → batch must fail.
        {
            let k_sub = Scalar::rand_nonzero(&mut rng);
            let master = create_master_sig(&mut rng, k_sub, 100, 5000, &generators, &keys2);
            let (_client, bad_proof) = RefreshProver::prove(
                &mut rng, &master, k_sub, 100, 5000, epoch, &generators, &keys2.pk_master, h_ctx,
            ).unwrap();
            proofs.push(bad_proof);
        }

        assert!(verify_refresh_batch(
            &proofs, epoch, &generators, &keys.pk_master, &keys, h_ctx, &mut rng,
        ).is_err());
    }
}
