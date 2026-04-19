//! Global setup and key generation.
//!
//! This module defines the BBS+ generators and server key pairs. The generators
//! are derived via hash‑to‑curve to ensure no trapdoors. Server keys are
//! generated with distinct signing keys for Master and Daily tokens as required
//! by the specification.

use ark_bls12_381::{G1Affine, G1Projective, G2Projective};
use ark_ec::{bls12::G2Prepared, CurveGroup, Group};
use ark_std::rand::RngCore;
use ark_std::Zero;
use std::sync::OnceLock;
use crate::hash::hash_to_g1;
use crate::types::Scalar;

/// Type alias for the cached G2 pairing line functions used by BLS12-381.
/// Equivalent to `<Bls12_381 as Pairing>::G2Prepared`.
type G2Prep = G2Prepared<ark_bls12_381::Config>;

/// BBS+ generators: `g1 ∈ G1`, `g2 ∈ G2`, and `h_0, h_1, h_2, h_3, h_4 ∈ G1`.
///
/// The generators are created deterministically using the domain separation tag
/// `"ACT:BBS:"` followed by the index.
///
/// **Performance:** affine forms (`g1_affine`, `h_affine`) are precomputed via
/// a single batch field inversion at initialization and cached in the global
/// singleton so that MSM callers never pay for projective→affine conversions.
/// `g2_prepared` caches the G2 pairing line functions for g2, eliminating their
/// recomputation on every `multi_pairing` call.
#[derive(Clone, Debug)]
pub struct Generators {
    pub g1: G1Projective,
    pub g2: G2Projective,
    pub h: [G1Projective; 5],
    /// Precomputed affine form of `g1` (z = 1 for the standard generator,
    /// so this is trivially free).
    pub g1_affine: G1Affine,
    /// Precomputed affine forms of `h[0..5]`, computed via a single batch
    /// field inversion at initialization time.
    pub h_affine: [G1Affine; 5],
    /// Precomputed G2Prepared form of `g2` (pairing line functions).
    /// Caching this avoids recomputing the line functions on every
    /// `multi_pairing` call in the server verifiers.
    pub g2_prepared: G2Prep,
}

/// Process-wide singleton for the deterministic BBS+ generators.
///
/// The five `hash_to_g1` calls and the batch affine normalization happen
/// exactly once per process; all subsequent `Generators::new()` calls return a
/// cheap clone.
static GENERATORS: OnceLock<Generators> = OnceLock::new();

impl Generators {
    /// Return the process-wide singleton generators (initialised on first call).
    pub fn global() -> &'static Self {
        GENERATORS.get_or_init(Self::compute)
    }

    /// Construct the generators.
    ///
    /// In practice this just clones the singleton so the expensive hash-to-curve
    /// work is never repeated after the first call.
    pub fn new() -> Self {
        Self::global().clone()
    }

    /// Perform the actual expensive initialisation (called at most once).
    fn compute() -> Self {
        let g1 = G1Projective::generator();
        let g2 = G2Projective::generator();
        let dst = b"ACT:BBS:";
        let mut h = [G1Projective::zero(); 5];
        for (i, elem) in h.iter_mut().enumerate() {
            // I2OSP(i, 4): 4-byte big-endian index. The DST is passed as the
            // first argument to hash_to_g1 and must NOT be repeated in msg.
            let msg = (i as u32).to_be_bytes();
            *elem = hash_to_g1(dst, &msg);
        }

        // Single batch field inversion to convert all h[0..5] to affine form.
        // This is the only batch inversion needed during the entire lifetime of
        // the generators.
        let h_batch = G1Projective::normalize_batch(&h);
        let h_affine = [h_batch[0], h_batch[1], h_batch[2], h_batch[3], h_batch[4]];

        // g1 is the standard generator (z-coordinate = 1), so into_affine is free.
        let g1_affine = g1.into_affine();

        // Precompute the G2Prepared pairing line functions for g2.  These are
        // completely static and would otherwise be recomputed on every pairing
        // call inside the server verifiers.
        let g2_prepared = G2Prep::from(g2.into_affine());

        Self { g1, g2, h, g1_affine, h_affine, g2_prepared }
    }
}

impl Default for Generators {
    fn default() -> Self {
        Self::new()
    }
}

/// Server key pair containing separate signing keys for Master and Daily tokens.
#[derive(Clone, Debug)]
pub struct ServerKeys {
    /// Master token signing key (scalar).
    pub sk_master: Scalar,
    /// Master token public key (G2 point).
    pub pk_master: G2Projective,
    /// Daily/Refund token signing key (scalar).
    pub sk_daily: Scalar,
    /// Daily token public key (G2 point).
    pub pk_daily: G2Projective,
    /// Precomputed G2Prepared form of `pk_master` (pairing line functions).
    /// Cached once at key-generation time to avoid recomputing on every verify.
    pub pk_master_prepared: G2Prep,
    /// Precomputed G2Prepared form of `pk_daily` (pairing line functions).
    /// Cached once at key-generation time to avoid recomputing on every verify.
    pub pk_daily_prepared: G2Prep,
}

impl ServerKeys {
    /// Generate a fresh key pair using the provided RNG.
    ///
    /// # Security
    /// The two secret keys are generated independently to prevent any
    /// cross‑protocol attacks.
    pub fn generate(rng: &mut impl RngCore) -> Self {
        let sk_master = Scalar::rand_nonzero(rng);
        let pk_master = G2Projective::generator() * sk_master.0;
        let sk_daily = Scalar::rand_nonzero(rng);
        let pk_daily = G2Projective::generator() * sk_daily.0;
        // Precompute G2Prepared forms so every verification call can reuse them.
        let pk_master_prepared = G2Prep::from(pk_master.into_affine());
        let pk_daily_prepared  = G2Prep::from(pk_daily.into_affine());
        Self {
            sk_master,
            pk_master,
            sk_daily,
            pk_daily,
            pk_master_prepared,
            pk_daily_prepared,
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::thread_rng;

    #[test]
    fn generators_are_distinct() {
        let gens = Generators::new();
        // h0..h4 should all be distinct from each other and from g1.
        for i in 0..5 {
            assert_ne!(gens.g1, gens.h[i]);
            for j in 0..5 {
                if i != j {
                    assert_ne!(gens.h[i], gens.h[j]);
                }
            }
        }
    }

    #[test]
    fn generators_are_deterministic() {
        let gens1 = Generators::new();
        let gens2 = Generators::new();
        for i in 0..5 {
            assert_eq!(gens1.h[i], gens2.h[i], "generator h[{i}] must be deterministic");
        }
    }

    #[test]
    fn generator_dst_not_in_message() {
        // Ensure generators are derived as hash_to_g1(dst, I2OSP(i)) and NOT
        // as hash_to_g1(dst, dst || I2OSP(i)).  We verify by checking the actual
        // output is consistent with the fixed derivation.
        let gens = Generators::new();
        let expected_h0 = hash_to_g1(b"ACT:BBS:", &0u32.to_be_bytes());
        let expected_h4 = hash_to_g1(b"ACT:BBS:", &4u32.to_be_bytes());
        assert_eq!(gens.h[0], expected_h0, "h[0] derivation mismatch");
        assert_eq!(gens.h[4], expected_h4, "h[4] derivation mismatch");
    }

    #[test]
    fn server_keys_distinct() {
        let mut rng = thread_rng();
        let keys = ServerKeys::generate(&mut rng);
        assert_ne!(keys.sk_master, keys.sk_daily);
        assert_ne!(keys.pk_master, keys.pk_daily);
        assert!(!keys.sk_master.is_zero());
        assert!(!keys.sk_daily.is_zero());
    }
}
