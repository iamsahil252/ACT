//! Global setup and key generation.
//!
//! This module defines the BBS+ generators and server key pairs. The generators
//! are derived via hash‑to‑curve to ensure no trapdoors. Server keys are
//! generated with distinct signing keys for Master and Daily tokens as required
//! by the specification.

extern crate alloc;
use alloc::vec::Vec;
use ark_std::vec;
use ark_bls12_381::{G1Projective, G2Projective};
use ark_ec::CurveGroup;
use ark_std::rand::RngCore;
use crate::hash::hash_to_g1;
use crate::types::Scalar;

/// BBS+ generators: `g1 ∈ G1`, `g2 ∈ G2`, and `h_0, h_1, h_2, h_3, h_4 ∈ G1`.
///
/// The generators are created deterministically using the domain separation tag
/// `"ACT:BBS:"` followed by the index.
#[derive(Clone, Debug)]
pub struct Generators {
    pub g1: G1Projective,
    pub g2: G2Projective,
    pub h: [G1Projective; 5],
}

impl Generators {
    pub fn new() -> Self {
        let g1 = G1Projective::generator();
        let g2 = G2Projective::generator();
        let dst = b"ACT:BBS:";
        let mut h = [G1Projective::zero(); 5];
        for (i, elem) in h.iter_mut().enumerate() {
            let msg = [dst.as_slice(), &[i as u8]].concat();
            *elem = hash_to_g1(dst, &msg);
        }
        Self { g1, g2, h }
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
        Self {
            sk_master,
            pk_master,
            sk_daily,
            pk_daily,
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
    fn server_keys_distinct() {
        let mut rng = thread_rng();
        let keys = ServerKeys::generate(&mut rng);
        assert_ne!(keys.sk_master, keys.sk_daily);
        assert_ne!(keys.pk_master, keys.pk_daily);
        assert!(!keys.sk_master.is_zero());
        assert!(!keys.sk_daily.is_zero());
    }
}
