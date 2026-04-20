//! Global setup and key generation backed by blstrs.

use blstrs::{G1Affine, G1Projective, G2Affine, G2Prepared, G2Projective};
use group::Group;
use rand_core::RngCore;
use std::sync::OnceLock;

use crate::hash::hash_to_g1;
use crate::msm::{batch_normalize, FixedBaseTable};
use crate::types::Scalar;

/// BBS+ generators: `g1 ∈ G1`, `g2 ∈ G2`, and `h_0 … h_4 ∈ G1`.
///
/// All affine forms, G2Prepared pairing tables, and fixed-base scalar
/// multiplication tables are precomputed exactly once per process and shared
/// via a `OnceLock` singleton.
#[derive(Clone, Debug)]
pub struct Generators {
    pub g1: G1Projective,
    pub g2: G2Projective,
    pub h: [G1Projective; 5],
    /// Precomputed affine form of `g1`.
    pub g1_affine: G1Affine,
    /// Precomputed affine forms of `h[0..5]`.
    pub h_affine: [G1Affine; 5],
    /// Precomputed G2Prepared pairing line functions for `g2`.
    pub g2_prepared: G2Prepared,
    /// Precomputed fixed-base scalar-multiplication table for `g1`.
    pub g1_table: FixedBaseTable,
    /// Precomputed fixed-base scalar-multiplication tables for `h[0..5]`.
    pub h_tables: [FixedBaseTable; 5],
}

static GENERATORS: OnceLock<Generators> = OnceLock::new();

impl Generators {
    /// Return the process-wide singleton (initialised on first call).
    pub fn global() -> &'static Self {
        GENERATORS.get_or_init(Self::compute)
    }

    /// Cheap clone of the singleton.
    pub fn new() -> Self {
        Self::global().clone()
    }

    fn compute() -> Self {
        let g1 = G1Projective::generator();
        let g2 = G2Projective::generator();
        let dst = b"ACT:BBS:";
        let mut h = [G1Projective::identity(); 5];
        for (i, elem) in h.iter_mut().enumerate() {
            let msg = (i as u32).to_be_bytes();
            *elem = hash_to_g1(dst, &msg);
        }

        // Convert all h[0..5] to affine using individual field inversions.
        let h_affines = batch_normalize(&h);
        let h_affine = [
            h_affines[0], h_affines[1], h_affines[2],
            h_affines[3], h_affines[4],
        ];
        let g1_affine = G1Affine::from(g1);
        let g2_prepared = G2Prepared::from(G2Affine::from(g2));

        // Precompute fixed-base scalar-multiplication tables for all five
        // protocol generators.  Each table holds 64 windows × 15 non-zero
        // affine entries ≈ 90 KB; computed once at startup via the singleton.
        let g1_table = FixedBaseTable::new(&g1_affine);
        let h_tables = [
            FixedBaseTable::new(&h_affine[0]),
            FixedBaseTable::new(&h_affine[1]),
            FixedBaseTable::new(&h_affine[2]),
            FixedBaseTable::new(&h_affine[3]),
            FixedBaseTable::new(&h_affine[4]),
        ];

        Self { g1, g2, h, g1_affine, h_affine, g2_prepared, g1_table, h_tables }
    }
}

impl Default for Generators {
    fn default() -> Self { Self::new() }
}

/// Server key pair with separate Master and Daily signing keys.
#[derive(Clone, Debug)]
pub struct ServerKeys {
    pub sk_master: Scalar,
    pub pk_master: G2Projective,
    pub sk_daily: Scalar,
    pub pk_daily: G2Projective,
    /// Precomputed G2Prepared for `pk_master` (avoids re-derivation per verify).
    pub pk_master_prepared: G2Prepared,
    /// Precomputed G2Prepared for `pk_daily`.
    pub pk_daily_prepared: G2Prepared,
}

impl ServerKeys {
    pub fn generate(rng: &mut impl RngCore) -> Self {
        let sk_master = Scalar::rand_nonzero(rng);
        let pk_master = &G2Projective::generator() * &sk_master.0;
        let sk_daily = Scalar::rand_nonzero(rng);
        let pk_daily = &G2Projective::generator() * &sk_daily.0;
        let pk_master_prepared = G2Prepared::from(G2Affine::from(pk_master));
        let pk_daily_prepared  = G2Prepared::from(G2Affine::from(pk_daily));
        Self { sk_master, pk_master, sk_daily, pk_daily,
               pk_master_prepared, pk_daily_prepared }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;

    #[test]
    fn generators_are_distinct() {
        let gens = Generators::new();
        for i in 0..5 {
            assert_ne!(gens.g1, gens.h[i]);
            for j in 0..5 {
                if i != j { assert_ne!(gens.h[i], gens.h[j]); }
            }
        }
    }

    #[test]
    fn generators_are_deterministic() {
        let gens1 = Generators::new();
        let gens2 = Generators::new();
        for i in 0..5 {
            assert_eq!(gens1.h[i], gens2.h[i]);
        }
    }

    #[test]
    fn generator_derivation() {
        let gens = Generators::new();
        assert_eq!(gens.h[0], hash_to_g1(b"ACT:BBS:", &0u32.to_be_bytes()));
        assert_eq!(gens.h[4], hash_to_g1(b"ACT:BBS:", &4u32.to_be_bytes()));
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
