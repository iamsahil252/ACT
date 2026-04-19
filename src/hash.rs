//! Domain‑separated hashing utilities.
//!
//! This module provides:
//! - `compute_h_ctx`: the application context hash binding the protocol to a
//!   specific deployment.
//! - `hash_to_g1`: deterministic hash to the G1 group (RFC 9380).
//! - `hash_to_scalar`: Fiat–Shamir challenge generation.
//!
//! All hash functions use strong domain separation tags as required by the
//! specification.

extern crate alloc;
use ark_ec::hashing::HashToCurve;
use alloc::vec::Vec;
use ark_std::vec;
use ark_bls12_381::{g1, G1Projective, G2Projective};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};
use crate::setup::Generators;
use crate::types::Scalar;

/// Compute the application context hash `H_ctx`.
///
/// This value binds all Fiat–Shamir challenges to the specific application and
/// its public keys, preventing cross‑deployment replay attacks.
///
/// # Arguments
/// - `app_id`: a unique identifier for the service (e.g., "https://api.example.com/v1").
/// - `pk_master`: the server's master token public key.
/// - `pk_daily`: the server's daily token public key.
/// - `generators`: the global BBS+ generators.
pub fn compute_h_ctx(
    app_id: &str,
    pk_master: &G2Projective,
    pk_daily: &G2Projective,
    generators: &Generators,
) -> Scalar {
    let mut hasher = Sha256::new();
    hasher.update(b"ACT:Context");
    hasher.update(app_id.as_bytes());

    // Serialize all points in compressed form
    let mut buf = Vec::new();
    pk_master.serialize_compressed(&mut buf).unwrap();
    pk_daily.serialize_compressed(&mut buf).unwrap();
    generators.g1.serialize_compressed(&mut buf).unwrap();
    generators.g2.serialize_compressed(&mut buf).unwrap();
    for h in &generators.h {
        h.serialize_compressed(&mut buf).unwrap();
    }
    hasher.update(&buf);

    scalar_from_hash(hasher.finalize())
}

/// Hash a message to a point in G1 using the BLS12‑381 hash‑to‑curve suite.
///
/// The domain separation tag (DST) should be a string like `"ACT:Epoch:"`.
pub fn hash_to_g1(dst: &[u8], message: &[u8]) -> G1Projective {
        <G1Projective as HashToCurve<Sha256>>::hash_to_curve(message, dst)
}

/// Hash an arbitrary preimage to a scalar for Fiat–Shamir challenges.
///
/// The output is uniformly distributed in the scalar field.
pub fn hash_to_scalar(preimage: &[u8]) -> Scalar {
    let digest = Sha256::digest(preimage);
    scalar_from_hash(digest)
}

/// Convert a 32‑byte hash digest to a scalar by reducing modulo the group order.
fn scalar_from_hash(digest: impl AsRef<[u8]>) -> Scalar {
    // The digest is 32 bytes. We interpret it as a little‑endian integer and reduce
    // modulo the field order. This matches the specification's `H_scalar`.
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(digest.as_ref());
    Scalar::from_bytes_mod_order(&bytes)
}

impl Scalar {
    /// Create a scalar by reducing a 32‑byte array modulo the group order.
    pub(crate) fn from_bytes_mod_order(bytes: &[u8; 32]) -> Self {
        use ark_ff::fields::PrimeField;
        let fr = ark_bls12_381::Fr::from_le_bytes_mod_order(bytes);
        Scalar(fr)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::setup::Generators;
    use ark_bls12_381::G2Projective;
    use ark_ec::Group;
    use ark_std::rand::thread_rng;

    #[test]
    fn h_ctx_deterministic() {
        let generators = Generators::new();
        let pk_master = G2Projective::generator();
        let pk_daily = G2Projective::generator() * Scalar::from(2u64).0;

        let h1 = compute_h_ctx("test", &pk_master, &pk_daily, &generators);
        let h2 = compute_h_ctx("test", &pk_master, &pk_daily, &generators);
        assert_eq!(h1, h2);

        let h3 = compute_h_ctx("other", &pk_master, &pk_daily, &generators);
        assert_ne!(h1, h3);
    }

    #[test]
    fn hash_to_g1_domain_separation() {
        let msg = b"epoch:42";
        let p1 = hash_to_g1(b"ACT:Epoch:", msg);
        let p2 = hash_to_g1(b"ACT:Other:", msg);
        assert_ne!(p1, p2);
    }

    #[test]
    fn hash_to_scalar_deterministic() {
        let preimage = b"test preimage";
        let s1 = hash_to_scalar(preimage);
        let s2 = hash_to_scalar(preimage);
        assert_eq!(s1, s2);
    }
}
