//! Domain-separated hashing utilities backed by blstrs and SHA-256/SHA-512.

extern crate alloc;
use blstrs::{G1Affine, G1Projective, G2Affine, G2Projective, Scalar as BlsScalar};
use group::Group;
use sha2::{Digest, Sha256, Sha512};
use std::io::Write as _;

use crate::setup::Generators;
use crate::types::Scalar;

// ============================================================================
// BLS12-381 scalar field modulus in little-endian u64 limbs
// r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
// ============================================================================
const R_LIMBS: [u64; 4] = [
    0xffffffff00000001,
    0x53bda402fffe5bfe,
    0x3339d80809a1d805,
    0x73eda753299d7d48,
];

/// Reduce an arbitrary 32-byte little-endian integer modulo the scalar field order.
///
/// For a 256-bit input, at most two subtractions of `r` are needed before the
/// value is canonical.  This is called from `scalar_from_hash` and from the
/// `Scalar::from_bytes_unchecked` path.
pub(crate) fn scalar_from_le_bytes_mod_order(bytes: &[u8; 32]) -> BlsScalar {
    let mut v = le_bytes_to_u64x4(bytes);

    // Subtract r until v < r (at most 2 iterations for 256-bit inputs).
    for _ in 0..3 {
        if lt_r(&v) {
            let canonical = u64x4_to_le_bytes(&v);
            return Option::<BlsScalar>::from(BlsScalar::from_bytes_le(&canonical))
                .expect("v < r guaranteed by lt_r check");
        }
        v = sub_u64x4(v, R_LIMBS);
    }
    // After 3 subtractions the value must be < r for any 256-bit input.
    let canonical = u64x4_to_le_bytes(&v);
    Option::<BlsScalar>::from(BlsScalar::from_bytes_le(&canonical))
        .expect("mod reduction failed – value still not canonical")
}

// ---- 256-bit integer helpers ------------------------------------------------

#[inline]
fn le_bytes_to_u64x4(bytes: &[u8; 32]) -> [u64; 4] {
    let mut limbs = [0u64; 4];
    for i in 0..4 {
        limbs[i] = u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().unwrap());
    }
    limbs
}

#[inline]
fn u64x4_to_le_bytes(limbs: &[u64; 4]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for i in 0..4 {
        bytes[i * 8..(i + 1) * 8].copy_from_slice(&limbs[i].to_le_bytes());
    }
    bytes
}

#[inline]
fn lt_r(v: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if v[i] != R_LIMBS[i] {
            return v[i] < R_LIMBS[i];
        }
    }
    false // equal to r → not strictly less
}

#[inline]
fn sub_u64x4(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let mut result = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (d1, ov1) = a[i].overflowing_sub(b[i]);
        let (d2, ov2) = d1.overflowing_sub(borrow);
        result[i] = d2;
        borrow = u64::from(ov1 | ov2);
    }
    result
}

// ============================================================================
// Public API
// ============================================================================

/// Compute the application context hash `H_ctx`.
///
/// Binds all Fiat–Shamir challenges to a specific deployment and set of public
/// keys, preventing cross-deployment replay attacks.
pub fn compute_h_ctx(
    app_id: &str,
    pk_master: &G2Projective,
    pk_daily: &G2Projective,
    generators: &Generators,
) -> Scalar {
    let mut hasher = Sha256::new();
    hasher.update(b"ACT:Context");
    hasher.update(app_id.as_bytes());
    {
        let mut w = HasherWriter(&mut hasher);
        write_g2(&mut w, *pk_master);
        write_g2(&mut w, *pk_daily);
        write_g1(&mut w, generators.g1);
        write_g2(&mut w, generators.g2);
        for h in &generators.h {
            write_g1(&mut w, *h);
        }
    }
    let d = hasher.finalize();
    let bytes: [u8; 32] = { let s: &[u8] = &d[..]; s.try_into().unwrap() };
    scalar_from_hash(&bytes)
}

/// Hash a message to a point in G1 using the BLS12-381 hash-to-curve suite.
///
/// Implements RFC 9380 `hash_to_curve` via the blst C library (WB-SSWU method
/// with `expand_message_xmd` using SHA-256).  The DST provides protocol-level
/// domain separation.
pub fn hash_to_g1(dst: &[u8], message: &[u8]) -> G1Projective {
    G1Projective::hash_to_curve(message, dst, b"")
}

/// Hash an arbitrary preimage to a scalar (Fiat–Shamir helper).
pub fn hash_to_scalar(preimage: &[u8]) -> Scalar {
    let digest: [u8; 32] = {
        let d = Sha256::digest(preimage);
        let s: &[u8] = &d[..];
        s.try_into().unwrap()
    };
    scalar_from_hash(&digest)
}

/// An adapter that implements `std::io::Write` by forwarding bytes into a
/// running `sha2::Sha256` hasher.
///
/// Lets serialization routines feed bytes directly into the hasher without any
/// intermediate heap allocation.
pub(crate) struct HasherWriter<'a>(pub &'a mut Sha256);

impl std::io::Write for HasherWriter<'_> {
    #[inline(always)]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.update(buf);
        Ok(buf.len())
    }
    #[inline(always)]
    fn flush(&mut self) -> std::io::Result<()> { Ok(()) }
}

/// Finalise a running `Sha256` hasher and return a Fiat–Shamir scalar.
pub(crate) fn hash_to_scalar_from_hasher(hasher: Sha256) -> Scalar {
    let digest: [u8; 32] = {
        let d = hasher.finalize();
        let s: &[u8] = &d[..];
        s.try_into().unwrap()
    };
    scalar_from_hash(&digest)
}

/// Write a compressed G1 projective point (48 bytes) into a writer.
#[inline]
pub(crate) fn write_g1(w: &mut impl std::io::Write, p: G1Projective) {
    w.write_all(&G1Affine::from(p).to_compressed()).unwrap();
}

/// Write a compressed G1 affine point (48 bytes) into a writer.
#[inline]
pub(crate) fn write_g1_affine(w: &mut impl std::io::Write, p: G1Affine) {
    w.write_all(&p.to_compressed()).unwrap();
}

/// Write a compressed G2 projective point (96 bytes) into a writer.
#[inline]
pub(crate) fn write_g2(w: &mut impl std::io::Write, p: G2Projective) {
    w.write_all(&G2Affine::from(p).to_compressed()).unwrap();
}

/// Write a scalar's canonical LE bytes (32 bytes) into a writer.
#[inline]
pub(crate) fn write_scalar(w: &mut impl std::io::Write, s: Scalar) {
    w.write_all(&s.to_bytes()).unwrap();
}

// ---- Internal helpers -------------------------------------------------------

/// `K = 2^256 mod r` (little-endian), precomputed.
///
/// Used by `scalar_from_hash` to implement the "two-half" wide reduction:
///
///   result = (lo + hi · 2^256) mod r
///          = (lo mod r + (hi mod r) · K) mod r
///
/// where `lo` and `hi` are the lower and upper 256-bit halves of the 512-bit
/// SHA-512 digest.  Since SHA-512 maps to a (pseudo-)uniform 512-bit value,
/// the output distribution has statistical distance ≤ r / 2^512 ≈ 2^−257 from
/// uniform, compared with ≈ 2^−1 for the naive 256-bit repeated-subtraction.
///
/// Derivation: r ≈ 2^254.86, so floor(2^256 / r) = 2 and
///   K = 2^256 − 2r = 0x1824b159_acc5056f_998c4fef_ecbc4ff5_5884b7fa_00034802_00000001_fffffffe
const K_2_256_MOD_R: [u8; 32] = [
    // limb 0 (least-significant 64 bits) = 0x00000001_fffffffe
    0xfe, 0xff, 0xff, 0xff, 0x01, 0x00, 0x00, 0x00,
    // limb 1 = 0x5884b7fa_00034802
    0x02, 0x48, 0x03, 0x00, 0xfa, 0xb7, 0x84, 0x58,
    // limb 2 = 0x998c4fef_ecbc4ff5
    0xf5, 0x4f, 0xbc, 0xec, 0xef, 0x4f, 0x8c, 0x99,
    // limb 3 (most-significant 64 bits) = 0x1824b159_acc5056f
    0x6f, 0x05, 0xc5, 0xac, 0x59, 0xb1, 0x24, 0x18,
];

/// Convert a 32-byte SHA-256 digest to a scalar using a bias-free wide reduction.
///
/// The 32-byte digest is expanded to 64 bytes via SHA-512, then the two 256-bit
/// halves are combined as `(lo + hi · 2^256) mod r`.  This matches the
/// hash-to-field strategy of RFC 9380 §5.2 and eliminates the per-value bias
/// that arises from naive repeated subtraction on a 256-bit digest.
fn scalar_from_hash(digest: &[u8; 32]) -> Scalar {
    // Expand to 64 bytes.  Treating SHA-512 as a random oracle, the output is
    // indistinguishable from a uniform 512-bit value.
    let wide_out = Sha512::digest(digest.as_slice());
    let wide_bytes: [u8; 64] = {
        let s: &[u8] = &wide_out[..];
        s.try_into().expect("SHA-512 output is always 64 bytes")
    };

    let lo: &[u8; 32] = wide_bytes[..32].try_into()
        .expect("lower 32 bytes of 64-byte array always fits");
    let hi: &[u8; 32] = wide_bytes[32..].try_into()
        .expect("upper 32 bytes of 64-byte array always fits");

    let s_lo = scalar_from_le_bytes_mod_order(lo);
    let s_hi = scalar_from_le_bytes_mod_order(hi);

    // K = 2^256 mod r; guaranteed < r so from_bytes_le succeeds.
    let k = Option::<BlsScalar>::from(BlsScalar::from_bytes_le(&K_2_256_MOD_R))
        .expect("K_2_256_MOD_R is a valid canonical BLS12-381 scalar");

    // Combine: (lo + hi · K) mod r  ≡  (lo + hi · 2^256) mod r
    Scalar(&s_lo + &(&s_hi * &k))
}

impl Scalar {
    /// Create a scalar by reducing a 32-byte LE array modulo the group order.
    pub(crate) fn from_bytes_mod_order(bytes: &[u8; 32]) -> Self {
        Self(scalar_from_le_bytes_mod_order(bytes))
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::setup::Generators;
    use group::Group;

    #[test]
    fn h_ctx_deterministic() {
        let generators = Generators::new();
        let pk_master = G2Projective::generator();
        let pk_daily = &pk_master * &BlsScalar::from(2u64);
        let h1 = compute_h_ctx("test", &pk_master, &pk_daily, &generators);
        let h2 = compute_h_ctx("test", &pk_master, &pk_daily, &generators);
        assert_eq!(h1, h2);
        let h3 = compute_h_ctx("other", &pk_master, &pk_daily, &generators);
        assert_ne!(h1, h3);
    }

    #[test]
    fn hash_to_g1_domain_separation() {
        let p1 = hash_to_g1(b"ACT:Epoch:", b"epoch:42");
        let p2 = hash_to_g1(b"ACT:Other:", b"epoch:42");
        assert_ne!(p1, p2);
    }

    #[test]
    fn hash_to_g1_deterministic() {
        let p1 = hash_to_g1(b"ACT:Epoch:", b"epoch:42");
        let p2 = hash_to_g1(b"ACT:Epoch:", b"epoch:42");
        assert_eq!(p1, p2);
    }

    #[test]
    fn hash_to_g1_is_not_generator() {
        let p = hash_to_g1(b"ACT:Test:", b"hello");
        assert_ne!(p, G1Projective::generator());
        assert!(!bool::from(p.is_identity()));
    }

    #[test]
    fn hash_to_scalar_deterministic() {
        let s1 = hash_to_scalar(b"test preimage");
        let s2 = hash_to_scalar(b"test preimage");
        assert_eq!(s1, s2);
    }

    #[test]
    fn scalar_from_mod_order_max_bytes() {
        // All 0xFF bytes (which is > r); should still produce a valid scalar.
        let bytes = [0xFFu8; 32];
        let s = scalar_from_le_bytes_mod_order(&bytes);
        // Verify the output is canonical by round-tripping.
        let back = s.to_bytes_le();
        let s2 = BlsScalar::from_bytes_le(&back).unwrap();
        assert_eq!(s, s2);
    }

    /// Verify the precomputed constant K = 2^256 mod r.
    ///
    /// We compute 2^256 mod r via repeated squaring and compare with K_2_256_MOD_R.
    #[test]
    fn k_2_256_mod_r_constant_is_correct() {
        // 2^256 mod r via iterated squaring in the scalar field.
        let two = BlsScalar::from(2u64);
        let mut pow = BlsScalar::from(1u64);
        for _ in 0..256 {
            pow = &pow * &two;
        }
        let k = Option::<BlsScalar>::from(BlsScalar::from_bytes_le(&K_2_256_MOD_R))
            .expect("K constant must be a valid scalar");
        assert_eq!(pow, k, "K_2_256_MOD_R does not equal 2^256 mod r");
    }

    /// Verify that scalar_from_hash produces a uniform-looking distribution:
    /// two different inputs must yield different outputs and both be canonical.
    #[test]
    fn scalar_from_hash_differs_on_distinct_inputs() {
        let d1 = [0x01u8; 32];
        let d2 = [0x02u8; 32];
        let s1 = scalar_from_hash(&d1);
        let s2 = scalar_from_hash(&d2);
        assert_ne!(s1, s2);
        // Both must be canonical (round-trip via bytes).
        assert_eq!(Scalar::from_bytes(&s1.to_bytes()).unwrap(), s1);
        assert_eq!(Scalar::from_bytes(&s2.to_bytes()).unwrap(), s2);
    }
}
