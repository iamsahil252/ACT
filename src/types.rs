//! Core types for the ACT protocol.
//!
//! This module defines `Scalar` (an element of the BLS12-381 scalar field) and
//! compressed representations for G1 and G2 points, all backed by the blstrs
//! assembly-optimised library.

use blstrs::{G1Affine, G1Projective, G2Affine, G2Projective, Scalar as BlsScalar};
use ff::Field;
use group::Group;
use rand_core::RngCore;
use serde::{Deserialize, Serialize};
use core::fmt;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::error::{ActError, Result};

// ============================================================================
// Scalar
// ============================================================================

/// A scalar field element (modulo the BLS12-381 group order).
///
/// Thin wrapper around `blstrs::Scalar` that provides by-value arithmetic and
/// the serialization interface expected by the rest of the ACT protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Scalar(pub BlsScalar);

impl Scalar {
    /// The zero scalar.
    pub const ZERO: Self = Self(BlsScalar::ZERO);

    /// The scalar `1`.
    pub const ONE: Self = Self(BlsScalar::ONE);

    /// Generate a random scalar using the given RNG.
    #[inline]
    pub fn rand(rng: &mut impl RngCore) -> Self {
        Self(BlsScalar::random(rng))
    }

    /// Generate a random non-zero scalar.
    pub fn rand_nonzero(rng: &mut impl RngCore) -> Self {
        loop {
            let s = Self::rand(rng);
            if !s.is_zero() {
                return s;
            }
        }
    }

    /// Returns `true` if the scalar equals zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        bool::from(self.0.is_zero())
    }

    /// Convert to a 32-byte little-endian array (canonical form).
    #[inline]
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes_le()
    }

    /// Create from a 32-byte little-endian array.
    ///
    /// # Errors
    /// Returns `ActError::InvalidScalar` if the bytes represent a value ≥ the
    /// group order.
    pub fn from_bytes(bytes: &[u8; 32]) -> Result<Self> {
        Option::<BlsScalar>::from(BlsScalar::from_bytes_le(bytes))
            .map(Scalar)
            .ok_or(ActError::InvalidScalar)
    }

    /// Create from bytes without canonical check (for trusted inputs).
    pub(crate) fn from_bytes_unchecked(bytes: &[u8; 32]) -> Self {
        // Try canonical first; if it fails use mod reduction.
        Option::<BlsScalar>::from(BlsScalar::from_bytes_le(bytes))
            .map(Scalar)
            .unwrap_or_else(|| Self(crate::hash::scalar_from_le_bytes_mod_order(bytes)))
    }

    /// Compute the multiplicative inverse.
    ///
    /// # Panics
    /// Panics if the scalar is zero.
    pub fn inverse(&self) -> Self {
        Self(self.0.invert().expect("cannot invert zero"))
    }

    /// Multiply a G1 projective point by this scalar.
    #[inline]
    pub fn mul_g1(self, p: G1Projective) -> G1Projective {
        &p * &self.0
    }
}

// ---- Arithmetic (by-value, wrapping blstrs references internally) ----------

impl Neg for Scalar {
    type Output = Self;
    fn neg(self) -> Self { Self(-self.0) }
}

impl Add for Scalar {
    type Output = Self;
    fn add(self, rhs: Self) -> Self { Self(&self.0 + &rhs.0) }
}

impl AddAssign for Scalar {
    fn add_assign(&mut self, rhs: Self) { self.0 += &rhs.0; }
}

impl Sub for Scalar {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self { Self(&self.0 - &rhs.0) }
}

impl SubAssign for Scalar {
    fn sub_assign(&mut self, rhs: Self) { self.0 -= &rhs.0; }
}

impl Mul for Scalar {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self { Self(&self.0 * &rhs.0) }
}

impl MulAssign for Scalar {
    fn mul_assign(&mut self, rhs: Self) { self.0 *= &rhs.0; }
}

impl Mul<u32> for Scalar {
    type Output = Self;
    fn mul(self, rhs: u32) -> Self { Self(&self.0 * &BlsScalar::from(rhs as u64)) }
}

impl Mul<u64> for Scalar {
    type Output = Self;
    fn mul(self, rhs: u64) -> Self { Self(&self.0 * &BlsScalar::from(rhs)) }
}

impl Mul<Scalar> for u32 {
    type Output = Scalar;
    fn mul(self, rhs: Scalar) -> Scalar { rhs * self }
}

impl Mul<Scalar> for u64 {
    type Output = Scalar;
    fn mul(self, rhs: Scalar) -> Scalar { rhs * self }
}

// ---- From conversions -------------------------------------------------------

impl From<u64> for Scalar {
    fn from(x: u64) -> Self { Self(BlsScalar::from(x)) }
}

impl From<u32> for Scalar {
    fn from(x: u32) -> Self { Self(BlsScalar::from(x as u64)) }
}

impl From<usize> for Scalar {
    fn from(x: usize) -> Self { Self(BlsScalar::from(x as u64)) }
}

// ---- Serde for Scalar -------------------------------------------------------

impl Serialize for Scalar {
    fn serialize<S: serde::Serializer>(&self, s: S) -> core::result::Result<S::Ok, S::Error> {
        self.to_bytes().serialize(s)
    }
}

impl<'de> Deserialize<'de> for Scalar {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> core::result::Result<Self, D::Error> {
        let bytes = <[u8; 32]>::deserialize(d)?;
        Self::from_bytes(&bytes).map_err(serde::de::Error::custom)
    }
}

// ============================================================================
// G1Projective serde module
// ============================================================================

/// Serde module for `G1Projective` (compressed 48-byte array).
/// Use with `#[serde(with = "crate::types::g1_serde")]`.
pub mod g1_serde {
    use blstrs::{G1Affine, G1Projective};
    use group::Group;
    use serde::{Deserializer, Serializer, de::SeqAccess};

    pub fn serialize<S: Serializer>(p: &G1Projective, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        let bytes = G1Affine::from(p).to_compressed();
        let mut tup = s.serialize_tuple(48)?;
        for b in &bytes {
            tup.serialize_element(b)?;
        }
        tup.end()
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<G1Projective, D::Error> {
        struct V48;
        impl<'de> serde::de::Visitor<'de> for V48 {
            type Value = [u8; 48];
            fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                f.write_str("48-byte compressed G1 point")
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<[u8; 48], A::Error> {
                let mut bytes = [0u8; 48];
                for b in bytes.iter_mut() {
                    *b = seq.next_element()?.ok_or_else(|| serde::de::Error::custom("too few bytes"))?;
                }
                Ok(bytes)
            }
        }
        let bytes = d.deserialize_tuple(48, V48)?;
        Option::<G1Affine>::from(G1Affine::from_compressed(&bytes))
            .map(G1Projective::from)
            .ok_or_else(|| serde::de::Error::custom("invalid compressed G1"))
    }
}

// ============================================================================
// Compressed Group Elements
// ============================================================================

/// Compressed G1 point (48 bytes).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompressedG1(pub [u8; 48]);

impl CompressedG1 {
    pub fn from_projective(p: G1Projective) -> Self {
        Self(G1Affine::from(p).to_compressed())
    }

    pub fn from_affine(p: G1Affine) -> Self {
        Self(p.to_compressed())
    }

    /// Convert to affine, enforcing subgroup membership.
    pub fn to_affine(&self) -> Result<G1Affine> {
        Option::<G1Affine>::from(G1Affine::from_compressed(&self.0))
            .ok_or(ActError::InvalidSubgroup)
    }

    pub fn to_projective(&self) -> Result<G1Projective> {
        self.to_affine().map(G1Projective::from)
    }
}

impl fmt::Debug for CompressedG1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CompressedG1({})", hex::encode(&self.0[..4]))
    }
}

/// Compressed G2 point (96 bytes).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompressedG2(pub [u8; 96]);

impl CompressedG2 {
    pub fn from_projective(p: G2Projective) -> Self {
        Self(G2Affine::from(p).to_compressed())
    }

    pub fn from_affine(p: G2Affine) -> Self {
        Self(p.to_compressed())
    }

    pub fn to_affine(&self) -> Result<G2Affine> {
        Option::<G2Affine>::from(G2Affine::from_compressed(&self.0))
            .ok_or(ActError::InvalidSubgroup)
    }

    pub fn to_projective(&self) -> Result<G2Projective> {
        self.to_affine().map(G2Projective::from)
    }
}

impl fmt::Debug for CompressedG2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CompressedG2({})", hex::encode(&self.0[..4]))
    }
}

// ============================================================================
// Hex JSON wrappers
// ============================================================================

#[derive(Serialize, Deserialize)]
#[serde(transparent)]
pub struct HexScalar(#[serde(with = "hex::serde")] [u8; 32]);

impl From<Scalar> for HexScalar {
    fn from(s: Scalar) -> Self { Self(s.to_bytes()) }
}
impl TryFrom<HexScalar> for Scalar {
    type Error = ActError;
    fn try_from(h: HexScalar) -> Result<Self> { Scalar::from_bytes(&h.0) }
}

#[derive(Serialize, Deserialize)]
#[serde(transparent)]
pub struct HexG1(#[serde(with = "hex::serde")] [u8; 48]);

impl From<CompressedG1> for HexG1 {
    fn from(c: CompressedG1) -> Self { Self(c.0) }
}
impl TryFrom<HexG1> for CompressedG1 {
    type Error = ActError;
    fn try_from(h: HexG1) -> Result<Self> {
        let c = CompressedG1(h.0);
        let _ = c.to_affine()?;
        Ok(c)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(transparent)]
pub struct HexG2(#[serde(with = "hex::serde")] [u8; 96]);

impl From<CompressedG2> for HexG2 {
    fn from(c: CompressedG2) -> Self { Self(c.0) }
}
impl TryFrom<HexG2> for CompressedG2 {
    type Error = ActError;
    fn try_from(h: HexG2) -> Result<Self> {
        let c = CompressedG2(h.0);
        let _ = c.to_affine()?;
        Ok(c)
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
    fn scalar_roundtrip() {
        let mut rng = thread_rng();
        let s = Scalar::rand(&mut rng);
        let b = s.to_bytes();
        let s2 = Scalar::from_bytes(&b).unwrap();
        assert_eq!(s, s2);
    }

    #[test]
    fn scalar_rejects_out_of_range() {
        let bytes = [0xFFu8; 32];
        assert!(matches!(Scalar::from_bytes(&bytes), Err(ActError::InvalidScalar)));
    }

    #[test]
    fn g1_roundtrip() {
        let p = G1Projective::generator();
        let c = CompressedG1::from_projective(p);
        let p2 = c.to_projective().unwrap();
        assert_eq!(p, p2);
    }

    #[test]
    fn g2_roundtrip() {
        let p = G2Projective::generator();
        let c = CompressedG2::from_projective(p);
        let p2 = c.to_projective().unwrap();
        assert_eq!(p, p2);
    }

    #[test]
    fn scalar_arithmetic() {
        let a = Scalar::from(3u64);
        let b = Scalar::from(4u64);
        assert_eq!(a + b, Scalar::from(7u64));
        assert_eq!(a * b, Scalar::from(12u64));
        assert_eq!(b - a, Scalar::ONE);
    }
}
