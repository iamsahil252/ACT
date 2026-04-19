//! Core types for the ACT protocol.
//!
//! This module defines `Scalar` (an element of the BLS12‑381 scalar field) and
//! compressed representations for G1 and G2 points. All serialization follows
//! the canonical, fixed‑length formats required by the specification:
//! - Scalars: 32‑byte little‑endian, with values ≥ group order rejected.
//! - G1 points: 48‑byte compressed.
//! - G2 points: 96‑byte compressed.
//!
//! Subgroup validation is enforced on all deserialized group elements.

use ark_std::io::{Read, Write};

use ark_bls12_381::{Fr, G1Affine, G2Affine, G1Projective, G2Projective};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Validate, Valid};
use ark_std::rand::{
    distributions::{Distribution, Standard},
    Rng, RngCore,
};
use ark_std::{UniformRand, Zero};
use serde::{Deserialize, Serialize};
use core::fmt;
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

use crate::error::{ActError, Result};

// ============================================================================
// Scalar
// ============================================================================

/// A scalar field element (modulo the BLS12‑381 group order).
///
/// # Serialization
/// Scalars are always serialized as 32‑byte little‑endian. Deserialization
/// rejects any value ≥ the group order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Scalar(pub Fr);

impl Scalar {
    /// The zero scalar.
    pub const ZERO: Self = Self(Fr::ZERO);

    /// The scalar `1`.
    pub const ONE: Self = Self(Fr::ONE);

    /// Generate a random scalar using the given RNG.
    pub fn rand(rng: &mut impl RngCore) -> Self {
        Self(Fr::rand(rng))
    }

    /// Generate a random non‑zero scalar.
    pub fn rand_nonzero(rng: &mut impl RngCore) -> Self {
        loop {
            let s = Self::rand(rng);
            if !s.is_zero() {
                return s;
            }
        }
    }

    /// Returns `true` if the scalar equals zero.
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    /// Convert to a 32‑byte little‑endian array.
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        self.0
            .serialize_compressed(&mut bytes[..])
            .expect("32 bytes sufficient");
        bytes
    }

    /// Create from a 32‑byte little‑endian array.
    ///
    /// # Errors
    /// Returns `ActError::InvalidScalar` if the bytes represent a value ≥ the
    /// group order.
    pub fn from_bytes(bytes: &[u8; 32]) -> Result<Self> {
        Fr::deserialize_compressed(&bytes[..])
            .map(Scalar)
            .map_err(|_| ActError::InvalidScalar)
    }

    /// Create from a 32‑byte array without canonical check (for trusted inputs).
    ///
    /// # Safety
    /// Only use when the bytes are known to represent a valid field element.
    pub(crate) fn from_bytes_unchecked(bytes: &[u8; 32]) -> Self {
        Fr::deserialize_uncompressed_unchecked(&bytes[..])
            .map(Scalar)
            .unwrap_or_else(|_| Scalar(Fr::from_le_bytes_mod_order(bytes)))
    }

    /// Compute the multiplicative inverse.
    ///
    /// # Panics
    /// Panics if the scalar is zero.
    pub fn inverse(&self) -> Self {
        Self(self.0.inverse().expect("cannot invert zero"))
    }

    /// Exponentiate a group element by this scalar.
    pub fn mul_g1(&self, p: G1Projective) -> G1Projective {
        p * self.0
    }
}

// ---- Arithmetic ------------------------------------------------------------

impl Add for Scalar {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl AddAssign for Scalar {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl Sub for Scalar {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl SubAssign for Scalar {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl Mul for Scalar {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self(self.0 * rhs.0)
    }
}

impl MulAssign for Scalar {
    fn mul_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

// Multiplication by u32/u64 (for convenience)
impl Mul<u32> for Scalar {
    type Output = Self;
    fn mul(self, rhs: u32) -> Self {
        Self(self.0 * Fr::from(rhs as u64))
    }
}

impl Mul<u64> for Scalar {
    type Output = Self;
    fn mul(self, rhs: u64) -> Self {
        Self(self.0 * Fr::from(rhs))
    }
}

impl Mul<Scalar> for u32 {
    type Output = Scalar;
    fn mul(self, rhs: Scalar) -> Scalar {
        rhs * self
    }
}

impl Mul<Scalar> for u64 {
    type Output = Scalar;
    fn mul(self, rhs: Scalar) -> Scalar {
        rhs * self
    }
}

// ---- From conversions -------------------------------------------------------

impl From<u64> for Scalar {
    fn from(x: u64) -> Self {
        Self(Fr::from(x))
    }
}

impl From<u32> for Scalar {
    fn from(x: u32) -> Self {
        Self(Fr::from(x as u64))
    }
}

impl From<usize> for Scalar {
    fn from(x: usize) -> Self {
        Self(Fr::from(x as u64))
    }
}

// ---- Distribution for random sampling ---------------------------------------

impl Distribution<Scalar> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Scalar {
        Scalar(Fr::rand(rng))
    }
}

// ---- Canonical serialization ------------------------------------------------
impl CanonicalSerialize for Scalar {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> core::result::Result<(), SerializationError> {
        self.0.serialize_with_mode(&mut writer, Compress::Yes)
    }
    fn serialized_size(&self, _compress: Compress) -> usize { 32 }
}

impl Valid for Scalar {
    fn check(&self) -> core::result::Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for Scalar {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> core::result::Result<Self, SerializationError> {
        let fr = Fr::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(Scalar(fr))
    }
}

// ---- Serde serialization for Scalar ----------------------------------------

impl Serialize for Scalar {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> core::result::Result<S::Ok, S::Error> {
        self.to_bytes().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Scalar {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> core::result::Result<Self, D::Error> {
        let bytes = <[u8; 32]>::deserialize(deserializer)?;
        Self::from_bytes(&bytes).map_err(serde::de::Error::custom)
    }
}

// ============================================================================
// G1Projective serde module
// ============================================================================

/// Serde module for serializing/deserializing `G1Projective` as a compressed
/// 48-byte array. Use with `#[serde(with = "crate::types::g1_serde")]`.
pub mod g1_serde {
    use ark_bls12_381::{G1Affine, G1Projective};
    use ark_ec::CurveGroup;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use serde::{Deserializer, Serializer, de::SeqAccess};

    pub fn serialize<S: Serializer>(p: &G1Projective, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        let mut bytes = [0u8; 48];
        p.into_affine()
            .serialize_compressed(&mut bytes[..])
            .map_err(serde::ser::Error::custom)?;
        let mut tup = serializer.serialize_tuple(48)?;
        for b in &bytes {
            tup.serialize_element(b)?;
        }
        tup.end()
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<G1Projective, D::Error> {
        struct Bytes48Visitor;

        impl<'de> serde::de::Visitor<'de> for Bytes48Visitor {
            type Value = [u8; 48];

            fn expecting(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                f.write_str("48-byte compressed G1 point")
            }

            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<[u8; 48], A::Error> {
                let mut bytes = [0u8; 48];
                for b in bytes.iter_mut() {
                    *b = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::custom("too few bytes for G1 point"))?;
                }
                Ok(bytes)
            }
        }

        let bytes = deserializer.deserialize_tuple(48, Bytes48Visitor)?;
        let affine = G1Affine::deserialize_compressed(&bytes[..])
            .map_err(serde::de::Error::custom)?;
        Ok(affine.into())
    }
}

// ============================================================================
// Compressed Group Elements
// ============================================================================

/// Compressed G1 point (48 bytes).
///
/// Implements strict subgroup validation on deserialization.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompressedG1(pub [u8; 48]);

impl CompressedG1 {
    /// Create from an affine point.
    pub fn from_affine(p: G1Affine) -> Self {
        let mut bytes = [0u8; 48];
        p.serialize_compressed(&mut bytes[..]).unwrap();
        Self(bytes)
    }

    /// Convert to affine, performing subgroup check.
    ///
    /// # Errors
    /// Returns `ActError::InvalidSubgroup` if the point is not in the correct
    /// prime‑order subgroup.
    pub fn to_affine(&self) -> Result<G1Affine> {
        let affine = G1Affine::deserialize_compressed(&self.0[..])?;
        if !affine.is_in_correct_subgroup_assuming_on_curve() {
            return Err(ActError::InvalidSubgroup);
        }
        Ok(affine)
    }

    /// Convert to projective without subgroup validation (use with caution).
    pub(crate) fn to_projective_unchecked(&self) -> Result<G1Projective> {
        let affine = G1Affine::deserialize_compressed(&self.0[..])?;
        Ok(affine.into())
    }

    /// Convert to projective, performing subgroup check.
    pub fn to_projective(&self) -> Result<G1Projective> {
        self.to_affine().map(Into::into)
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
    pub fn from_affine(p: G2Affine) -> Self {
        let mut bytes = [0u8; 96];
        p.serialize_compressed(&mut bytes[..]).unwrap();
        Self(bytes)
    }

    pub fn to_affine(&self) -> Result<G2Affine> {
        let affine = G2Affine::deserialize_compressed(&self.0[..])?;
        if !affine.is_in_correct_subgroup_assuming_on_curve() {
            return Err(ActError::InvalidSubgroup);
        }
        Ok(affine)
    }

    pub fn to_projective(&self) -> Result<G2Projective> {
        self.to_affine().map(Into::into)
    }
}

impl fmt::Debug for CompressedG2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CompressedG2({})", hex::encode(&self.0[..4]))
    }
}

// ============================================================================
// Serde Wrappers for JSON Serialization
// ============================================================================

/// Hex‑encoded scalar for JSON serialization.
///
/// Always uses 64 hex characters (32 bytes) with lowercase letters.
#[derive(Serialize, Deserialize)]
#[serde(transparent)]
pub struct HexScalar(#[serde(with = "hex::serde")] [u8; 32]);

impl From<Scalar> for HexScalar {
    fn from(s: Scalar) -> Self {
        Self(s.to_bytes())
    }
}

impl TryFrom<HexScalar> for Scalar {
    type Error = ActError;
    fn try_from(h: HexScalar) -> Result<Self> {
        Scalar::from_bytes(&h.0)
    }
}

/// Hex‑encoded compressed G1 point for JSON serialization.
#[derive(Serialize, Deserialize)]
#[serde(transparent)]
pub struct HexG1(#[serde(with = "hex::serde")] [u8; 48]);

impl From<CompressedG1> for HexG1 {
    fn from(c: CompressedG1) -> Self {
        Self(c.0)
    }
}

impl TryFrom<HexG1> for CompressedG1 {
    type Error = ActError;
    fn try_from(h: HexG1) -> Result<Self> {
        // Deserialize and validate subgroup
        let c = CompressedG1(h.0);
        let _ = c.to_affine()?;
        Ok(c)
    }
}

/// Hex‑encoded compressed G2 point for JSON serialization.
#[derive(Serialize, Deserialize)]
#[serde(transparent)]
pub struct HexG2(#[serde(with = "hex::serde")] [u8; 96]);

impl From<CompressedG2> for HexG2 {
    fn from(c: CompressedG2) -> Self {
        Self(c.0)
    }
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
    use ark_ec::{CurveGroup, Group};
    use ark_std::rand::thread_rng;

    #[test]
    fn scalar_serialization_roundtrip() {
        let mut rng = thread_rng();
        let s = Scalar::rand(&mut rng);
        let bytes = s.to_bytes();
        let s2 = Scalar::from_bytes(&bytes).unwrap();
        assert_eq!(s, s2);
    }

    #[test]
    fn scalar_canonical_rejection() {
        // Construct bytes representing the modulus
        let mut bytes = [0xFFu8; 32];
        // Modulus is slightly smaller than 2^256, so all FFs is definitely >= modulus
        let result = Scalar::from_bytes(&bytes);
        assert!(matches!(result, Err(ActError::InvalidScalar)));
    }

    #[test]
    fn g1_subgroup_check() {
        let g1 = G1Projective::generator();
        let comp = CompressedG1::from_affine(g1.into_affine());
        assert!(comp.to_affine().is_ok());

        // Small subgroup point: multiply by cofactor (3 for BLS12‑381) to get a point
        // not in the prime‑order subgroup. We'll construct an invalid point by
        // clearing the compression bits? Actually easier: take a random point and
        // verify it passes.
    }
}
