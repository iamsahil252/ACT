//! Dual-curve Sigma protocol bridge: `BatchedEqualityProof`.
//!
//! Proves that the balance `m` hidden inside a BLS12-381 Pedersen commitment
//! `C_BLS = m·h4 + r_bls·h0` is identical to the `m` hidden inside a
//! Curve25519 Ristretto Pedersen commitment `C_25519 = m·G + r_25519·H`.
//!
//! The proof executes a cross-curve Sigma protocol over the integers (ℤ) using
//! arbitrary-precision arithmetic so that the scalar response is valid in both
//! finite fields simultaneously.  A native Dalek Bulletproof running on
//! Curve25519 then proves `m ∈ [0, 2³²−1]`, which—by the equality bridge—
//! transitively enforces the range bound on the BLS12-381 side.
//!
//! # ZK Parameter Sizing
//!
//! * `m` is at most 32 bits.
//! * The Fiat–Shamir challenge `c` is truncated to **128 bits** (16 bytes).
//! * The integer blinding factor `u_m` is drawn from a **240-bit** uniform space
//!   (30 random bytes).
//! * The integer response `z_e = u_m + c·m` is therefore at most 241 bits.
//! * Both curve orders satisfy `q₂₅₅₁₉ ≈ 2²⁵² > 2²⁴¹` and
//!   `q_BLS ≈ 2²⁵⁵ > q₂₅₅₁₉`, so no modular wrap ever occurs in `z_e`.
//!
//! # Generator Policy (Section 9.2 compatibility)
//!
//! Because the bridge evaluates equality over ℤ rather than a shared finite
//! field, the two sides are free to use completely independent generators.
//! The BLS12-381 side uses the pure BBS+ generators `h4` and `h0`.
//! The Curve25519 side uses Dalek's default `PedersenGens` (hardcoded Ristretto
//! bases), which are provably orthogonal to the BLS12-381 generators.
//! The Section 9.2 override requirement is therefore automatically satisfied.

extern crate alloc;
use alloc::vec::Vec;

use ark_bls12_381::{Fr, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::{UniformRand, Zero};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};

use bulletproofs::{BulletproofGens, PedersenGens, RangeProof as DalekRangeProof};
use curve25519_dalek_ng::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek_ng::scalar::Scalar as DalekScalar;
use merlin::Transcript;

use crate::error::{ActError, Result};

// ============================================================================
// Constant: Curve25519 / ristretto255 group order (little-endian)
//
// l = 2²⁵² + 27742317777372353535851937790883648493
//   = 0x1000000000000000000000000000000014DEF9DEA2F79CD65812631A5CF5D3ED
// ============================================================================

const Q_25519_LE: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

// ============================================================================
// Proof Structure
// ============================================================================

/// A dual-curve Sigma protocol proof of equality between a BLS12-381 and a
/// Curve25519 Pedersen commitment, together with a Dalek range proof showing
/// the committed value lies in `[0, 2³²−1]`.
#[derive(Clone, Debug)]
pub struct BatchedEqualityProof {
    /// BLS12-381 Schnorr commitment `R_BLS = u_m·h4 + u_r·h0` (compressed, 48 B).
    pub r_bls_bytes: [u8; 48],
    /// Curve25519 Schnorr commitment `R_25519 = u_m·G + u_r·H` (compressed, 32 B).
    pub r_25519_bytes: [u8; 32],
    /// Curve25519 Pedersen commitment `C_25519 = m·G + r_25519·H` (compressed, 32 B).
    pub c_25519_bytes: [u8; 32],
    /// Integer response `z_e = u_m + c·m` in ℤ, little-endian 32-byte encoding.
    /// Always < 2²⁴¹; top 1–2 bytes are always zero.
    pub z_e_bytes: [u8; 32],
    /// BLS12-381 randomness response `z_r_bls = u_r + c·r_bls (mod q_BLS)`,
    /// little-endian 32-byte encoding.
    pub z_r_bls_bytes: [u8; 32],
    /// Curve25519 randomness response `z_r_25519 = u_r + c·r_25519 (mod q₂₅₅₁₉)`,
    /// little-endian 32-byte encoding.
    pub z_r_25519_bytes: [u8; 32],
    /// Serialized Dalek `RangeProof` bytes proving `m ∈ [0, 2³²−1]` over `C_25519`.
    pub range_proof_bytes: Vec<u8>,
}

impl BatchedEqualityProof {
    /// Canonical byte serialization for use in Fiat–Shamir transcripts.
    ///
    /// Format: `r_bls(48) ∥ r_25519(32) ∥ c_25519(32) ∥ z_e(32) ∥ z_r_bls(32) ∥
    ///          z_r_25519(32) ∥ range_len(4 LE) ∥ range_proof(variable)`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(
            48 + 32 + 32 + 32 + 32 + 32 + 4 + self.range_proof_bytes.len(),
        );
        buf.extend_from_slice(&self.r_bls_bytes);
        buf.extend_from_slice(&self.r_25519_bytes);
        buf.extend_from_slice(&self.c_25519_bytes);
        buf.extend_from_slice(&self.z_e_bytes);
        buf.extend_from_slice(&self.z_r_bls_bytes);
        buf.extend_from_slice(&self.z_r_25519_bytes);
        buf.extend_from_slice(&(self.range_proof_bytes.len() as u32).to_le_bytes());
        buf.extend_from_slice(&self.range_proof_bytes);
        buf
    }
}

// ============================================================================
// Helper: Dalek generators
// ============================================================================

/// Return Dalek's default Pedersen generators (Ristretto base-point B and a
/// hash-derived blinding base B_blinding).  These are completely independent of
/// the BLS12-381 BBS+ generators, so no collision is possible.
fn dalek_pc_gens() -> PedersenGens {
    PedersenGens::default()
}

/// Return Dalek's Bulletproof generators for a 32-bit range proof.
/// 64 generators are sufficient for a 32-multiplier R1CS range proof.
fn dalek_bp_gens() -> BulletproofGens {
    BulletproofGens::new(64, 1)
}

// ============================================================================
// Helper: uniform dalek Scalar from RNG
// ============================================================================

/// Sample a uniform Dalek scalar by hashing 64 random bytes (wide reduction).
fn rand_dalek_scalar(rng: &mut (impl CryptoRng + RngCore)) -> DalekScalar {
    let mut wide = [0u8; 64];
    rng.fill_bytes(&mut wide);
    DalekScalar::from_bytes_mod_order_wide(&wide)
}

// ============================================================================
// Helper: challenge computation (128-bit output)
// ============================================================================

/// Derive the 128-bit cross-curve challenge `c` by hashing all public
/// commitments and context.
///
/// This is truncated deliberately: `m ≤ 2³²` and `c < 2¹²⁸` ensures
/// `c·m < 2¹⁶⁰`, and adding the 240-bit blinder `u_m` keeps `z_e < 2²⁴¹`.
/// Both curve orders are > 2²⁵², so no modular wrap can occur.
fn compute_beq_challenge(
    context: &[u8],
    c_bls_bytes: &[u8],      // compressed BLS12-381 C_BLS (48 B)
    c_25519_bytes: &[u8; 32],
    r_bls_bytes: &[u8],      // compressed BLS12-381 R_BLS (48 B)
    r_25519_bytes: &[u8; 32],
    range_proof_bytes: &[u8],
) -> [u8; 16] {
    let mut hasher = Sha256::new();
    hasher.update(b"ACT:BEQ:Challenge");
    hasher.update(context);
    hasher.update(c_bls_bytes);
    hasher.update(c_25519_bytes);
    hasher.update(r_bls_bytes);
    hasher.update(r_25519_bytes);
    hasher.update(range_proof_bytes);
    let digest = hasher.finalize();
    let mut c128 = [0u8; 16];
    c128.copy_from_slice(&digest[..16]);
    c128
}

/// Expand a 16-byte challenge to a 32-byte little-endian array (zero-padded).
#[inline]
fn c128_to_bytes32(c128: &[u8; 16]) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[..16].copy_from_slice(c128);
    b
}

// ============================================================================
// Prover
// ============================================================================

/// Generate a `BatchedEqualityProof` that `m` inside
/// `C_BLS = m·h4 + r_bls·h0` (BLS12-381) equals the `m` inside a freshly
/// generated Curve25519 commitment, together with a Dalek range proof for
/// `m ∈ [0, 2³²−1]`.
///
/// # Returns
/// `(proof, c_bls)` where `c_bls` is the BLS12-381 commitment computed from
/// the given `m` and `r_bls` (it is returned for convenience; callers that
/// already hold `c_bp` should verify equality).
///
/// The Curve25519 commitment `C_25519` is embedded inside the returned proof
/// as `proof.c_25519_bytes`.
///
/// # Parameters
/// * `m`       – 32-bit secret balance to commit to and range-prove.
/// * `r_bls`   – BLS12-381 blinding scalar for `C_BLS`.
/// * `h4`      – BBS+ generator used as the value base in `C_BLS`.
/// * `h0`      – BBS+ generator used as the blinding base in `C_BLS`.
/// * `context` – Caller-supplied byte string bound into the challenge hash
///               (should include `H_ctx`, BBS+ commitments, nonce, etc.).
#[allow(clippy::too_many_arguments)]
pub fn prove_batched_equality(
    rng: &mut (impl CryptoRng + RngCore),
    m: u32,
    r_bls: Fr,
    h4: G1Projective,
    h0: G1Projective,
    context: &[u8],
) -> Result<(BatchedEqualityProof, G1Projective)> {
    // ── Step 1: Curve25519 commitment + Dalek range proof ────────────────────
    let r_25519 = rand_dalek_scalar(rng);
    let pc_gens = dalek_pc_gens();
    let bp_gens = dalek_bp_gens();

    // C_25519 = m·G + r_25519·H
    let m_dalek = DalekScalar::from(m as u64);
    let c_25519_point = pc_gens.commit(m_dalek, r_25519);
    let c_25519_compressed = c_25519_point.compress();
    let c_25519_bytes: [u8; 32] = c_25519_compressed.to_bytes();

    // Dalek range proof over C_25519, binding context in transcript.
    let mut range_transcript = Transcript::new(b"ACT:BEQ:Range");
    range_transcript.append_message(b"ctx", context);
    let (dalek_proof, _committed) = DalekRangeProof::prove_single(
        &bp_gens,
        &pc_gens,
        &mut range_transcript,
        m as u64,
        &r_25519,
        32, // 32-bit range proof
    )
    .map_err(|e| ActError::ProtocolError(alloc::format!("Dalek range prove failed: {:?}", e)))?;
    let range_proof_bytes = dalek_proof.to_bytes();

    // ── Step 2: Integer blinding factor u_m (240 bits = 30 bytes) ────────────
    let mut u_m_le30 = [0u8; 30];
    rng.fill_bytes(&mut u_m_le30);
    let u_m = BigUint::from_bytes_le(&u_m_le30);

    // Represent u_m as a 32-byte LE array (fits in 32 bytes since 240 < 256).
    let mut u_m_32 = [0u8; 32];
    u_m_32[..30].copy_from_slice(&u_m_le30);

    // Convert u_m into BLS12-381 Fr (no reduction: u_m < 2²⁴⁰ < q_BLS).
    let u_m_bls = Fr::from_le_bytes_mod_order(&u_m_32);

    // Convert u_m into a Dalek Scalar (no reduction: u_m < 2²⁴⁰ < q₂₅₅₁₉).
    let u_m_25519 = DalekScalar::from_bytes_mod_order(u_m_32);

    // ── Step 3: Schnorr blinders for randomness terms ────────────────────────
    let u_r_bls = Fr::rand(rng);
    let u_r_25519 = rand_dalek_scalar(rng);

    // ── Step 4: Schnorr commitments ───────────────────────────────────────────
    // R_BLS = u_m·h4 + u_r_bls·h0
    let r_bls_point = h4 * u_m_bls + h0 * u_r_bls;
    let mut r_bls_bytes = [0u8; 48];
    r_bls_point
        .into_affine()
        .serialize_compressed(&mut r_bls_bytes[..])
        .map_err(ActError::SerializationError)?;

    // R_25519 = u_m·G + u_r_25519·H  =  pc_gens.commit(u_m_25519, u_r_25519)
    let r_25519_point = pc_gens.commit(u_m_25519, u_r_25519);
    let r_25519_bytes: [u8; 32] = r_25519_point.compress().to_bytes();

    // ── Step 5: BLS12-381 commitment C_BLS = m·h4 + r_bls·h0 ────────────────
    let c_bls = h4 * Fr::from(m as u64) + h0 * r_bls;
    let mut c_bls_bytes_48 = [0u8; 48];
    c_bls
        .into_affine()
        .serialize_compressed(&mut c_bls_bytes_48[..])
        .map_err(ActError::SerializationError)?;

    // ── Step 6: 128-bit Fiat–Shamir challenge ────────────────────────────────
    let c128 = compute_beq_challenge(
        context,
        &c_bls_bytes_48,
        &c_25519_bytes,
        &r_bls_bytes,
        &r_25519_bytes,
        &range_proof_bytes,
    );
    let c_32 = c128_to_bytes32(&c128);
    let c_big = BigUint::from_bytes_le(&c128);
    let c_fr = Fr::from_le_bytes_mod_order(&c_32);
    let c_dalek = DalekScalar::from_bytes_mod_order(c_32);

    // ── Step 7: Integer response z_e = u_m + c·m  (over ℤ, no modulo) ────────
    let z_e = u_m + &c_big * BigUint::from(m as u64);
    // z_e < 2²⁴¹; fits in ≤ 31 bytes.
    let z_e_le = z_e.to_bytes_le();
    debug_assert!(z_e_le.len() <= 31, "z_e unexpectedly exceeded 31 bytes");
    let mut z_e_bytes = [0u8; 32];
    z_e_bytes[..z_e_le.len()].copy_from_slice(&z_e_le);

    // ── Step 8: BLS12-381 randomness response ────────────────────────────────
    let z_r_bls = u_r_bls + c_fr * r_bls;
    let mut z_r_bls_bytes = [0u8; 32];
    z_r_bls
        .serialize_compressed(&mut z_r_bls_bytes[..])
        .map_err(ActError::SerializationError)?;

    // ── Step 9: Curve25519 randomness response ───────────────────────────────
    let z_r_25519 = u_r_25519 + c_dalek * r_25519;
    let z_r_25519_bytes: [u8; 32] = z_r_25519.to_bytes();

    // ── Assemble proof ────────────────────────────────────────────────────────
    let proof = BatchedEqualityProof {
        r_bls_bytes,
        r_25519_bytes,
        c_25519_bytes,
        z_e_bytes,
        z_r_bls_bytes,
        z_r_25519_bytes,
        range_proof_bytes,
    };

    Ok((proof, c_bls))
}

// ============================================================================
// Verifier
// ============================================================================

/// Verify a [`BatchedEqualityProof`] against the BLS12-381 commitment `c_bls`.
///
/// The proof is accepted if and only if:
///
/// 1. `z_e < q₂₅₅₁₉` (bounds check, prevents modular wrap attacks).
/// 2. BLS12-381 Schnorr equation holds:
///    `z_m_bls·h4 + z_r_bls·h0 = R_BLS + c·C_BLS`.
/// 3. Curve25519 Schnorr equation holds:
///    `z_m_25519·G + z_r_25519·H = R_25519 + c·C_25519`.
/// 4. Dalek range proof verifies `m ∈ [0, 2³²−1]` against `C_25519`.
///
/// # Parameters
/// * `c_bls`   – The BLS12-381 commitment from the spend proof (`C_BP`).
/// * `h4`, `h0` – BBS+ generators matching those used during proving.
/// * `context` – Same byte string passed to [`prove_batched_equality`].
pub fn verify_batched_equality(
    proof: &BatchedEqualityProof,
    c_bls: G1Projective,
    h4: G1Projective,
    h0: G1Projective,
    context: &[u8],
) -> Result<()> {
    // ── 1. Bounds check: z_e < q₂₅₅₁₉ ──────────────────────────────────────
    // The honest prover always produces z_e < 2²⁴¹ ≪ q₂₅₅₁₉.  We compare
    // BigUint representations for a precise check.
    let q_25519 = BigUint::from_bytes_le(&Q_25519_LE);
    let z_e = BigUint::from_bytes_le(&proof.z_e_bytes);
    if z_e >= q_25519 {
        return Err(ActError::VerificationFailed(
            "BatchedEqualityProof: z_e >= q_25519 (modular wrap attack)".into(),
        ));
    }

    // ── 2. Project z_e into the respective scalar fields ─────────────────────
    // Since z_e < q₂₅₅₁₉ < q_BLS, both reductions are no-ops; the integer
    // value is preserved exactly in both scalars.
    let z_m_bls = Fr::from_le_bytes_mod_order(&proof.z_e_bytes);
    let z_m_25519 = DalekScalar::from_bytes_mod_order(proof.z_e_bytes);

    // ── 3. Deserialize proof elements ────────────────────────────────────────
    let r_bls_affine = ark_bls12_381::G1Affine::deserialize_compressed(&proof.r_bls_bytes[..])
        .map_err(|_| {
            ActError::VerificationFailed("BatchedEqualityProof: invalid R_BLS bytes".into())
        })?;
    let r_bls_point: G1Projective = r_bls_affine.into();

    let r_25519_compressed = CompressedRistretto(proof.r_25519_bytes);
    let r_25519_point: RistrettoPoint = r_25519_compressed.decompress().ok_or_else(|| {
        ActError::VerificationFailed("BatchedEqualityProof: invalid R_25519 point".into())
    })?;

    let c_25519_compressed = CompressedRistretto(proof.c_25519_bytes);
    let c_25519_point: RistrettoPoint = c_25519_compressed.decompress().ok_or_else(|| {
        ActError::VerificationFailed("BatchedEqualityProof: invalid C_25519 point".into())
    })?;

    let z_r_bls = Fr::from_le_bytes_mod_order(&proof.z_r_bls_bytes);
    let z_r_25519 = DalekScalar::from_bytes_mod_order(proof.z_r_25519_bytes);

    // ── 4. Recompute the 128-bit challenge ───────────────────────────────────
    let mut c_bls_bytes_48 = [0u8; 48];
    c_bls
        .into_affine()
        .serialize_compressed(&mut c_bls_bytes_48[..])
        .map_err(ActError::SerializationError)?;

    let c128 = compute_beq_challenge(
        context,
        &c_bls_bytes_48,
        &proof.c_25519_bytes,
        &proof.r_bls_bytes,
        &proof.r_25519_bytes,
        &proof.range_proof_bytes,
    );
    let c_32 = c128_to_bytes32(&c128);
    let c_fr = Fr::from_le_bytes_mod_order(&c_32);
    let c_dalek = DalekScalar::from_bytes_mod_order(c_32);

    // ── 5. BLS12-381 Schnorr check ────────────────────────────────────────────
    // LHS: z_m_bls·h4 + z_r_bls·h0
    let lhs_bls = h4 * z_m_bls + h0 * z_r_bls;
    // RHS: R_BLS + c·C_BLS
    let rhs_bls = r_bls_point + c_bls * c_fr;
    if lhs_bls != rhs_bls {
        return Err(ActError::VerificationFailed(
            "BatchedEqualityProof: BLS12-381 Schnorr check failed".into(),
        ));
    }

    // ── 6. Curve25519 Schnorr check ──────────────────────────────────────────
    let pc_gens = dalek_pc_gens();
    // LHS: z_m_25519·G + z_r_25519·H  =  pc_gens.commit(z_m_25519, z_r_25519)
    let lhs_25519 = pc_gens.commit(z_m_25519, z_r_25519);
    // RHS: R_25519 + c·C_25519
    let rhs_25519 = r_25519_point + c_25519_point * c_dalek;
    if lhs_25519 != rhs_25519 {
        return Err(ActError::VerificationFailed(
            "BatchedEqualityProof: Curve25519 Schnorr check failed".into(),
        ));
    }

    // ── 7. Dalek range proof verification ────────────────────────────────────
    let bp_gens = dalek_bp_gens();
    let dalek_proof = DalekRangeProof::from_bytes(&proof.range_proof_bytes).map_err(|e| {
        ActError::VerificationFailed(alloc::format!("Invalid Dalek range proof bytes: {:?}", e))
    })?;
    let mut range_transcript = Transcript::new(b"ACT:BEQ:Range");
    range_transcript.append_message(b"ctx", context);
    dalek_proof
        .verify_single(
            &bp_gens,
            &pc_gens,
            &mut range_transcript,
            &c_25519_compressed,
            32,
        )
        .map_err(|e| {
            ActError::VerificationFailed(alloc::format!(
                "BatchedEqualityProof: Dalek range proof failed: {:?}",
                e
            ))
        })?;

    Ok(())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::setup::Generators;
    use ark_std::rand::thread_rng;

    #[test]
    fn batched_equality_proof_roundtrip() {
        let mut rng = thread_rng();
        let gens = Generators::new();
        let h4 = gens.h[4];
        let h0 = gens.h[0];

        let m = 42u32;
        let r_bls = Fr::rand(&mut rng);
        let context = b"ACT:Test:BEQ context data";

        let (proof, c_bls) = prove_batched_equality(&mut rng, m, r_bls, h4, h0, context).unwrap();

        verify_batched_equality(&proof, c_bls, h4, h0, context).unwrap();
    }

    #[test]
    fn batched_equality_proof_zero_balance() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let m = 0u32;
        let r_bls = Fr::rand(&mut rng);
        let context = b"ACT:Test:zero balance";

        let (proof, c_bls) =
            prove_batched_equality(&mut rng, m, r_bls, gens.h[4], gens.h[0], context).unwrap();
        verify_batched_equality(&proof, c_bls, gens.h[4], gens.h[0], context).unwrap();
    }

    #[test]
    fn batched_equality_proof_max_balance() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let m = u32::MAX;
        let r_bls = Fr::rand(&mut rng);
        let context = b"ACT:Test:max balance";

        let (proof, c_bls) =
            prove_batched_equality(&mut rng, m, r_bls, gens.h[4], gens.h[0], context).unwrap();
        verify_batched_equality(&proof, c_bls, gens.h[4], gens.h[0], context).unwrap();
    }

    #[test]
    fn wrong_c_bls_fails() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let m = 10u32;
        let r_bls = Fr::rand(&mut rng);
        let context = b"ACT:Test:wrong cbls";

        let (proof, _c_bls) =
            prove_batched_equality(&mut rng, m, r_bls, gens.h[4], gens.h[0], context).unwrap();

        // Present a commitment to a different value (m+1).
        let wrong_r = Fr::rand(&mut rng);
        let wrong_c_bls = gens.h[4] * Fr::from((m + 1) as u64) + gens.h[0] * wrong_r;
        let result = verify_batched_equality(&proof, wrong_c_bls, gens.h[4], gens.h[0], context);
        assert!(result.is_err(), "should fail with wrong C_BLS");
    }

    #[test]
    fn wrong_context_fails() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let m = 20u32;
        let r_bls = Fr::rand(&mut rng);

        let (proof, c_bls) =
            prove_batched_equality(&mut rng, m, r_bls, gens.h[4], gens.h[0], b"context-A")
                .unwrap();

        let result = verify_batched_equality(&proof, c_bls, gens.h[4], gens.h[0], b"context-B");
        assert!(result.is_err(), "should fail with wrong context");
    }

    #[test]
    fn z_e_fits_in_31_bytes() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        // Worst case: m = u32::MAX and a large challenge.
        let m = u32::MAX;
        let r_bls = Fr::rand(&mut rng);
        let context = b"ACT:Test:z_e size";

        let (proof, _) =
            prove_batched_equality(&mut rng, m, r_bls, gens.h[4], gens.h[0], context).unwrap();

        // The 32nd byte (index 31) must be zero for all honest proofs.
        assert_eq!(
            proof.z_e_bytes[31], 0,
            "z_e must fit in 31 bytes for m = u32::MAX"
        );
    }

    #[test]
    fn to_bytes_round_trips_length() {
        let mut rng = thread_rng();
        let gens = Generators::new();
        let r_bls = Fr::rand(&mut rng);
        let (proof, _) =
            prove_batched_equality(&mut rng, 100, r_bls, gens.h[4], gens.h[0], b"t").unwrap();
        let bytes = proof.to_bytes();
        // Minimum: 48+32+32+32+32+32+4 = 212 bytes header + range proof.
        assert!(bytes.len() >= 212);
    }
}
