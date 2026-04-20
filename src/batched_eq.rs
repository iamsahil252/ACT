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
//! * The integer blinding factor `u_m` is drawn from a **240-bit** uniform space.
//! * The integer response `z_e = u_m + c·m` is therefore at most 241 bits.
//! * Both curve orders satisfy `q₂₅₅₁₉ ≈ 2²⁵² > 2²⁴¹` and
//!   `q_BLS ≈ 2²⁵⁵ > q₂₅₅₁₉`, so no modular wrap ever occurs in `z_e`.

extern crate alloc;
use alloc::vec::Vec;

use blstrs::{G1Affine, G1Projective, Scalar as BlsScalar};
use ff::Field as _;
use group::Group as _;
use rand_core::{CryptoRng, RngCore};
use sha2::{Digest, Sha256};
use std::io::Write as _;

use bulletproofs::{BulletproofGens, PedersenGens, RangeProof as DalekRangeProof};
use curve25519_dalek_ng::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek_ng::scalar::Scalar as DalekScalar;
use merlin::Transcript;

use crate::error::{ActError, Result};
use crate::hash::{scalar_from_le_bytes_mod_order, write_g1_affine};

// ============================================================================
// Curve25519 order constant (for the modular-wrap guard)
// ============================================================================

const Q_25519_LIMBS: [u64; 4] = {
    let b = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
        0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
    ];
    [
        u64::from_le_bytes([b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7]]),
        u64::from_le_bytes([b[8],b[9],b[10],b[11],b[12],b[13],b[14],b[15]]),
        u64::from_le_bytes([b[16],b[17],b[18],b[19],b[20],b[21],b[22],b[23]]),
        u64::from_le_bytes([b[24],b[25],b[26],b[27],b[28],b[29],b[30],b[31]]),
    ]
};

// ============================================================================
// Inline 256-bit integer arithmetic (stack-allocated, no heap)
// ============================================================================

#[inline]
fn u256_from_le_bytes(bytes: &[u8; 32]) -> [u64; 4] {
    let mut limbs = [0u64; 4];
    for (i, chunk) in bytes.chunks_exact(8).enumerate() {
        limbs[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    limbs
}

#[inline]
fn u256_to_le_bytes(limbs: &[u64; 4]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (i, &l) in limbs.iter().enumerate() {
        bytes[i * 8..(i + 1) * 8].copy_from_slice(&l.to_le_bytes());
    }
    bytes
}

#[inline]
fn u256_lt(a: &[u64; 4], b: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] { return a[i] < b[i]; }
    }
    false
}

#[inline]
fn u256_mul_u64(a: &[u64; 4], b: u64) -> [u64; 4] {
    let mut result = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let prod = a[i] as u128 * b as u128 + carry;
        result[i] = prod as u64;
        carry = prod >> 64;
    }
    debug_assert_eq!(carry, 0, "u256_mul_u64: overflow");
    result
}

#[inline]
fn u256_add(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut result = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let sum = a[i] as u128 + b[i] as u128 + carry;
        result[i] = sum as u64;
        carry = sum >> 64;
    }
    debug_assert_eq!(carry, 0, "u256_add: overflow");
    result
}

// ============================================================================
// Proof Structure
// ============================================================================

/// A dual-curve Sigma protocol proof of equality between a BLS12-381 and a
/// Curve25519 Pedersen commitment, together with a Dalek range proof.
///
/// # Transcript Compression
///
/// `R_BLS` and `R_25519` are **not** transmitted.  The verifier reconstructs
/// them from the responses and the stored challenge `c`.
#[derive(Clone, Debug)]
pub struct BatchedEqualityProof {
    pub c_bytes: [u8; 16],
    pub c_25519_bytes: [u8; 32],
    pub z_e_bytes: [u8; 32],
    pub z_r_bls_bytes: [u8; 32],
    pub z_r_25519_bytes: [u8; 32],
    pub range_proof_bytes: Vec<u8>,
}

impl BatchedEqualityProof {
    /// Canonical wire format serialization.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(16 + 32 + 32 + 32 + 32 + 4 + self.range_proof_bytes.len());
        buf.extend_from_slice(&self.c_bytes);
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
// Dalek helpers
// ============================================================================

fn dalek_pc_gens() -> PedersenGens { PedersenGens::default() }
fn dalek_bp_gens() -> BulletproofGens { BulletproofGens::new(64, 1) }

fn rand_dalek_scalar(rng: &mut (impl CryptoRng + RngCore)) -> DalekScalar {
    let mut wide = [0u8; 64];
    rng.fill_bytes(&mut wide);
    DalekScalar::from_bytes_mod_order_wide(&wide)
}

// ============================================================================
// Challenge computation (128-bit output)
// ============================================================================

fn compute_beq_challenge(
    context: &[u8],
    c_bls_bytes: &[u8; 48],
    c_25519_bytes: &[u8; 32],
    r_bls_bytes: &[u8; 48],
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

#[inline]
fn c128_to_bytes32(c128: &[u8; 16]) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[..16].copy_from_slice(c128);
    b
}

// ============================================================================
// Prover
// ============================================================================

/// Generate a `BatchedEqualityProof` that `m` inside `C_BLS = m·h4 + r_bls·h0`
/// equals the `m` inside a freshly generated Curve25519 commitment.
///
/// Returns `(proof, c_bls)`.
#[allow(clippy::too_many_arguments)]
pub fn prove_batched_equality(
    rng: &mut (impl CryptoRng + RngCore),
    m: u32,
    r_bls: BlsScalar,
    h4: G1Projective,
    h0: G1Projective,
    context: &[u8],
) -> Result<(BatchedEqualityProof, G1Projective)> {
    // ── Step 1: Curve25519 commitment + Dalek range proof ────────────────────
    let r_25519 = rand_dalek_scalar(rng);
    let pc_gens = dalek_pc_gens();
    let bp_gens = dalek_bp_gens();

    let m_dalek = DalekScalar::from(m as u64);
    let c_25519_point = pc_gens.commit(m_dalek, r_25519);
    let c_25519_bytes: [u8; 32] = c_25519_point.compress().to_bytes();

    let mut range_transcript = Transcript::new(b"ACT:BEQ:Range");
    range_transcript.append_message(b"ctx", context);
    let (dalek_proof, _committed) = DalekRangeProof::prove_single(
        &bp_gens, &pc_gens, &mut range_transcript, m as u64, &r_25519, 32,
    )
    .map_err(|e| ActError::ProtocolError(alloc::format!("Dalek range prove failed: {:?}", e)))?;
    let range_proof_bytes = dalek_proof.to_bytes();

    // ── Step 2: Integer blinding factor u_m (240 bits) ───────────────────────
    let mut u_m_le30 = [0u8; 30];
    rng.fill_bytes(&mut u_m_le30);
    let mut u_m_32 = [0u8; 32];
    u_m_32[..30].copy_from_slice(&u_m_le30);
    let u_m_limbs = u256_from_le_bytes(&u_m_32);
    let u_m_bls = scalar_from_le_bytes_mod_order(&u_m_32);
    let u_m_25519 = DalekScalar::from_bytes_mod_order(u_m_32);

    // ── Step 3: Schnorr blinders ──────────────────────────────────────────────
    let u_r_bls = BlsScalar::random(&mut *rng);
    let u_r_25519 = rand_dalek_scalar(&mut *rng);

    // ── Step 4: Schnorr commitments ───────────────────────────────────────────
    let r_bls_point = &(&h4 * &u_m_bls) + &(&h0 * &u_r_bls);
    let r_bls_bytes = G1Affine::from(r_bls_point).to_compressed();

    let r_25519_point = pc_gens.commit(u_m_25519, u_r_25519);
    let r_25519_bytes: [u8; 32] = r_25519_point.compress().to_bytes();

    // ── Step 5: BLS12-381 commitment C_BLS = m·h4 + r_bls·h0 ────────────────
    let c_bls = &(&h4 * &BlsScalar::from(m as u64)) + &(&h0 * &r_bls);
    let c_bls_bytes = G1Affine::from(c_bls).to_compressed();

    // ── Step 6: 128-bit Fiat–Shamir challenge ────────────────────────────────
    let c128 = compute_beq_challenge(
        context, &c_bls_bytes, &c_25519_bytes, &r_bls_bytes, &r_25519_bytes, &range_proof_bytes,
    );
    let c_32 = c128_to_bytes32(&c128);
    let c_limbs = u256_from_le_bytes(&c_32);
    let c_fr  = scalar_from_le_bytes_mod_order(&c_32);
    let c_dalek = DalekScalar::from_bytes_mod_order(c_32);

    // ── Step 7: Integer response z_e = u_m + c·m (over ℤ) ────────────────────
    let cm_limbs = u256_mul_u64(&c_limbs, m as u64);
    let z_e_limbs = u256_add(&u_m_limbs, &cm_limbs);
    let z_e_bytes = u256_to_le_bytes(&z_e_limbs);
    debug_assert_eq!(z_e_bytes[31], 0, "z_e unexpectedly exceeded 31 bytes");

    // ── Step 8: BLS12-381 randomness response ────────────────────────────────
    let z_r_bls = &u_r_bls + &(&c_fr * &r_bls);
    let z_r_bls_bytes = z_r_bls.to_bytes_le();

    // ── Step 9: Curve25519 randomness response ───────────────────────────────
    let z_r_25519 = u_r_25519 + c_dalek * r_25519;
    let z_r_25519_bytes: [u8; 32] = z_r_25519.to_bytes();

    Ok((
        BatchedEqualityProof {
            c_bytes: c128,
            c_25519_bytes,
            z_e_bytes,
            z_r_bls_bytes,
            z_r_25519_bytes,
            range_proof_bytes,
        },
        c_bls,
    ))
}

// ============================================================================
// Verifier
// ============================================================================

/// Verify a [`BatchedEqualityProof`] against the BLS12-381 commitment `c_bls`.
pub fn verify_batched_equality(
    proof: &BatchedEqualityProof,
    c_bls: G1Projective,
    h4: G1Projective,
    h0: G1Projective,
    context: &[u8],
) -> Result<()> {
    // ── 1. Bounds check: z_e < q₂₅₅₁₉ ──────────────────────────────────────
    let z_e_limbs = u256_from_le_bytes(&proof.z_e_bytes);
    if !u256_lt(&z_e_limbs, &Q_25519_LIMBS) {
        return Err(ActError::VerificationFailed(
            "BatchedEqualityProof: z_e >= q_25519 (modular wrap attack)".into(),
        ));
    }

    // ── 2. Read scalar responses ──────────────────────────────────────────────
    let z_m_bls   = scalar_from_le_bytes_mod_order(&proof.z_e_bytes);
    let z_m_25519 = DalekScalar::from_bytes_mod_order(proof.z_e_bytes);
    let z_r_bls   = scalar_from_le_bytes_mod_order(&proof.z_r_bls_bytes);
    let z_r_25519 = DalekScalar::from_bytes_mod_order(proof.z_r_25519_bytes);

    // ── 3. Read stored challenge ──────────────────────────────────────────────
    let c128 = proof.c_bytes;
    let c_32 = c128_to_bytes32(&c128);
    let c_fr = scalar_from_le_bytes_mod_order(&c_32);
    let c_dalek = DalekScalar::from_bytes_mod_order(c_32);

    // ── 4. Deserialize C_25519 ───────────────────────────────────────────────
    let c_25519_compressed = CompressedRistretto(proof.c_25519_bytes);
    let c_25519_point: RistrettoPoint = c_25519_compressed.decompress().ok_or_else(|| {
        ActError::VerificationFailed("BatchedEqualityProof: invalid C_25519 point".into())
    })?;

    // ── 5. Reconstruct R points ───────────────────────────────────────────────
    // R_BLS  = z_m·h4 + z_r·h0 − c·C_BLS
    let r_bls_point = &(&(&h4 * &z_m_bls) + &(&h0 * &z_r_bls)) - &(&c_bls * &c_fr);
    let r_bls_recon_bytes = G1Affine::from(r_bls_point).to_compressed();

    // R_25519 = z_m·G + z_r·H − c·C_25519
    let pc_gens = dalek_pc_gens();
    let r_25519_point = pc_gens.commit(z_m_25519, z_r_25519) - c_25519_point * c_dalek;
    let r_25519_recon_bytes: [u8; 32] = r_25519_point.compress().to_bytes();

    // ── 6. Verify challenge hash ─────────────────────────────────────────────
    let c_bls_bytes = G1Affine::from(c_bls).to_compressed();
    let expected_c128 = compute_beq_challenge(
        context,
        &c_bls_bytes,
        &proof.c_25519_bytes,
        &r_bls_recon_bytes,
        &r_25519_recon_bytes,
        &proof.range_proof_bytes,
    );
    if expected_c128 != c128 {
        return Err(ActError::VerificationFailed(
            "BatchedEqualityProof: challenge mismatch (Schnorr check failed)".into(),
        ));
    }

    // ── 7. Dalek range proof verification ────────────────────────────────────
    let bp_gens = dalek_bp_gens();
    let dalek_proof = DalekRangeProof::from_bytes(&proof.range_proof_bytes).map_err(|e| {
        ActError::VerificationFailed(alloc::format!("Invalid Dalek range proof bytes: {:?}", e))
    })?;
    let mut range_transcript = Transcript::new(b"ACT:BEQ:Range");
    range_transcript.append_message(b"ctx", context);
    dalek_proof.verify_single(&bp_gens, &pc_gens, &mut range_transcript, &c_25519_compressed, 32)
        .map_err(|e| {
            ActError::VerificationFailed(alloc::format!(
                "BatchedEqualityProof: Dalek range proof failed: {:?}", e
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
    use rand::thread_rng;

    fn gens_h4_h0() -> (G1Projective, G1Projective) {
        let gens = Generators::new();
        (gens.h[4], gens.h[0])
    }

    #[test]
    fn batched_equality_proof_roundtrip() {
        let mut rng = thread_rng();
        let (h4, h0) = gens_h4_h0();
        let m = 42u32;
        let r_bls = BlsScalar::random(&mut rng);
        let (proof, c_bls) = prove_batched_equality(&mut rng, m, r_bls, h4, h0, b"ctx").unwrap();
        verify_batched_equality(&proof, c_bls, h4, h0, b"ctx").unwrap();
    }

    #[test]
    fn batched_equality_proof_zero_balance() {
        let mut rng = thread_rng();
        let (h4, h0) = gens_h4_h0();
        let r_bls = BlsScalar::random(&mut rng);
        let (proof, c_bls) = prove_batched_equality(&mut rng, 0, r_bls, h4, h0, b"zero").unwrap();
        verify_batched_equality(&proof, c_bls, h4, h0, b"zero").unwrap();
    }

    #[test]
    fn batched_equality_proof_max_balance() {
        let mut rng = thread_rng();
        let (h4, h0) = gens_h4_h0();
        let r_bls = BlsScalar::random(&mut rng);
        let (proof, c_bls) = prove_batched_equality(&mut rng, u32::MAX, r_bls, h4, h0, b"max").unwrap();
        verify_batched_equality(&proof, c_bls, h4, h0, b"max").unwrap();
    }

    #[test]
    fn wrong_c_bls_fails() {
        let mut rng = thread_rng();
        let (h4, h0) = gens_h4_h0();
        let m = 10u32;
        let r_bls = BlsScalar::random(&mut rng);
        let (proof, _c_bls) = prove_batched_equality(&mut rng, m, r_bls, h4, h0, b"ctx").unwrap();
        let wrong_r = BlsScalar::random(&mut rng);
        let wrong_c_bls = &(&h4 * &BlsScalar::from(m as u64 + 1)) + &(&h0 * &wrong_r);
        assert!(verify_batched_equality(&proof, wrong_c_bls, h4, h0, b"ctx").is_err());
    }

    #[test]
    fn wrong_context_fails() {
        let mut rng = thread_rng();
        let (h4, h0) = gens_h4_h0();
        let r_bls = BlsScalar::random(&mut rng);
        let (proof, c_bls) = prove_batched_equality(&mut rng, 20, r_bls, h4, h0, b"A").unwrap();
        assert!(verify_batched_equality(&proof, c_bls, h4, h0, b"B").is_err());
    }

    #[test]
    fn z_e_fits_in_31_bytes() {
        let mut rng = thread_rng();
        let (h4, h0) = gens_h4_h0();
        let r_bls = BlsScalar::random(&mut rng);
        let (proof, _) = prove_batched_equality(&mut rng, u32::MAX, r_bls, h4, h0, b"size").unwrap();
        assert_eq!(proof.z_e_bytes[31], 0);
    }
}
