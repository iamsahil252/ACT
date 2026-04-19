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
use ark_serialize::CanonicalSerialize;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::{UniformRand};
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

// Precomputed limb form of Q_25519 for the inline u64 comparator.
const Q_25519_LIMBS: [u64; 4] = {
    let b = Q_25519_LE;
    [
        u64::from_le_bytes([b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7]]),
        u64::from_le_bytes([b[8],b[9],b[10],b[11],b[12],b[13],b[14],b[15]]),
        u64::from_le_bytes([b[16],b[17],b[18],b[19],b[20],b[21],b[22],b[23]]),
        u64::from_le_bytes([b[24],b[25],b[26],b[27],b[28],b[29],b[30],b[31]]),
    ]
};

// ============================================================================
// Inline 256-bit integer arithmetic (stack-allocated, no heap)
//
// Replaces num-bigint::BigUint for the hot BEQ prover/verifier path.
// Representation: four little-endian u64 limbs (limbs[0] is least significant).
// ============================================================================

/// Load a 256-bit integer from a 32-byte little-endian array.
#[inline]
fn u256_from_le_bytes(bytes: &[u8; 32]) -> [u64; 4] {
    let mut limbs = [0u64; 4];
    for (i, chunk) in bytes.chunks_exact(8).enumerate() {
        limbs[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    limbs
}

/// Store a 256-bit integer into a 32-byte little-endian array.
#[inline]
fn u256_to_le_bytes(limbs: &[u64; 4]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (i, &l) in limbs.iter().enumerate() {
        bytes[i * 8..(i + 1) * 8].copy_from_slice(&l.to_le_bytes());
    }
    bytes
}

/// Compare two 256-bit integers: returns `true` if `a < b`.
#[inline]
fn u256_lt(a: &[u64; 4], b: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] { return a[i] < b[i]; }
    }
    false // equal
}

/// Multiply a 256-bit integer by a 64-bit value, returning the low 256 bits.
/// Callers must ensure no overflow (the product fits in 256 bits).
#[inline]
fn u256_mul_u64(a: &[u64; 4], b: u64) -> [u64; 4] {
    let mut result = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let prod = a[i] as u128 * b as u128 + carry;
        result[i] = prod as u64;
        carry = prod >> 64;
    }
    // Caller guarantees the product fits; any carry here would be a bug.
    debug_assert_eq!(carry, 0, "u256_mul_u64: overflow");
    result
}

/// Add two 256-bit integers, returning the low 256 bits.
/// Callers must ensure no overflow (the sum fits in 256 bits).
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
/// Curve25519 Pedersen commitment, together with a Dalek range proof showing
/// the committed value lies in `[0, 2³²−1]`.
#[derive(Clone, Debug)]
/// A dual-curve Sigma protocol proof of equality between a BLS12-381 and a
/// Curve25519 Pedersen commitment, together with a Dalek range proof showing
/// the committed value lies in `[0, 2³²−1]`.
///
/// # Transcript Compression
///
/// The Schnorr commitment points `R_BLS` and `R_25519` are **not transmitted**
/// over the wire.  Instead the prover stores the 128-bit challenge `c` directly
/// in the proof.  The verifier reconstructs the R points from the responses and
/// the public commitments (`R = z·G − c·C`), then checks that their hash
/// matches `c`.  This saves 64 bytes per proof (48 B for R_BLS + 32 B for
/// R_25519 − 16 B for c) and eliminates two elliptic-curve decompressions on
/// the server.
pub struct BatchedEqualityProof {
    /// 128-bit Fiat–Shamir challenge (16 B).  The verifier uses this to
    /// reconstruct the Schnorr commitments R without transmitting them.
    pub c_bytes: [u8; 16],
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
    /// Format: `c(16) ∥ c_25519(32) ∥ z_e(32) ∥ z_r_bls(32) ∥
    ///          z_r_25519(32) ∥ range_len(4 LE) ∥ range_proof(variable)`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(
            16 + 32 + 32 + 32 + 32 + 4 + self.range_proof_bytes.len(),
        );
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
/// The hash commits to both C_BLS and C_25519 (binding the prover's values)
/// and to R_BLS and R_25519 (the Schnorr commitments that randomise the proof).
/// The resulting c is truncated to 128 bits: `m ≤ 2³²` and `c < 2¹²⁸` ensures
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

    // Represent u_m as a 32-byte LE array (fits in 32 bytes since 240 < 256).
    let mut u_m_32 = [0u8; 32];
    u_m_32[..30].copy_from_slice(&u_m_le30);
    // Stack-allocated 256-bit limb representation of u_m.
    let u_m_limbs = u256_from_le_bytes(&u_m_32);

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
    // Stack-allocated 256-bit representation of c (upper 16 bytes are zero).
    let c_limbs = u256_from_le_bytes(&c_32);
    let c_fr = Fr::from_le_bytes_mod_order(&c_32);
    let c_dalek = DalekScalar::from_bytes_mod_order(c_32);

    // ── Step 7: Integer response z_e = u_m + c·m  (over ℤ, no modulo) ────────
    // c ≤ 2¹²⁸, m ≤ 2³², so c·m ≤ 2¹⁶⁰; u_m ≤ 2²⁴⁰; sum ≤ 2²⁴¹ — fits in U256.
    let cm_limbs = u256_mul_u64(&c_limbs, m as u64);
    let z_e_limbs = u256_add(&u_m_limbs, &cm_limbs);
    let z_e_bytes = u256_to_le_bytes(&z_e_limbs);
    // Sanity: the honest prover never exceeds 31 bytes of significant content.
    debug_assert!(z_e_bytes[31] == 0, "z_e unexpectedly exceeded 31 bytes");

    // ── Step 8: BLS12-381 randomness response ────────────────────────────────
    let z_r_bls = u_r_bls + c_fr * r_bls;
    let mut z_r_bls_bytes = [0u8; 32];
    z_r_bls
        .serialize_compressed(&mut z_r_bls_bytes[..])
        .map_err(ActError::SerializationError)?;

    // ── Step 9: Curve25519 randomness response ───────────────────────────────
    let z_r_25519 = u_r_25519 + c_dalek * r_25519;
    let z_r_25519_bytes: [u8; 32] = z_r_25519.to_bytes();

    // ── Assemble proof (transcript-compressed: c stored instead of R points) ──
    // R_BLS (48 B) and R_25519 (32 B) are omitted from the wire format.
    // The verifier reconstructs them from the responses and the committed
    // challenge, saving 64 bytes per proof.
    let proof = BatchedEqualityProof {
        c_bytes: c128,
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
/// The proof uses transcript compression: R_BLS and R_25519 are not transmitted;
/// instead the prover stores the 128-bit challenge `c`.  The verifier:
///
/// 1. Checks `z_e < q₂₅₅₁₉` (prevents modular wrap attacks).
/// 2. Reconstructs `R_BLS = z_m_bls·h4 + z_r_bls·h0 − c·C_BLS` (no decompression).
/// 3. Reconstructs `R_25519 = z_m_25519·G + z_r_25519·H − c·C_25519` (no decompression).
/// 4. Verifies `H(context, C_BLS, C_25519, R_BLS, R_25519, range_proof) == c`.
/// 5. Verifies the Dalek range proof `m ∈ [0, 2³²−1]` against `C_25519`.
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
    // using inline u64-limb arithmetic to avoid heap allocation.
    let z_e_limbs = u256_from_le_bytes(&proof.z_e_bytes);
    if !u256_lt(&z_e_limbs, &Q_25519_LIMBS) {
        return Err(ActError::VerificationFailed(
            "BatchedEqualityProof: z_e >= q_25519 (modular wrap attack)".into(),
        ));
    }

    // ── 2. Read scalar responses ──────────────────────────────────────────────
    // Since z_e < q₂₅₅₁₉ < q_BLS, both reductions are no-ops.
    let z_m_bls    = Fr::from_le_bytes_mod_order(&proof.z_e_bytes);
    let z_m_25519  = DalekScalar::from_bytes_mod_order(proof.z_e_bytes);
    let z_r_bls    = Fr::from_le_bytes_mod_order(&proof.z_r_bls_bytes);
    let z_r_25519  = DalekScalar::from_bytes_mod_order(proof.z_r_25519_bytes);

    // ── 3. Read the stored challenge and expand to scalar form ───────────────
    let c128   = proof.c_bytes;
    let c_32   = c128_to_bytes32(&c128);
    let c_fr   = Fr::from_le_bytes_mod_order(&c_32);
    let c_dalek = DalekScalar::from_bytes_mod_order(c_32);

    // ── 4. Deserialize C_25519 ───────────────────────────────────────────────
    let c_25519_compressed = CompressedRistretto(proof.c_25519_bytes);
    let c_25519_point: RistrettoPoint = c_25519_compressed.decompress().ok_or_else(|| {
        ActError::VerificationFailed("BatchedEqualityProof: invalid C_25519 point".into())
    })?;

    // ── 5. Reconstruct R points from responses (transcript compression) ──────
    // R_BLS  = z_m·h4 + z_r·h0 − c·C_BLS
    // R_25519 = z_m·G + z_r·H  − c·C_25519
    // These are the Schnorr commitments the prover used when computing c.
    // They match exactly when the proof is honest; soundness follows from
    // the collision-resistance of SHA-256.

    let r_bls_point = h4 * z_m_bls + h0 * z_r_bls - c_bls * c_fr;
    let mut r_bls_recon_bytes = [0u8; 48];
    r_bls_point
        .into_affine()
        .serialize_compressed(&mut r_bls_recon_bytes[..])
        .map_err(ActError::SerializationError)?;

    let pc_gens = dalek_pc_gens();
    let r_25519_point = pc_gens.commit(z_m_25519, z_r_25519) - c_25519_point * c_dalek;
    let r_25519_recon_bytes: [u8; 32] = r_25519_point.compress().to_bytes();

    // ── 6. Serialize C_BLS and verify the challenge hash ────────────────────
    let mut c_bls_bytes_48 = [0u8; 48];
    c_bls
        .into_affine()
        .serialize_compressed(&mut c_bls_bytes_48[..])
        .map_err(ActError::SerializationError)?;

    let expected_c128 = compute_beq_challenge(
        context,
        &c_bls_bytes_48,
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
        // Header: c(16) + c_25519(32) + z_e(32) + z_r_bls(32) + z_r_25519(32) + range_len(4) = 148 bytes
        // plus the variable-length range proof (≈ 673 bytes for 32-bit).
        assert!(bytes.len() >= 148);
    }
}
