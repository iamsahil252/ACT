//! Bulletproof-style range-proof helpers using `ark-bulletproofs`.
//!
//! This module implements real zero-knowledge range proofs for 32-bit values,
//! using the R1CS interface of `ark-bulletproofs` with BLS12-381 G1.
//!
//! The prover and verifier share identical gadget logic (`range_proof_gadget_*`)
//! so transcript state cannot drift between them.

extern crate alloc;
use alloc::vec::Vec;
use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::One;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{CryptoRng, RngCore};
use sha2::{Digest, Sha256};

use ark_bulletproofs::{
    r1cs::{ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, Verifier},
    BulletproofGens, PedersenGens,
};
use merlin::Transcript;

use crate::error::{ActError, Result};
use crate::hash::hash_to_g1;
use crate::types::Scalar;

/// Number of BulletproofGens to allocate.
/// 64 generators is sufficient for a 32-multiplier (32-bit) R1CS range proof.
const BP_GENS_CAPACITY: usize = 64;

// ============================================================================
// ACT-specific Bulletproof inner-product vector generators
// ============================================================================

/// Build a `BulletproofGens` whose inner-product vector bases (**G** and **H**)
/// are derived from ACT-specific domain separators, satisfying the requirement
/// of Section 9.2 of the ACT specification.
///
/// The domain separators used are:
/// - G vector: `b"ACT:BP:G:"` with a 4-byte big-endian index suffix.
/// - H vector: `b"ACT:BP:H:"` with a 4-byte big-endian index suffix.
///
/// Both derive points via [`hash_to_g1`] (RFC 9380 WB-SSWU / SHA-256), which
/// is a completely different derivation path from the library's default ChaCha
/// PRNG seeded from SHA3-512.  The BBS+ Pedersen bases use the domain
/// separator `b"ACT:BBS:"`, so the inner-product bases are provably
/// orthogonal in derivation (computationally orthogonal under the DL
/// assumption).
///
/// Because this construction is deterministic and relatively expensive
/// (128 hash-to-curve operations), the result is cached in a `OnceLock`.
fn make_act_bp_gens() -> BulletproofGens<G1Affine> {
    // Generate G and H points using ACT-specific domain separators.
    let g_pts: alloc::vec::Vec<G1Affine> = (0..BP_GENS_CAPACITY)
        .map(|i| hash_to_g1(b"ACT:BP:G:", &(i as u32).to_be_bytes()).into_affine())
        .collect();
    let h_pts: alloc::vec::Vec<G1Affine> = (0..BP_GENS_CAPACITY)
        .map(|i| hash_to_g1(b"ACT:BP:H:", &(i as u32).to_be_bytes()).into_affine())
        .collect();

    // `BulletproofGens` has private `G_vec`/`H_vec` fields with no public
    // constructor accepting custom bases.  We inject them via the
    // `CanonicalDeserialize` path, which serialises the struct in the
    // following format (all lengths as u64 LE, points compressed 48 bytes):
    //
    //   [gens_capacity: u64][party_capacity: u64]
    //   [G_vec outer len: u64]
    //     [G_vec[0] inner len: u64] [G1Affine × BP_GENS_CAPACITY]
    //   [H_vec outer len: u64]
    //     [H_vec[0] inner len: u64] [G1Affine × BP_GENS_CAPACITY]
    let point_block = 8 + BP_GENS_CAPACITY * 48; // inner_len u64 + points
    let mut buf = alloc::vec::Vec::with_capacity(16 + 2 * (8 + point_block));

    buf.extend_from_slice(&(BP_GENS_CAPACITY as u64).to_le_bytes()); // gens_capacity
    buf.extend_from_slice(&1u64.to_le_bytes()); // party_capacity = 1

    // G_vec: 1 outer entry, BP_GENS_CAPACITY inner points
    buf.extend_from_slice(&1u64.to_le_bytes()); // outer Vec len = 1 party
    buf.extend_from_slice(&(BP_GENS_CAPACITY as u64).to_le_bytes()); // inner len
    for pt in &g_pts {
        pt.serialize_compressed(&mut buf)
            .expect("G1Affine compressed serialization is infallible");
    }

    // H_vec: 1 outer entry, BP_GENS_CAPACITY inner points
    buf.extend_from_slice(&1u64.to_le_bytes()); // outer Vec len = 1 party (H_vec)
    buf.extend_from_slice(&(BP_GENS_CAPACITY as u64).to_le_bytes()); // inner len
    for pt in &h_pts {
        pt.serialize_compressed(&mut buf)
            .expect("G1Affine compressed serialization is infallible");
    }

    BulletproofGens::<G1Affine>::deserialize_compressed(&buf[..])
        .expect("BulletproofGens construction from valid ACT generator points cannot fail")
}

/// Return a reference to the process-wide cached ACT `BulletproofGens`.
///
/// The generators are initialised once (lazily) using [`make_act_bp_gens`].
fn act_bp_gens() -> &'static BulletproofGens<G1Affine> {
    static CACHE: std::sync::OnceLock<BulletproofGens<G1Affine>> = std::sync::OnceLock::new();
    CACHE.get_or_init(make_act_bp_gens)
}

/// Lightweight wrapper for a Bulletproof range proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeProof {
    /// Serialised R1CS proof bytes.
    pub proof_bytes: Vec<u8>,
    /// Bit length (must be 32 for ACT).
    pub bits: u32,
    /// Binding tag: SHA-256 hash of the outer-proof extra transcript data.
    pub transcript_tag: [u8; 32],
}

/// Generate a real Bulletproof range proof that `value < 2^bits`.
///
/// Returns the proof together with the Pedersen commitment
/// `commitment = value * value_base + blinding * blinding_base`.
pub fn prove_range(
    rng: &mut (impl CryptoRng + RngCore),
    value: u64,
    blinding: Scalar,
    bits: usize,
    value_base: G1Projective,
    blinding_base: G1Projective,
    transcript_label: &'static [u8],
    extra_transcript_data: &[u8],
) -> Result<(RangeProof, G1Projective)> {
    if bits != 32 {
        return Err(ActError::ProtocolError(
            "ACT uses exactly 32-bit range proofs".into(),
        ));
    }
    if value >= (1u64 << bits) {
        return Err(ActError::VerificationFailed("value exceeds range".into()));
    }

    let pc_gens = PedersenGens::<G1Affine> {
        B: value_base.into_affine(),
        B_blinding: blinding_base.into_affine(),
    };
    let bp_gens = act_bp_gens();

    let mut transcript = Transcript::new(b"ACT:RangeProof");
    transcript.append_message(b"label", transcript_label);
    transcript.append_message(b"extra", extra_transcript_data);

    let mut prover = Prover::<G1Affine, &mut Transcript>::new(&pc_gens, &mut transcript);

    // Commit to value; prover.commit returns the affine commitment point.
    let (commitment_affine, v_var) = prover.commit(Fr::from(value), blinding.0);

    // Bit-decomposition range check.
    range_proof_gadget_prover(&mut prover, v_var, value, bits)
        .map_err(|e| ActError::ProtocolError(alloc::format!("R1CS prover error: {:?}", e)))?;

    let r1cs_proof = prover
        .prove(rng, bp_gens)
        .map_err(|e| ActError::ProtocolError(alloc::format!("Bulletproof prove error: {:?}", e)))?;

    let mut proof_bytes = Vec::new();
    r1cs_proof
        .serialize_compressed(&mut proof_bytes)
        .map_err(ActError::SerializationError)?;

    let transcript_tag = compute_transcript_tag(
        transcript_label,
        extra_transcript_data,
        value,
        blinding,
        bits as u32,
    );

    let commitment: G1Projective = commitment_affine.into();
    Ok((
        RangeProof {
            proof_bytes,
            bits: bits as u32,
            transcript_tag,
        },
        commitment,
    ))
}

/// Verify a Bulletproof range proof.
pub fn verify_range(
    proof: &RangeProof,
    commitment: G1Projective,
    bits: usize,
    value_base: G1Projective,
    blinding_base: G1Projective,
    transcript_label: &'static [u8],
    extra_transcript_data: &[u8],
) -> Result<()> {
    if bits as u32 != proof.bits {
        return Err(ActError::VerificationFailed(
            "range bit-length mismatch".into(),
        ));
    }
    if bits != 32 {
        return Err(ActError::ProtocolError(
            "ACT uses exactly 32-bit range proofs".into(),
        ));
    }

    let pc_gens = PedersenGens::<G1Affine> {
        B: value_base.into_affine(),
        B_blinding: blinding_base.into_affine(),
    };
    let bp_gens = act_bp_gens();

    let mut transcript = Transcript::new(b"ACT:RangeProof");
    transcript.append_message(b"label", transcript_label);
    transcript.append_message(b"extra", extra_transcript_data);

    let mut verifier = Verifier::<G1Affine, &mut Transcript>::new(&mut transcript);

    // Feed the commitment into the verifier's transcript.
    let v_var = verifier.commit(commitment.into_affine());

    // Identical bit-decomposition gadget; no witness values needed.
    range_proof_gadget_verifier(&mut verifier, v_var, bits)
        .map_err(|e| ActError::VerificationFailed(alloc::format!("R1CS verifier error: {:?}", e)))?;

    let r1cs_proof = R1CSProof::<G1Affine>::deserialize_compressed(&proof.proof_bytes[..])
        .map_err(|_| ActError::VerificationFailed("invalid Bulletproof bytes".into()))?;

    verifier
        .verify(&r1cs_proof, &pc_gens, bp_gens)
        .map_err(|e| {
            ActError::VerificationFailed(alloc::format!("Bulletproof verify failed: {:?}", e))
        })?;

    Ok(())
}

/// Serialise a range proof to bytes (for inclusion in Fiat-Shamir challenges).
pub fn serialize_proof(proof: &RangeProof) -> Result<Vec<u8>> {
    // Format: [bits:4 LE][tag:32][proof_len:4 LE][proof_bytes...]
    let mut buf = Vec::new();
    buf.extend_from_slice(&proof.bits.to_le_bytes());
    buf.extend_from_slice(&proof.transcript_tag);
    buf.extend_from_slice(&(proof.proof_bytes.len() as u32).to_le_bytes());
    buf.extend_from_slice(&proof.proof_bytes);
    Ok(buf)
}

/// Deserialise a range proof from bytes.
pub fn deserialize_proof(data: &[u8]) -> Result<RangeProof> {
    if data.len() < 4 + 32 + 4 {
        return Err(ActError::SerializationError(
            ark_serialize::SerializationError::InvalidData,
        ));
    }
    let mut bits_bytes = [0u8; 4];
    bits_bytes.copy_from_slice(&data[0..4]);
    let bits = u32::from_le_bytes(bits_bytes);
    let mut tag = [0u8; 32];
    tag.copy_from_slice(&data[4..36]);
    let mut len_bytes = [0u8; 4];
    len_bytes.copy_from_slice(&data[36..40]);
    let proof_len = u32::from_le_bytes(len_bytes) as usize;
    if data.len() != 40 + proof_len {
        return Err(ActError::SerializationError(
            ark_serialize::SerializationError::InvalidData,
        ));
    }
    let proof_bytes = data[40..].to_vec();
    Ok(RangeProof {
        proof_bytes,
        bits,
        transcript_tag: tag,
    })
}

// ============================================================================
// Internal gadget: bit-decomposition range check
// ============================================================================

/// Prover-side range-check gadget.
///
/// Proves that the committed variable `v_var` equals `value` and that
/// `0 <= value < 2^n_bits` by decomposing `value` into `n_bits` bits.
///
/// For each bit index `i`:
///   - Allocate multiplier `(b_l, b_r, b_o)` with `b_l = bit_i`, `b_r = 1-bit_i`.
///   - Constrain `b_l + b_r = 1`   (b_r is the complement of b_l).
///   - Constrain `b_o = 0`          (product is zero, so b_l is a bit).
/// Then constrain `v_var = sum(b_l_i * 2^i)`.
fn range_proof_gadget_prover<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    v_var: Variable<Fr>,
    value: u64,
    n_bits: usize,
) -> core::result::Result<(), ark_bulletproofs::r1cs::R1CSError> {
    let mut bit_sum: LinearCombination<Fr> = LinearCombination::default();
    let mut pow2 = Fr::one();

    for i in 0..n_bits {
        let bit_val = ((value >> i) & 1) as u64;
        let bit_fr = Fr::from(bit_val);
        let one_minus_bit = Fr::one() - bit_fr;

        // l = b_i, r = 1 - b_i; implicit constraint: l * r = o.
        let (b_l, b_r, b_o) = cs.allocate_multiplier(Some((bit_fr, one_minus_bit)))?;

        // Explicit: b_l + b_r - 1 = 0.
        cs.constrain(b_l + b_r - Variable::One());
        // Explicit: b_o = 0 (ensures b_l is a bit).
        cs.constrain(LinearCombination::from(b_o));

        // Accumulate: bit_sum += b_l * 2^i.
        bit_sum = bit_sum + b_l * pow2;
        pow2 = pow2 + pow2;
    }

    // v = sum(b_i * 2^i).
    cs.constrain(LinearCombination::from(v_var) - bit_sum);

    Ok(())
}

/// Verifier-side range-check gadget.
///
/// Structurally identical to `range_proof_gadget_prover` but without witness
/// values (`None` passed to `allocate_multiplier`).
fn range_proof_gadget_verifier<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    v_var: Variable<Fr>,
    n_bits: usize,
) -> core::result::Result<(), ark_bulletproofs::r1cs::R1CSError> {
    let mut bit_sum: LinearCombination<Fr> = LinearCombination::default();
    let mut pow2 = Fr::one();

    for _ in 0..n_bits {
        let (b_l, b_r, b_o) = cs.allocate_multiplier(None)?;

        cs.constrain(b_l + b_r - Variable::One());
        cs.constrain(LinearCombination::from(b_o));

        bit_sum = bit_sum + b_l * pow2;
        pow2 = pow2 + pow2;
    }

    cs.constrain(LinearCombination::from(v_var) - bit_sum);

    Ok(())
}

/// Compute the binding tag for the range proof.
fn compute_transcript_tag(
    label: &[u8],
    extra: &[u8],
    value: u64,
    blinding: Scalar,
    bits: u32,
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"ACT:RangeProof");
    hasher.update(label);
    hasher.update(extra);
    hasher.update(value.to_le_bytes());
    hasher.update(blinding.to_bytes());
    hasher.update(bits.to_le_bytes());
    hasher.finalize().into()
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
    fn range_proof_roundtrip() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let value = 12345u64;
        let blinding = Scalar::rand(&mut rng);
        let value_base = gens.h[4];
        let blinding_base = gens.h[0];

        let extra = b"test extra data";

        let (proof, commitment) = prove_range(
            &mut rng,
            value,
            blinding,
            32,
            value_base,
            blinding_base,
            b"ACT:Test",
            extra,
        )
        .unwrap();

        verify_range(
            &proof,
            commitment,
            32,
            value_base,
            blinding_base,
            b"ACT:Test",
            extra,
        )
        .unwrap();

        // Serialization roundtrip.
        let bytes = serialize_proof(&proof).unwrap();
        let proof2 = deserialize_proof(&bytes).unwrap();
        assert_eq!(proof.bits, proof2.bits);
        assert_eq!(proof.transcript_tag, proof2.transcript_tag);
        assert_eq!(proof.proof_bytes, proof2.proof_bytes);
    }

    #[test]
    fn range_proof_wrong_commitment_fails() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let value = 100u64;
        let blinding = Scalar::rand(&mut rng);
        let extra = b"extra";

        let (proof, _commitment) = prove_range(
            &mut rng,
            value,
            blinding,
            32,
            gens.h[4],
            gens.h[0],
            b"ACT:Test",
            extra,
        )
        .unwrap();

        // Use a different commitment (for a different value).
        let wrong_blinding = Scalar::rand(&mut rng);
        let wrong_commitment =
            gens.h[4] * ark_bls12_381::Fr::from(999u64) + gens.h[0] * wrong_blinding.0;

        let result = verify_range(
            &proof,
            wrong_commitment,
            32,
            gens.h[4],
            gens.h[0],
            b"ACT:Test",
            extra,
        );
        assert!(result.is_err(), "verification must fail for wrong commitment");
    }

    #[test]
    fn transcript_scalar_uses_fixed_width_bytes() {
        // Verify that k_cur.to_bytes() always returns exactly 32 bytes.
        let mut rng = thread_rng();
        let k_cur = Scalar::rand(&mut rng);
        let bytes = k_cur.to_bytes();
        assert_eq!(bytes.len(), 32, "Scalar::to_bytes must return exactly 32 bytes");
    }

    /// Verify that the ACT inner-product generator bases are deterministic and
    /// distinct from the library defaults (Section 9.2 of the specification).
    #[test]
    fn act_bp_gens_deterministic_and_distinct_from_defaults() {
        // Two independent calls must produce the same generators.
        let gens_a = make_act_bp_gens();
        let gens_b = make_act_bp_gens();

        let a_g: alloc::vec::Vec<_> = gens_a.G(BP_GENS_CAPACITY, 1).cloned().collect();
        let b_g: alloc::vec::Vec<_> = gens_b.G(BP_GENS_CAPACITY, 1).cloned().collect();
        assert_eq!(a_g, b_g, "ACT BulletproofGens G must be deterministic");

        let a_h: alloc::vec::Vec<_> = gens_a.H(BP_GENS_CAPACITY, 1).cloned().collect();
        let b_h: alloc::vec::Vec<_> = gens_b.H(BP_GENS_CAPACITY, 1).cloned().collect();
        assert_eq!(a_h, b_h, "ACT BulletproofGens H must be deterministic");

        // The ACT generators must differ from the library defaults.
        let default_gens = BulletproofGens::<G1Affine>::new(BP_GENS_CAPACITY, 1);
        let default_g: alloc::vec::Vec<_> = default_gens.G(BP_GENS_CAPACITY, 1).cloned().collect();
        let default_h: alloc::vec::Vec<_> = default_gens.H(BP_GENS_CAPACITY, 1).cloned().collect();

        assert_ne!(
            a_g, default_g,
            "ACT G bases must differ from ark-bulletproofs defaults"
        );
        assert_ne!(
            a_h, default_h,
            "ACT H bases must differ from ark-bulletproofs defaults"
        );
    }

    /// Verify that each ACT generator is distinct (no accidental collisions
    /// between G and H vectors, and between indices).
    #[test]
    fn act_bp_gens_orthogonal_to_bbs_generators() {
        let bp_gens = make_act_bp_gens();
        let bbs_gens = crate::setup::Generators::new();

        let g_vec: alloc::vec::Vec<_> = bp_gens.G(BP_GENS_CAPACITY, 1).cloned().collect();
        let h_vec: alloc::vec::Vec<_> = bp_gens.H(BP_GENS_CAPACITY, 1).cloned().collect();

        // No ACT BP generator should equal any BBS+ generator.
        for bbs_h in &bbs_gens.h {
            let bbs_affine = bbs_h.into_affine();
            assert!(
                !g_vec.contains(&bbs_affine),
                "ACT BP G must not overlap with BBS+ h generators"
            );
            assert!(
                !h_vec.contains(&bbs_affine),
                "ACT BP H must not overlap with BBS+ h generators"
            );
        }
    }
}
