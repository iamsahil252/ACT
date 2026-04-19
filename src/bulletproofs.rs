//! Bulletproof-style range-proof helpers using `ark-bulletproofs`.
//!
//! This module implements real zero‑knowledge range proofs for 32‑bit values,
//! using the specified generators `(value_base, blinding_base)`.
//! The proofs are bound to the outer protocol transcript via a hash of the
//! extra data, which is included in the proof’s transcript.

extern crate alloc;
use alloc::vec::Vec;
use ark_bls12_381::{Fr, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::{Field, PrimeField};
use ark_std::rand::RngCore;
use ark_std::Zero;
use sha2::{Digest, Sha256};

use ark_bulletproofs::{
    r1cs::{
        ConstraintSystem, LinearCombination, Variable,
    },
    BulletproofGens, PedersenGens, RangeProof as ArkRangeProof,
};
use ark_std::cfg_into_iter::IntoIterator;

use crate::error::{ActError, Result};
use crate::types::Scalar;

/// Lightweight wrapper for a Bulletproof range proof.
/// Contains the serialised proof and a commitment binding tag.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeProof {
    /// Serialised Bulletproof (variable length)
    pub proof_bytes: Vec<u8>,
    /// Bit length (must be 32 for ACT)
    pub bits: u32,
    /// Hash of the extra transcript data to bind the proof to the outer context.
    pub transcript_tag: [u8; 32],
}

/// Generate a real Bulletproof range proof that `value < 2^bits`.
/// Uses the given `value_base` and `blinding_base` as Pedersen generators.
pub fn prove_range(
    rng: &mut impl RngCore,
    value: u64,
    blinding: Scalar,
    bits: usize,
    value_base: G1Projective,
    blinding_base: G1Projective,
    transcript_label: &'static [u8],
    extra_transcript_data: &[u8],
) -> Result<(RangeProof, G1Projective)> {
    if bits != 32 {
        return Err(ActError::ProtocolError("ACT uses exactly 32-bit range proofs".into()));
    }
    if value >= (1u64 << bits) {
        return Err(ActError::VerificationFailed("value exceeds range".into()));
    }

    // Compute commitment C = value * value_base + blinding * blinding_base
    let commitment = value_base * Fr::from(value) + blinding_base * blinding.0;

    // Build custom Pedersen generators from the provided bases.
    let pedersen_gens = PedersenGens {
        B: value_base.into_affine(),
        B_blinding: blinding_base.into_affine(),
    };

    let bp_gens = BulletproofGens::new(bits, 1);
    let mut transcript = ark_bulletproofs::Transcript::new(b"ACT:RangeProof");
    // Bind the outer context into the transcript
    transcript.append_message(b"label", transcript_label);
    transcript.append_message(b"extra", extra_transcript_data);

    let proof = ArkRangeProof::prove_single(
        rng,
        &bp_gens,
        &pedersen_gens,
        &mut transcript,
        value,
        &blinding.0,
        bits,
    ).map_err(|e| ActError::ProtocolError(format!("Bulletproof generation failed: {:?}", e)))?;

    let proof_bytes = proof.to_bytes();
    let transcript_tag = compute_transcript_tag(transcript_label, extra_transcript_data, value, blinding, bits as u32);

    Ok((
        RangeProof {
            proof_bytes,
            bits: bits as u32,
            transcript_tag,
        },
        commitment,
    ))
}

/// Verify a real Bulletproof range proof.
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
        return Err(ActError::VerificationFailed("range bit-length mismatch".into()));
    }
    if bits != 32 {
        return Err(ActError::ProtocolError("ACT uses exactly 32-bit range proofs".into()));
    }

    let pedersen_gens = PedersenGens {
        B: value_base.into_affine(),
        B_blinding: blinding_base.into_affine(),
    };
    let bp_gens = BulletproofGens::new(bits, 1);
    let mut transcript = ark_bulletproofs::Transcript::new(b"ACT:RangeProof");
    transcript.append_message(b"label", transcript_label);
    transcript.append_message(b"extra", extra_transcript_data);

    let proof_obj = ArkRangeProof::from_bytes(&proof.proof_bytes)
        .map_err(|_| ActError::VerificationFailed("invalid Bulletproof bytes".into()))?;

    proof_obj.verify_single(
        &bp_gens,
        &pedersen_gens,
        &mut transcript,
        &commitment.into_affine(),
        bits,
    ).map_err(|e| ActError::VerificationFailed(format!("Bulletproof verification failed: {:?}", e)))?;

    Ok(())
}

/// Serialise a range proof to bytes (for inclusion in Fiat‑Shamir challenges).
pub fn serialize_proof(proof: &RangeProof) -> Result<Vec<u8>> {
    // Format: [bits:4][tag:32][proof_len:4][proof_bytes...]
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
        return Err(ActError::SerializationError(ark_serialize::SerializationError::InvalidData));
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
        return Err(ActError::SerializationError(ark_serialize::SerializationError::InvalidData));
    }
    let proof_bytes = data[40..].to_vec();
    Ok(RangeProof {
        proof_bytes,
        bits,
        transcript_tag: tag,
    })
}

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
        ).unwrap();

        verify_range(
            &proof,
            commitment,
            32,
            value_base,
            blinding_base,
            b"ACT:Test",
            extra,
        ).unwrap();

        // Serialization roundtrip
        let bytes = serialize_proof(&proof).unwrap();
        let proof2 = deserialize_proof(&bytes).unwrap();
        assert_eq!(proof.bits, proof2.bits);
        assert_eq!(proof.transcript_tag, proof2.transcript_tag);
        assert_eq!(proof.proof_bytes, proof2.proof_bytes);
    }
}
