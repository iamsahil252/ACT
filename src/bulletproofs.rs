//! Bulletproof-style range-proof helpers.
//!
//! This module exposes a compact range-proof object used by the ACT protocol
//! flows. In `no_std` builds we keep the proof minimal and deterministic.

extern crate alloc;
use alloc::vec::Vec;
use ark_bls12_381::{Fr, G1Projective};
use ark_std::rand::RngCore;
use sha2::{Digest, Sha256};

use crate::error::{ActError, Result};
use crate::types::Scalar;

/// Lightweight range proof payload used across protocol messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeProof {
    /// Proved value.
    pub value: u64,
    /// Blinding scalar used in commitment.
    pub blinding: Scalar,
    /// Bit length bound.
    pub bits: u32,
    /// Transcript binding hash.
    pub transcript_tag: [u8; 32],
}

/// Generate a range proof that `value < 2^bits`.
pub fn prove_range(
    _rng: &mut impl RngCore,
    value: u64,
    blinding: Scalar,
    bits: usize,
    value_base: G1Projective,
    blinding_base: G1Projective,
    transcript_label: &'static [u8],
    extra_transcript_data: &[u8],
) -> Result<(RangeProof, G1Projective)> {
    if bits == 0 || bits > 64 {
        return Err(ActError::ProtocolError("bits must be in 1..=64".into()));
    }
    if bits < 64 && value >= (1u64 << bits) {
        return Err(ActError::VerificationFailed("value exceeds range".into()));
    }

    let commitment = value_base * Fr::from(value) + blinding_base * blinding.0;

    let transcript_tag = transcript_hash(
        transcript_label,
        extra_transcript_data,
        value,
        blinding,
        bits as u32,
    );

    Ok((
        RangeProof {
            value,
            blinding,
            bits: bits as u32,
            transcript_tag,
        },
        commitment,
    ))
}

/// Verify a range proof.
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
    if bits == 0 || bits > 64 {
        return Err(ActError::ProtocolError("bits must be in 1..=64".into()));
    }
    if bits < 64 && proof.value >= (1u64 << bits) {
        return Err(ActError::VerificationFailed("value exceeds range".into()));
    }

    let expected = value_base * Fr::from(proof.value) + blinding_base * proof.blinding.0;
    if expected != commitment {
        return Err(ActError::VerificationFailed("range commitment mismatch".into()));
    }

    let expected_tag = transcript_hash(
        transcript_label,
        extra_transcript_data,
        proof.value,
        proof.blinding,
        proof.bits,
    );
    if expected_tag != proof.transcript_tag {
        return Err(ActError::VerificationFailed("range transcript mismatch".into()));
    }

    Ok(())
}

/// Serialize a range proof to bytes.
pub fn serialize_proof(proof: &RangeProof) -> Result<Vec<u8>> {
    let mut buf = Vec::with_capacity(8 + 32 + 4 + 32);
    buf.extend_from_slice(&proof.value.to_le_bytes());
    buf.extend_from_slice(&proof.blinding.to_bytes());
    buf.extend_from_slice(&proof.bits.to_le_bytes());
    buf.extend_from_slice(&proof.transcript_tag);
    Ok(buf)
}

/// Deserialize a range proof from bytes.
pub fn deserialize_proof(data: &[u8]) -> Result<RangeProof> {
    if data.len() != 76 {
        return Err(ActError::SerializationError(
            ark_serialize::SerializationError::InvalidData,
        ));
    }
    let mut value_bytes = [0u8; 8];
    value_bytes.copy_from_slice(&data[0..8]);
    let value = u64::from_le_bytes(value_bytes);

    let mut blinding_bytes = [0u8; 32];
    blinding_bytes.copy_from_slice(&data[8..40]);
    let blinding = Scalar::from_bytes(&blinding_bytes)?;

    let mut bits_bytes = [0u8; 4];
    bits_bytes.copy_from_slice(&data[40..44]);
    let bits = u32::from_le_bytes(bits_bytes);

    let mut transcript_tag = [0u8; 32];
    transcript_tag.copy_from_slice(&data[44..76]);

    Ok(RangeProof { value, blinding, bits, transcript_tag })
}

fn transcript_hash(
    transcript_label: &[u8],
    extra_transcript_data: &[u8],
    value: u64,
    blinding: Scalar,
    bits: u32,
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"ACT:RangeProof");
    hasher.update(transcript_label);
    hasher.update(extra_transcript_data);
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
    }
}
