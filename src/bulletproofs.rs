//! Bulletproofs integration for range proofs.
//!
//! This module provides 32‑bit range proofs using Bulletproofs with custom
//! Pedersen generators that match the BBS+ generators `h_3`/`h_4` and `h_0`.
//! The proofs are bound to the outer protocol transcript via the extra data
//! parameter, which must include `H_ctx` and relevant commitments.
extern crate alloc;
use alloc::vec::Vec;
use ark_std::vec;
use ark_bulletproofs::{PedersenGens, RangeProof, Transcript};
use ark_bls12_381::{Fr, G1Projective};
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use ark_std::rand::RngCore;
use crate::error::{ActError, Result};
use crate::types::Scalar;

/// Generate a Bulletproof that a value lies in `[0, 2^bits)`.
///
/// # Arguments
/// - `rng`: secure RNG.
/// - `value`: the value to prove (must be < 2^bits).
/// - `blinding`: the blinding factor for the Pedersen commitment.
/// - `bits`: number of bits (typically 32).
/// - `value_base`: the generator for the committed value (e.g., `h_4` or `h_3`).
/// - `blinding_base`: the generator for the blinding factor (always `h_0`).
/// - `transcript_label`: domain separation label (e.g., `b"ACT:Expiry"`).
/// - `extra_transcript_data`: additional data to bind into the transcript
///   (must include `H_ctx` and all BBS+ commitments and public values).
///
/// # Returns
/// A tuple containing the range proof and the Pedersen commitment to the value.
pub fn prove_range(
    rng: &mut impl RngCore,
    value: u64,
    blinding: Scalar,
    bits: usize,
    value_base: G1Projective,
    blinding_base: G1Projective,
    transcript_label: &'static [u8],
    extra_transcript_data: &[u8],
) -> Result<(RangeProof<Fr>, G1Projective)> {
    // Construct custom Pedersen generators using the specified bases.
    let pc_gens = PedersenGens {
        B: value_base.into_affine(),
        B_blinding: blinding_base.into_affine(),
    };

    // Initialize transcript with domain separation label.
    let mut transcript = Transcript::new(transcript_label);
    // Bind the extra data (H_ctx, commitments, etc.) to the transcript.
    transcript.append_message(b"extra", extra_transcript_data);

    // Generate the proof.
    let proof = RangeProof::prove_single(
        rng,
        &pc_gens,
        &mut transcript,
        value,
        &blinding.0,
        bits,
    )?;

    // Compute the commitment (should match the one the verifier sees).
    let commitment = pc_gens.commit(Fr::from(value), blinding.0)?;

    Ok((proof, commitment))
}

/// Verify a Bulletproof range proof.
///
/// # Arguments
/// - `proof`: the range proof to verify.
/// - `commitment`: the Pedersen commitment to the value.
/// - `bits`: number of bits (must match proof generation).
/// - `value_base`: the generator for the committed value.
/// - `blinding_base`: the generator for the blinding factor.
/// - `transcript_label`: same domain separation label used during proving.
/// - `extra_transcript_data`: same extra data used during proving.
pub fn verify_range(
    proof: &RangeProof<Fr>,
    commitment: G1Projective,
    bits: usize,
    value_base: G1Projective,
    blinding_base: G1Projective,
    transcript_label: &'static [u8],
    extra_transcript_data: &[u8],
) -> Result<()> {
    let pc_gens = PedersenGens {
        B: value_base.into_affine(),
        B_blinding: blinding_base.into_affine(),
    };

    let mut transcript = Transcript::new(transcript_label);
    transcript.append_message(b"extra", extra_transcript_data);

    proof.verify_single(
        &pc_gens,
        &mut transcript,
        &commitment.into_affine(),
        bits,
    )?;

    Ok(())
}

/// Serialize a range proof to bytes.
///
/// The `RangeProof` type implements `CanonicalSerialize`.
pub fn serialize_proof(proof: &RangeProof<Fr>) -> Result<Vec<u8>> {
    let mut buf = Vec::new();
    proof.serialize_compressed(&mut buf)?;
    Ok(buf)
}

/// Deserialize a range proof from bytes.
pub fn deserialize_proof(data: &[u8]) -> Result<RangeProof<Fr>> {
    Ok(RangeProof::deserialize_compressed(data)?)
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

    #[test]
    fn invalid_value_fails() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let value = 1u64 << 33; // exceeds 32 bits
        let blinding = Scalar::rand(&mut rng);
        let value_base = gens.h[4];
        let blinding_base = gens.h[0];

        let extra = b"test extra data";

        let result = prove_range(
            &mut rng,
            value,
            blinding,
            32,
            value_base,
            blinding_base,
            b"ACT:Test",
            extra,
        );
        // Bulletproofs will reject the value > 2^bits during proving.
        assert!(result.is_err());
    }

    #[test]
    fn tampered_extra_data_fails() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let value = 42u64;
        let blinding = Scalar::rand(&mut rng);
        let value_base = gens.h[4];
        let blinding_base = gens.h[0];

        let extra = b"correct data";

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

        let wrong_extra = b"wrong data";
        let result = verify_range(
            &proof,
            commitment,
            32,
            value_base,
            blinding_base,
            b"ACT:Test",
            wrong_extra,
        );
        assert!(result.is_err());
    }

    #[test]
    fn serialization_roundtrip() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let value = 999u64;
        let blinding = Scalar::rand(&mut rng);
        let (proof, _) = prove_range(
            &mut rng,
            value,
            blinding,
            32,
            gens.h[4],
            gens.h[0],
            b"ACT:Test",
            b"extra",
        )
        .unwrap();

        let bytes = serialize_proof(&proof).unwrap();
        let proof2 = deserialize_proof(&bytes).unwrap();

        // Verify with the same parameters.
        let commitment = gens.h[4] * Scalar::from(value).0 + gens.h[0] * blinding.0;
        verify_range(
            &proof2,
            commitment,
            32,
            gens.h[4],
            gens.h[0],
            b"ACT:Test",
            b"extra",
        )
        .unwrap();
    }
}
