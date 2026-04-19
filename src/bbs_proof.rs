//! Multiplicative BBS+ Zero‑Knowledge Proof of Possession (Protocol 1)
//!
//! This module implements a non‑interactive zero‑knowledge proof that the prover
//! holds a valid BBS+ signature on a set of messages, without revealing the
//! signature or the hidden messages. The proof is constructed using the
//! multiplicative randomization technique described in Section 2.4 of the ACT
//! specification.
//!
//! # Security
//! - The proof is sound under the q‑SDH and DL assumptions in the random oracle
//!   model.
//! - Zero‑knowledge is achieved by randomization of the signature and the use of
//!   fresh blinding factors.
//! - All challenges are bound to the application context hash `H_ctx` and
//!   include all public parameters to prevent cross‑deployment replay.
extern crate alloc;
use alloc::format;
use alloc::vec::Vec;
use ark_std::vec;
use ark_bls12_381::{Fr, G1Projective, G2Projective};
use ark_ec::{pairing::Pairing, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::RngCore;
use crate::error::{ActError, Result};
use crate::hash::hash_to_scalar;
use crate::setup::Generators;
use crate::types::Scalar;

fn msm_projective(bases: &[G1Projective], scalars: &[Fr]) -> G1Projective {
    bases
        .iter()
        .zip(scalars.iter())
        .fold(G1Projective::zero(), |acc, (b, s)| acc + (*b * *s))
}

/// A BBS+ signature.
#[derive(Clone, Debug)]
pub struct BbsSignature {
    pub a: G1Projective,
    pub e: Scalar,
    pub s: Scalar,
}

/// The multiplicative BBS+ proof of knowledge.
///
/// The proof contains the randomized signature components `a_prime` and `a_bar`,
/// the commitment `t_bbs`, and the responses to the Fiat–Shamir challenge.
#[derive(Clone, Debug)]
pub struct BbsProof {
    pub a_prime: G1Projective,
    pub a_bar: G1Projective,
    pub t_bbs: G1Projective,
    pub z_e: Scalar,
    pub z_r1: Scalar,
    pub z_s_tilde: Scalar,
    pub z_m_tilde: Vec<Scalar>,
}

/// Internal state generated during proof creation, required for external
/// bridging operations in the refresh and spend phases.
#[derive(Clone, Debug)]
pub struct BbsProofContext {
    /// The randomization scalar `r1`.
    pub r1: Scalar,
    /// The scaled signature randomness: `s_tilde = s * r1`.
    pub s_tilde: Scalar,
    /// The scaled hidden messages: `m_tilde[i] = m[i] * r1`.
    pub m_tilde: Vec<Scalar>,
}

impl BbsProof {
    /// Generate a zero‑knowledge proof of possession of a BBS+ signature.
    ///
    /// # Arguments
    /// - `rng`: cryptographically secure random number generator.
    /// - `generators`: the global BBS+ generators (g1, h0..h4).
    /// - `pk`: the signer's public key (a point in G2).
    /// - `sig`: the BBS+ signature on the messages.
    /// - `messages`: all messages in the order they were signed.
    /// - `disclosed`: a boolean mask indicating which messages are revealed.
    /// - `h_ctx`: the application context hash (see Section 3).
    /// - `aux`: additional public data to bind into the challenge (e.g., epoch,
    ///   commitments, nonces).
    ///
    /// # Returns
    /// A tuple containing the proof and the internal context needed for external
    /// bridging.
    ///
    /// # Panics
    /// Panics if the length of `messages` or `disclosed` exceeds the number of
    /// available generators (currently 3 message generators: h1, h2, h3).
    pub fn prove(
        rng: &mut impl RngCore,
        generators: &Generators,
        pk: &G2Projective,
        sig: &BbsSignature,
        messages: &[Scalar],
        disclosed: &[bool],
        h_ctx: Scalar,
        aux: &[u8],
    ) -> Result<(Self, BbsProofContext)> {
        let l = messages.len();
        assert_eq!(disclosed.len(), l, "disclosed mask length mismatch");
        // We have generators h0..h4. h0 is for randomness s, h1..h3 for messages.
        // The specification uses up to L=3 messages. We enforce this.
        assert!(l <= 3, "ACT supports at most 3 messages (h1, h2, h3)");

        // ---------- 1. Randomization ----------
        let r1 = Scalar::rand_nonzero(rng);
        let a_prime = sig.a * r1.0;

        // Compute the message part: M = g1 * h0^s * ∏_{i=1..L} h_i^{m_i}
        let mut bases = vec![generators.g1, generators.h[0]];
        let mut scalars = vec![Scalar::ONE.0, sig.s.0];
        for i in 0..l {
            bases.push(generators.h[i + 1]);
            scalars.push(messages[i].0);
        }
        let msg_part = msm_projective(&bases, &scalars);

        // A_bar = A'^{-e} * M^{r1}
        let a_bar = a_prime * (-sig.e.0) + msg_part * r1.0;

        // Scaled secrets
        let s_tilde = sig.s * r1;
        let m_tilde: Vec<Scalar> = messages.iter().map(|m| *m * r1).collect();

        // ---------- 2. Commitments ----------
        let rho_e = Scalar::rand(rng);
        let rho_r1 = Scalar::rand(rng);
        let rho_s_tilde = Scalar::rand(rng);
        let rho_m_tilde: Vec<Scalar> = (0..l).map(|_| Scalar::rand(rng)).collect();

        // T_BBS = A'^{-ρ_e} * g1^{ρ_r1} * h0^{ρ_s_tilde} * ∏_{i=1..L} h_i^{ρ_m_tilde[i]}
        let mut t_bases = vec![a_prime.into_affine()];
        let mut t_scalars = vec![-rho_e.0];
        t_bases.push(generators.g1.into_affine());
        t_scalars.push(rho_r1.0);
        t_bases.push(generators.h[0].into_affine());
        t_scalars.push(rho_s_tilde.0);
        for i in 0..l {
            t_bases.push(generators.h[i + 1].into_affine());
            t_scalars.push(rho_m_tilde[i].0);
        }
        let t_bbs = G1Projective::msm(&t_bases, &t_scalars)
            .map_err(|e| ActError::ProtocolError(format!("MSM failed: {:?}", e)))?;

        // ---------- 3. Challenge ----------
        let c = Self::compute_challenge(
            h_ctx,
            pk,
            &a_prime,
            &a_bar,
            &t_bbs,
            messages,
            disclosed,
            aux,
        );

        // ---------- 4. Responses ----------
        let z_e = rho_e + c * sig.e;
        let z_r1 = rho_r1 + c * r1;
        let z_s_tilde = rho_s_tilde + c * s_tilde;
        let z_m_tilde: Vec<Scalar> = rho_m_tilde
            .iter()
            .zip(m_tilde.iter())
            .map(|(rho, m)| *rho + c * *m)
            .collect();

        let proof = Self {
            a_prime,
            a_bar,
            t_bbs,
            z_e,
            z_r1,
            z_s_tilde,
            z_m_tilde,
        };

        let ctx = BbsProofContext {
            r1,
            s_tilde,
            m_tilde,
        };

        Ok((proof, ctx))
    }

    /// Verify the proof.
    ///
    /// # Arguments
    /// - `generators`: the global BBS+ generators.
    /// - `pk`: the signer's public key.
    /// - `disclosed_messages`: an array where `Some(value)` indicates a
    ///   disclosed message and `None` indicates a hidden one. The length must
    ///   match the number of messages in the original signature.
    /// - `h_ctx`: the application context hash.
    /// - `aux`: the same auxiliary data used during proof generation.
    ///
    /// # Returns
    /// `Ok(())` if the proof is valid, otherwise an error.
    pub fn verify(
        &self,
        generators: &Generators,
        pk: &G2Projective,
        disclosed_messages: &[Option<Scalar>],
        h_ctx: Scalar,
        aux: &[u8],
    ) -> Result<()> {
        let l = disclosed_messages.len();
        // We support up to 3 messages.
        if l > 3 {
            return Err(ActError::VerificationFailed(
                "Too many messages (max 3)".into(),
            ));
        }

        // Basic non‑zero checks
        if self.a_prime.is_zero() {
            return Err(ActError::VerificationFailed(
                "A' is the point at infinity".into(),
            ));
        }
        if self.t_bbs.is_zero() {
            return Err(ActError::VerificationFailed(
                "T_BBS is the point at infinity".into(),
            ));
        }

        // Reconstruct the messages array as originally signed (disclosed values are
        // known, hidden are not needed for challenge but we must feed the disclosed
        // ones to the challenge hash).
        let mut messages_for_challenge: Vec<Scalar> = Vec::with_capacity(l);
        for opt in disclosed_messages {
            // For the challenge we only need the disclosed ones, but we pass a full array
            // with placeholders for hidden ones (they won't be hashed). We'll handle this
            // in `compute_challenge`.
            messages_for_challenge.push(opt.unwrap_or(Scalar::ZERO));
        }

        // Recompute challenge
        let c = Self::compute_challenge(
            h_ctx,
            pk,
            &self.a_prime,
            &self.a_bar,
            &self.t_bbs,
            &messages_for_challenge,
            &disclosed_messages.iter().map(Option::is_some).collect::<Vec<_>>(),
            aux,
        );

        // ---------- Pairing check: e(A', pk) == e(A_bar, g2) ----------
        let pairing_left = ark_bls12_381::Bls12_381::pairing(self.a_prime, *pk);
        let pairing_right = ark_bls12_381::Bls12_381::pairing(self.a_bar, generators.g2);
        if pairing_left.0 != pairing_right.0 {
            return Err(ActError::VerificationFailed(
                "Pairing check failed".into(),
            ));
        }

        // ---------- Schnorr MSM check ----------
        // LHS = A'^{-z_e} * g1^{z_r1} * h0^{z_s_tilde} * ∏_{i=1..L} h_i^{z_m_tilde[i]}
        let mut lhs_bases = vec![self.a_prime.into_affine()];
        let mut lhs_scalars = vec![-self.z_e.0];
        lhs_bases.push(generators.g1.into_affine());
        lhs_scalars.push(self.z_r1.0);
        lhs_bases.push(generators.h[0].into_affine());
        lhs_scalars.push(self.z_s_tilde.0);
        for i in 0..l {
            lhs_bases.push(generators.h[i + 1].into_affine());
            lhs_scalars.push(self.z_m_tilde[i].0);
        }
        let lhs = G1Projective::msm(&lhs_bases, &lhs_scalars)
            .map_err(|e| ActError::VerificationFailed(format!("MSM failed: {:?}", e)))?;

        // RHS = T_BBS * A_bar^c
        let rhs = self.t_bbs + self.a_bar * c.0;

        if lhs != rhs {
            return Err(ActError::VerificationFailed(
                "Schnorr equation check failed".into(),
            ));
        }

        Ok(())
    }

    /// Internal helper to compute the Fiat–Shamir challenge.
    fn compute_challenge(
        h_ctx: Scalar,
        pk: &G2Projective,
        a_prime: &G1Projective,
        a_bar: &G1Projective,
        t_bbs: &G1Projective,
        messages: &[Scalar],
        disclosed: &[bool],
        aux: &[u8],
    ) -> Scalar {
        let mut preimage = Vec::new();

        // H_ctx (32 bytes)
        preimage.extend_from_slice(&h_ctx.to_bytes());

        // Public key (compressed)
        pk.serialize_compressed(&mut preimage).unwrap();

        // Proof elements (compressed)
        a_prime.serialize_compressed(&mut preimage).unwrap();
        a_bar.serialize_compressed(&mut preimage).unwrap();
        t_bbs.serialize_compressed(&mut preimage).unwrap();

        // Disclosed messages (only those marked true)
        for (i, &disc) in disclosed.iter().enumerate() {
            if disc {
                messages[i].0.serialize_compressed(&mut preimage).unwrap();
            }
        }

        // Auxiliary data (e.g., epoch, commitments, nonce)
        preimage.extend_from_slice(aux);

        // Domain separation string (optional, but already included via H_ctx)
        // We follow the spec: challenge includes H_ctx and "Refresh"/"Spend" is in aux.

        hash_to_scalar(&preimage)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::thread_rng;
    use crate::hash::compute_h_ctx;
    use crate::setup::{Generators, ServerKeys};

    #[test]
    fn bbs_proof_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);

        // Create a dummy signature on three messages
        let messages = vec![
            Scalar::from(42u64),
            Scalar::from(12345u64),
            Scalar::from(99999u64),
        ];
        let sig = {
            // In real use, the server would sign, but for testing we create a signature
            // manually using the secret key.
            let e = Scalar::rand(&mut rng);
            let s = Scalar::rand(&mut rng);
            let mut bases = vec![generators.g1, generators.h[0]];
            let mut scalars = vec![Scalar::ONE.0, s.0];
            for i in 0..3 {
                bases.push(generators.h[i + 1]);
                scalars.push(messages[i].0);
            }
            let msg_part = msm_projective(&bases, &scalars);
            let denom = e + keys.sk_master;
            let a = msg_part * denom.0.inverse().unwrap();
            BbsSignature { a, e, s }
        };

        let h_ctx = compute_h_ctx(
            "test-app",
            &keys.pk_master,
            &keys.pk_daily,
            &generators,
        );

        // Prove with all messages hidden
        let disclosed = vec![false, false, false];
        let (proof, ctx) = BbsProof::prove(
            &mut rng,
            &generators,
            &keys.pk_master,
            &sig,
            &messages,
            &disclosed,
            h_ctx,
            b"test",
        )
        .unwrap();

        // Verify with all messages hidden
        let disclosed_verify: Vec<Option<Scalar>> = vec![None, None, None];
        proof
            .verify(
                &generators,
                &keys.pk_master,
                &disclosed_verify,
                h_ctx,
                b"test",
            )
            .unwrap();

        // Test with some messages disclosed
        let disclosed = vec![true, false, true];
        let (proof, _) = BbsProof::prove(
            &mut rng,
            &generators,
            &keys.pk_master,
            &sig,
            &messages,
            &disclosed,
            h_ctx,
            b"test",
        )
        .unwrap();

        let disclosed_verify = vec![
            Some(messages[0]),
            None,
            Some(messages[2]),
        ];
        proof
            .verify(
                &generators,
                &keys.pk_master,
                &disclosed_verify,
                h_ctx,
                b"test",
            )
            .unwrap();

        // Tampered aux should fail
        let result = proof.verify(
            &generators,
            &keys.pk_master,
            &disclosed_verify,
            h_ctx,
            b"wrong",
        );
        assert!(result.is_err());
    }
}
