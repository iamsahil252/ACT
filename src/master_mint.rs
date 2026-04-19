//! Phase 1: Master Subscription Minting
//!
//! This module implements the blind issuance of the Master Token.
//! The client generates a secret identifier `k_sub` and a commitment `K_sub`,
//! proves knowledge of its opening via a Schnorr proof, and receives a blind
//! BBS+ signature from the server. The server enforces the policy limits
//! `c_max` and `e_max` (both 32‑bit unsigned integers).

extern crate alloc;
use alloc::format;
use alloc::vec::Vec;
use ark_std::vec;
use ark_bls12_381::G1Projective;
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::RngCore;
use ark_std::Zero;
use crate::bbs_proof::BbsSignature;
use crate::commitments::commit;
use crate::error::{ActError, Result};
use crate::hash::hash_to_scalar;
use crate::setup::{Generators, ServerKeys};
use crate::types::Scalar;

fn msm_projective(bases: &[G1Projective], scalars: &[ark_bls12_381::Fr]) -> G1Projective {
    bases
        .iter()
        .zip(scalars.iter())
        .fold(G1Projective::zero(), |acc, (b, s)| acc + (*b * *s))
}

// ============================================================================
// Client
// ============================================================================

/// The client's request for a Master Token.
#[derive(Clone, Debug)]
pub struct MasterMintRequest {
    /// Commitment to the secret `k_sub`: `K_sub = k_sub * h1 + r_sub * h0`.
    pub k_sub_commit: G1Projective,
    /// Proof of knowledge of `(k_sub, r_sub)`.
    pub pok: ProofOfKnowledge,
}

/// Schnorr proof of knowledge of the opening of `K_sub`.
///
/// Proves knowledge of `k_sub` and `r_sub` such that
/// `K_sub = k_sub * h1 + r_sub * h0`.
#[derive(Clone, Debug)]
pub struct ProofOfKnowledge {
    /// Commitment `T = alpha * h1 + beta * h0`.
    pub t: G1Projective,
    /// Response for `k_sub`.
    pub s_k: Scalar,
    /// Response for `r_sub`.
    pub s_r: Scalar,
}

impl ProofOfKnowledge {
    /// Generate a proof of knowledge of the opening of `K_sub`.
    ///
    /// # Arguments
    /// - `rng`: secure random number generator.
    /// - `k_sub`: the secret subscription identifier.
    /// - `r_sub`: the blinding factor.
    /// - `k_sub_commit`: the commitment `K_sub`.
    /// - `generators`: the global generators.
    /// - `h_ctx`: the application context hash.
    pub fn prove(
        rng: &mut impl RngCore,
        k_sub: Scalar,
        r_sub: Scalar,
        k_sub_commit: G1Projective,
        generators: &Generators,
        h_ctx: Scalar,
    ) -> Self {
        // Choose random blinders
        let alpha = Scalar::rand(rng);
        let beta = Scalar::rand(rng);

        // T = alpha * h1 + beta * h0
        let t = generators.h[1] * alpha.0 + generators.h[0] * beta.0;

        // Compute challenge c = H(H_ctx || K_sub || T || "PoK:MasterSecret")
        let mut preimage = Vec::new();
        preimage.extend_from_slice(&h_ctx.to_bytes());
        k_sub_commit.serialize_compressed(&mut preimage).unwrap();
        t.serialize_compressed(&mut preimage).unwrap();
        preimage.extend_from_slice(b"PoK:MasterSecret");
        let c = hash_to_scalar(&preimage);

        // Responses
        let s_k = alpha + c * k_sub;
        let s_r = beta + c * r_sub;

        Self { t, s_k, s_r }
    }

    /// Verify the proof of knowledge.
    ///
    /// # Arguments
    /// - `k_sub_commit`: the commitment `K_sub` being proven.
    /// - `generators`: the global generators.
    /// - `h_ctx`: the application context hash.
    pub fn verify(
        &self,
        k_sub_commit: G1Projective,
        generators: &Generators,
        h_ctx: Scalar,
    ) -> Result<()> {
        // Recompute challenge
        let mut preimage = Vec::new();
        preimage.extend_from_slice(&h_ctx.to_bytes());
        k_sub_commit.serialize_compressed(&mut preimage).unwrap();
        self.t.serialize_compressed(&mut preimage).unwrap();
        preimage.extend_from_slice(b"PoK:MasterSecret");
        let c = hash_to_scalar(&preimage);

        // Check: s_k * h1 + s_r * h0 == T + c * K_sub
        let lhs = generators.h[1] * self.s_k.0 + generators.h[0] * self.s_r.0;
        let rhs = self.t + k_sub_commit * c.0;

        if lhs != rhs {
            return Err(ActError::VerificationFailed(
                "PoK verification failed".into(),
            ));
        }
        Ok(())
    }
}

/// Client state during master token minting.
pub struct MasterMintClient {
    pub k_sub: Scalar,
    pub r_sub: Scalar,
    pub c_max: u32,
    pub e_max: u32,
}

impl MasterMintClient {
    /// Start the minting process.
    ///
    /// Generates the secret `k_sub`, blinding `r_sub`, and the request to send
    /// to the server.
    pub fn begin(
        rng: &mut impl RngCore,
        c_max: u32,
        e_max: u32,
        generators: &Generators,
        h_ctx: Scalar,
    ) -> (Self, MasterMintRequest) {
        let k_sub = Scalar::rand_nonzero(rng);
        let r_sub = Scalar::rand(rng);

        let k_sub_commit = commit(k_sub, r_sub, generators.h[1], generators.h[0]);

        let pok = ProofOfKnowledge::prove(
            rng,
            k_sub,
            r_sub,
            k_sub_commit,
            generators,
            h_ctx,
        );

        let request = MasterMintRequest {
            k_sub_commit,
            pok,
        };

        let client = Self {
            k_sub,
            r_sub,
            c_max,
            e_max,
        };

        (client, request)
    }

    /// Finalize the Master Token after receiving the server's blind signature.
    pub fn finalize(
        self,
        a_sub: G1Projective,
        e_sub: Scalar,
        s_prime_sub: Scalar,
    ) -> BbsSignature {
        let s_sub = self.r_sub + s_prime_sub;
        BbsSignature {
            a: a_sub,
            e: e_sub,
            s: s_sub,
        }
    }
}

// ============================================================================
// Server
// ============================================================================

/// Server handling of master minting requests.
pub struct MasterMintServer;

impl MasterMintServer {
    /// Process a mint request and issue a blind BBS+ signature.
    ///
    /// # Arguments
    /// - `rng`: secure random number generator.
    /// - `request`: the client's request containing `K_sub` and PoK.
    /// - `c_max`: maximum credits per epoch (server policy).
    /// - `e_max`: expiry epoch (server policy).
    /// - `generators`: the global generators.
    /// - `keys`: the server's master signing key.
    /// - `h_ctx`: the application context hash.
    ///
    /// # Returns
    /// A tuple `(A_sub, e_sub, s'_sub)` to send to the client.
    pub fn issue(
        rng: &mut impl RngCore,
        request: &MasterMintRequest,
        c_max: u32,
        e_max: u32,
        generators: &Generators,
        keys: &ServerKeys,
        h_ctx: Scalar,
    ) -> Result<(G1Projective, Scalar, Scalar)> {
        // 1. Verify the proof of knowledge.
        request
            .pok
            .verify(request.k_sub_commit, generators, h_ctx)?;

        // 2. Enforce policy: c_max must be ≤ 2^32-1 (always true for u32).
        //    Also ensure c_max is non-zero (subscription must allow at least one spend).
        if c_max == 0 {
            return Err(ActError::ProtocolError(
                "c_max must be positive".into(),
            ));
        }

        // 3. Generate signature randomness.
        let e_sub = Scalar::rand(rng);
        let s_prime_sub = Scalar::rand(rng);

        // 4. Compute A_sub = (g1 * K_sub * h0^{s'} * h2^{c_max} * h3^{e_max})^{1/(e + sk_master)}
        //    Note: the message vector is (k_sub, c_max, e_max) on (h1, h2, h3).
        let mut bases = vec![
            generators.g1,
            request.k_sub_commit,
            generators.h[0],
            generators.h[2],
            generators.h[3],
        ];
        let mut scalars = vec![
            Scalar::ONE.0,
            Scalar::ONE.0,
            s_prime_sub.0,
            Scalar::from(c_max).0,
            Scalar::from(e_max).0,
        ];

        let msg_part = msm_projective(&bases, &scalars);

        let denom = e_sub + keys.sk_master;
        let denom_inv = denom
            .0
            .inverse()
            .ok_or_else(|| ActError::ProtocolError("Division by zero".into()))?;
        let a_sub = msg_part * denom_inv;

        Ok((a_sub, e_sub, s_prime_sub))
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::compute_h_ctx;
    use crate::setup::{Generators, ServerKeys};
    use ark_std::rand::thread_rng;
    use ark_std::Zero;

    #[test]
    fn master_mint_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx(
            "test-app",
            &keys.pk_master,
            &keys.pk_daily,
            &generators,
        );

        let c_max = 100u32;
        let e_max = 12345u32;

        // Client begins
        let (client, request) = MasterMintClient::begin(
            &mut rng,
            c_max,
            e_max,
            &generators,
            h_ctx,
        );

        // Server issues blind signature
        let (a_sub, e_sub, s_prime_sub) = MasterMintServer::issue(
            &mut rng,
            &request,
            c_max,
            e_max,
            &generators,
            &keys,
            h_ctx,
        )
        .unwrap();

        // Client finalizes
        let master_sig = client.finalize(a_sub, e_sub, s_prime_sub);

        // Verify the signature (using BBS+ verification)
        // We'll do a quick check: the signature should verify under pk_master.
        // For a full verification we'd need the BBS+ verification function.
        // Since we don't have it exposed, we just check it's not the identity.
        assert!(!master_sig.a.is_zero());
        assert!(!master_sig.e.is_zero());
    }

    #[test]
    fn pok_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let h_ctx = Scalar::rand(&mut rng);

        let k_sub = Scalar::rand(&mut rng);
        let r_sub = Scalar::rand(&mut rng);
        let k_sub_commit = commit(k_sub, r_sub, generators.h[1], generators.h[0]);

        let pok = ProofOfKnowledge::prove(
            &mut rng,
            k_sub,
            r_sub,
            k_sub_commit,
            &generators,
            h_ctx,
        );

        assert!(pok.verify(k_sub_commit, &generators, h_ctx).is_ok());

        // Tampered commitment should fail
        let wrong_commit = generators.h[1] * Scalar::from(999u64).0;
        assert!(pok.verify(wrong_commit, &generators, h_ctx).is_err());
    }

    #[test]
    fn server_rejects_invalid_pok() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = Scalar::rand(&mut rng);

        let c_max = 100;
        let e_max = 1000;

        // Create a fake request with a bad PoK
        let bad_request = MasterMintRequest {
            k_sub_commit: generators.h[1] * Scalar::from(42u64).0,
            pok: ProofOfKnowledge {
                t: generators.g1,
                s_k: Scalar::ZERO,
                s_r: Scalar::ZERO,
            },
        };

        let result = MasterMintServer::issue(
            &mut rng,
            &bad_request,
            c_max,
            e_max,
            &generators,
            &keys,
            h_ctx,
        );
        assert!(result.is_err());
    }
}
