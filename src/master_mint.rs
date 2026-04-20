//! Phase 1: Master Subscription Minting.

extern crate alloc;

use blstrs::{G1Affine, G1Projective};
use group::Group as _;
use rand_core::RngCore;
use sha2::{Digest as _, Sha256};
use std::io::Write as _;

use crate::bbs_proof::BbsSignature;
use crate::commitments::commit;
use crate::error::{ActError, Result};
use crate::hash::{hash_to_scalar_from_hasher, write_g1, write_scalar, HasherWriter};
use crate::msm::g1_msm;
use crate::setup::{Generators, ServerKeys};
use crate::types::Scalar;

// ============================================================================
// Client
// ============================================================================

/// The client's request for a Master Token.
#[derive(Clone, Debug)]
pub struct MasterMintRequest {
    /// `K_sub = k_sub·h1 + r_sub·h0`
    pub k_sub_commit: G1Projective,
    /// Schnorr proof of knowledge of the opening.
    pub pok: ProofOfKnowledge,
}

/// Schnorr proof of knowledge of `(k_sub, r_sub)` s.t. `K_sub = k_sub·h1 + r_sub·h0`.
#[derive(Clone, Debug)]
pub struct ProofOfKnowledge {
    pub t: G1Projective,
    pub s_k: Scalar,
    pub s_r: Scalar,
}

impl ProofOfKnowledge {
    pub fn prove(
        rng: &mut impl RngCore,
        k_sub: Scalar,
        r_sub: Scalar,
        k_sub_commit: G1Projective,
        generators: &Generators,
        h_ctx: Scalar,
    ) -> Self {
        let alpha = Scalar::rand(rng);
        let beta  = Scalar::rand(rng);

        let t = g1_msm(
            &[generators.h_affine[1], generators.h_affine[0]],
            &[alpha.0, beta.0],
        );

        let c = Self::challenge(h_ctx, k_sub_commit, t);
        let s_k = alpha + c * k_sub;
        let s_r = beta  + c * r_sub;
        Self { t, s_k, s_r }
    }

    pub fn verify(&self, k_sub_commit: G1Projective, generators: &Generators, h_ctx: Scalar) -> Result<()> {
        let c = Self::challenge(h_ctx, k_sub_commit, self.t);

        let lhs = g1_msm(
            &[generators.h_affine[1], generators.h_affine[0]],
            &[self.s_k.0, self.s_r.0],
        );
        let rhs = &self.t + &(&k_sub_commit * &c.0);

        if lhs != rhs {
            return Err(ActError::VerificationFailed("PoK verification failed".into()));
        }
        Ok(())
    }

    fn challenge(h_ctx: Scalar, k_sub_commit: G1Projective, t: G1Projective) -> Scalar {
        let mut hasher = Sha256::new();
        let mut w = HasherWriter(&mut hasher);
        write_scalar(&mut w, h_ctx);
        write_g1(&mut w, k_sub_commit);
        write_g1(&mut w, t);
        w.write_all(b"PoK:MasterSecret").unwrap();
        drop(w);
        hash_to_scalar_from_hasher(hasher)
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
        let pok = ProofOfKnowledge::prove(rng, k_sub, r_sub, k_sub_commit, generators, h_ctx);
        (
            Self { k_sub, r_sub, c_max, e_max },
            MasterMintRequest { k_sub_commit, pok },
        )
    }

    pub fn finalize(self, a_sub: G1Projective, e_sub: Scalar, s_prime_sub: Scalar) -> BbsSignature {
        BbsSignature { a: a_sub, e: e_sub, s: self.r_sub + s_prime_sub }
    }
}

// ============================================================================
// Server
// ============================================================================

pub struct MasterMintServer;

impl MasterMintServer {
    /// Process a mint request and issue a blind BBS+ signature.
    pub fn issue(
        rng: &mut impl RngCore,
        request: &MasterMintRequest,
        c_max: u32,
        e_max: u32,
        generators: &Generators,
        keys: &ServerKeys,
        h_ctx: Scalar,
    ) -> Result<(G1Projective, Scalar, Scalar)> {
        request.pok.verify(request.k_sub_commit, generators, h_ctx)?;

        if c_max == 0 {
            return Err(ActError::ProtocolError("c_max must be positive".into()));
        }

        let e_sub       = Scalar::rand(rng);
        let s_prime_sub = Scalar::rand(rng);

        let k_sub_aff = G1Affine::from(request.k_sub_commit);
        let bases  = [
            generators.g1_affine,
            k_sub_aff,
            generators.h_affine[0],
            generators.h_affine[2],
            generators.h_affine[3],
        ];
        let scalars = [
            Scalar::ONE.0,
            Scalar::ONE.0,
            s_prime_sub.0,
            Scalar::from(c_max).0,
            Scalar::from(e_max).0,
        ];
        let msg_part = g1_msm(&bases, &scalars);

        let denom = e_sub + keys.sk_master;
        if denom.is_zero() {
            return Err(ActError::ProtocolError("Division by zero".into()));
        }
        let denom_inv = denom.inverse();
        let a_sub = &msg_part * &denom_inv.0;

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
    use group::Group as _;
    use rand::thread_rng;

    #[test]
    fn master_mint_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);

        let (client, request) = MasterMintClient::begin(&mut rng, 100, 12345, &generators, h_ctx);
        let (a_sub, e_sub, s_prime) = MasterMintServer::issue(
            &mut rng, &request, 100, 12345, &generators, &keys, h_ctx,
        ).unwrap();
        let master_sig = client.finalize(a_sub, e_sub, s_prime);
        assert!(!bool::from(master_sig.a.is_identity()));
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
        let pok = ProofOfKnowledge::prove(&mut rng, k_sub, r_sub, k_sub_commit, &generators, h_ctx);
        assert!(pok.verify(k_sub_commit, &generators, h_ctx).is_ok());
        let wrong = &generators.h[1] * &Scalar::from(999u64).0;
        assert!(pok.verify(wrong, &generators, h_ctx).is_err());
    }

    #[test]
    fn server_rejects_invalid_pok() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = Scalar::rand(&mut rng);
        let bad_request = MasterMintRequest {
            k_sub_commit: &generators.h[1] * &Scalar::from(42u64).0,
            pok: ProofOfKnowledge {
                t: generators.g1,
                s_k: Scalar::ZERO,
                s_r: Scalar::ZERO,
            },
        };
        assert!(MasterMintServer::issue(&mut rng, &bad_request, 100, 1000, &generators, &keys, h_ctx).is_err());
    }
}
