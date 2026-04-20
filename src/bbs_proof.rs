//! Multiplicative BBS+ Zero-Knowledge Proof of Possession (Protocol 1).

extern crate alloc;
use alloc::format;
use alloc::vec::Vec;

use blstrs::{Bls12, G1Affine, G1Projective, G2Affine, G2Projective, Gt};
use ff::Field as _;
use group::Group as _;
use pairing::{MultiMillerLoop as _, MillerLoopResult as _};
use rand_core::RngCore;
use sha2::{Digest as _, Sha256};
use std::io::Write as _;

use crate::error::{ActError, Result};
use crate::hash::{hash_to_scalar_from_hasher, write_g1, write_g2, write_scalar, HasherWriter};
use crate::msm::g1_msm;
use crate::setup::Generators;
use crate::types::Scalar;

/// A BBS+ signature.
#[derive(Clone, Debug)]
pub struct BbsSignature {
    pub a: G1Projective,
    pub e: Scalar,
    pub s: Scalar,
}

/// The multiplicative BBS+ proof of knowledge.
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

/// Internal state generated during proof creation, needed by bridging layers.
#[derive(Clone, Debug)]
pub struct BbsProofContext {
    pub r1: Scalar,
    pub s_tilde: Scalar,
    pub m_tilde: Vec<Scalar>,
}

impl BbsProof {
    /// Generate a zero-knowledge proof of BBS+ signature possession.
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
        assert!(l <= 3, "ACT supports at most 3 messages");

        // ── 1. Randomization ────────────────────────────────────────────────
        let r1 = Scalar::rand_nonzero(rng);
        let a_prime = &sig.a * &r1.0;

        // M = g1 * h0^s * ∏ h_i^{m_i}
        let mut bases: Vec<G1Affine> = Vec::with_capacity(2 + l);
        let mut scalars = Vec::with_capacity(2 + l);
        bases.push(generators.g1_affine);
        scalars.push(Scalar::ONE.0);
        bases.push(generators.h_affine[0]);
        scalars.push(sig.s.0);
        for i in 0..l {
            bases.push(generators.h_affine[i + 1]);
            scalars.push(messages[i].0);
        }
        let msg_part = g1_msm(&bases, &scalars);

        // A_bar = A'^{-e} * M^{r1}
        let a_bar = &(&a_prime * &(-sig.e.0)) + &(&msg_part * &r1.0);

        let s_tilde = sig.s * r1;
        let m_tilde: Vec<Scalar> = messages.iter().map(|m| *m * r1).collect();

        // ── 2. Commitments ───────────────────────────────────────────────────
        let rho_e      = Scalar::rand(rng);
        let rho_r1     = Scalar::rand(rng);
        let rho_s_tilde = Scalar::rand(rng);
        let rho_m_tilde: Vec<Scalar> = (0..l).map(|_| Scalar::rand(rng)).collect();

        // T_BBS = A'^{-ρ_e} * g1^{ρ_r1} * h0^{ρ_s_tilde} * ∏ h_i^{ρ_m_tilde[i]}
        let mut t_bases: Vec<G1Affine> = Vec::with_capacity(3 + l);
        let mut t_scalars = Vec::with_capacity(3 + l);
        t_bases.push(G1Affine::from(a_prime));
        t_scalars.push((-rho_e).0);
        t_bases.push(generators.g1_affine);
        t_scalars.push(rho_r1.0);
        t_bases.push(generators.h_affine[0]);
        t_scalars.push(rho_s_tilde.0);
        for i in 0..l {
            t_bases.push(generators.h_affine[i + 1]);
            t_scalars.push(rho_m_tilde[i].0);
        }
        let t_bbs = g1_msm(&t_bases, &t_scalars);

        // ── 3. Challenge ─────────────────────────────────────────────────────
        let c = Self::compute_challenge(h_ctx, pk, &a_prime, &a_bar, &t_bbs, messages, disclosed, aux);

        // ── 4. Responses ─────────────────────────────────────────────────────
        let z_e      = rho_e + c * sig.e;
        let z_r1     = rho_r1 + c * r1;
        let z_s_tilde = rho_s_tilde + c * s_tilde;
        let z_m_tilde: Vec<Scalar> = rho_m_tilde
            .iter()
            .zip(m_tilde.iter())
            .map(|(rho, m)| *rho + c * *m)
            .collect();

        Ok((
            Self { a_prime, a_bar, t_bbs, z_e, z_r1, z_s_tilde, z_m_tilde },
            BbsProofContext { r1, s_tilde, m_tilde },
        ))
    }

    /// Verify the BBS+ proof.
    pub fn verify(
        &self,
        generators: &Generators,
        pk: &G2Projective,
        disclosed_messages: &[Option<Scalar>],
        h_ctx: Scalar,
        aux: &[u8],
    ) -> Result<()> {
        let l = disclosed_messages.len();
        if l > 3 {
            return Err(ActError::VerificationFailed("Too many messages (max 3)".into()));
        }

        if bool::from(self.a_prime.is_identity()) {
            return Err(ActError::VerificationFailed("A' is the point at infinity".into()));
        }
        if bool::from(self.t_bbs.is_identity()) {
            return Err(ActError::VerificationFailed("T_BBS is the point at infinity".into()));
        }

        let messages_for_challenge: Vec<Scalar> = disclosed_messages
            .iter()
            .map(|opt| opt.unwrap_or(Scalar::ZERO))
            .collect();
        let disclosed_mask: Vec<bool> = disclosed_messages.iter().map(Option::is_some).collect();

        let c = Self::compute_challenge(
            h_ctx, pk, &self.a_prime, &self.a_bar, &self.t_bbs,
            &messages_for_challenge, &disclosed_mask, aux,
        );

        // ── Pairing check: e(A', pk) * e(-A_bar, g2) == 1 ──────────────────
        let a_prime_aff = G1Affine::from(self.a_prime);
        let a_bar_neg_aff = G1Affine::from(-self.a_bar);
        let pk_aff  = G2Affine::from(*pk);
        let g2_aff  = G2Affine::from(generators.g2);
        let pk_prep = blstrs::G2Prepared::from(pk_aff);
        let g2_prep = blstrs::G2Prepared::from(g2_aff);

        let pairing_result = Bls12::multi_miller_loop(&[
            (&a_prime_aff, &pk_prep),
            (&a_bar_neg_aff, &g2_prep),
        ])
        .final_exponentiation();
        if pairing_result != Gt::identity() {
            return Err(ActError::VerificationFailed("Pairing check failed".into()));
        }

        // ── Schnorr MSM check ────────────────────────────────────────────────
        // LHS = A'^{-z_e} * g1^{z_r1} * h0^{z_s_tilde} * ∏ h_i^{z_m_tilde[i]}
        let mut lhs_bases: Vec<G1Affine> = Vec::with_capacity(3 + l);
        let mut lhs_scalars = Vec::with_capacity(3 + l);
        lhs_bases.push(G1Affine::from(self.a_prime));
        lhs_scalars.push((-self.z_e).0);
        lhs_bases.push(generators.g1_affine);
        lhs_scalars.push(self.z_r1.0);
        lhs_bases.push(generators.h_affine[0]);
        lhs_scalars.push(self.z_s_tilde.0);
        for i in 0..l {
            lhs_bases.push(generators.h_affine[i + 1]);
            lhs_scalars.push(self.z_m_tilde[i].0);
        }
        let lhs = g1_msm(&lhs_bases, &lhs_scalars);

        // RHS = T_BBS + A_bar^c
        let rhs = &self.t_bbs + &(&self.a_bar * &c.0);

        if lhs != rhs {
            return Err(ActError::VerificationFailed("Schnorr equation check failed".into()));
        }
        Ok(())
    }

    /// Fiat–Shamir challenge computation.
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
        let mut hasher = Sha256::new();
        let mut w = HasherWriter(&mut hasher);
        write_scalar(&mut w, h_ctx);
        write_g2(&mut w, *pk);
        write_g1(&mut w, *a_prime);
        write_g1(&mut w, *a_bar);
        write_g1(&mut w, *t_bbs);
        for (i, &disc) in disclosed.iter().enumerate() {
            if disc {
                write_scalar(&mut w, messages[i]);
            }
        }
        w.write_all(aux).unwrap();
        drop(w);
        hash_to_scalar_from_hasher(hasher)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::compute_h_ctx;
    use crate::setup::ServerKeys;
    use rand::thread_rng;

    fn make_sig(
        rng: &mut impl RngCore,
        generators: &Generators,
        keys: &ServerKeys,
        messages: &[Scalar],
    ) -> BbsSignature {
        let e = Scalar::rand(rng);
        let s = Scalar::rand(rng);
        let mut bases = vec![generators.g1_affine];
        let mut scalars = vec![Scalar::ONE.0];
        bases.push(generators.h_affine[0]);
        scalars.push(s.0);
        for (i, m) in messages.iter().enumerate() {
            bases.push(generators.h_affine[i + 1]);
            scalars.push(m.0);
        }
        let msg_part = g1_msm(&bases, &scalars);
        let denom = e + keys.sk_master;
        let a = &msg_part * &denom.inverse().0;
        BbsSignature { a, e, s }
    }

    #[test]
    fn bbs_proof_roundtrip() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let messages = vec![Scalar::from(42u64), Scalar::from(12345u64), Scalar::from(99999u64)];
        let sig = make_sig(&mut rng, &generators, &keys, &messages);
        let h_ctx = compute_h_ctx("test-app", &keys.pk_master, &keys.pk_daily, &generators);

        let (proof, _ctx) = BbsProof::prove(
            &mut rng, &generators, &keys.pk_master, &sig,
            &messages, &[false, false, false], h_ctx, b"test",
        ).unwrap();
        proof.verify(&generators, &keys.pk_master, &[None, None, None], h_ctx, b"test").unwrap();

        let (proof2, _) = BbsProof::prove(
            &mut rng, &generators, &keys.pk_master, &sig,
            &messages, &[true, false, true], h_ctx, b"test",
        ).unwrap();
        let disclosed = vec![Some(messages[0]), None, Some(messages[2])];
        proof2.verify(&generators, &keys.pk_master, &disclosed, h_ctx, b"test").unwrap();

        let result = proof2.verify(&generators, &keys.pk_master, &disclosed, h_ctx, b"wrong");
        assert!(result.is_err());
    }
}
