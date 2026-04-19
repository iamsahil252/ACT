//! # Anonymous Credit Tokens (ACT)
//!
//! A privacy‑preserving, rate‑limited credential system for subscription‑based
//! services. This crate implements the full ACT protocol as specified in the
//! accompanying paper, including:
//!
//! - Blind issuance of Master Tokens (BBS+ signatures).
//! - Epoch‑bound Daily Tokens derived via zero‑knowledge proofs.
//! - Intra‑day partial spending with refund tokens.
//! - Unlinkable epoch nullifiers for cross‑epoch privacy.
//!
//! ## Features
//!
//! - `server`: Enables server‑side components (Redis integration, async handlers).
//! - `default`: Client‑only functionality.
//!
//! ## Example
//!
//! ```no_run
//! use act::{Generators, ServerKeys, Scalar};
//! use act::master_mint::{MasterMintClient, MasterMintServer};
//! use act::hash::compute_h_ctx;
//! use rand::thread_rng;
//!
//! let mut rng = thread_rng();
//! let generators = Generators::new();
//! let keys = ServerKeys::generate(&mut rng);
//! let h_ctx = compute_h_ctx("my-app", &keys.pk_master, &keys.pk_daily, &generators);
//!
//! // Client requests a Master Token
//! let (client, request) = MasterMintClient::begin(&mut rng, 100, 5000, &generators, h_ctx);
//! // Server issues blind signature
//! let (a_sub, e_sub, s_prime) = MasterMintServer::issue(
//!     &mut rng, &request, 100, 5000, &generators, &keys, h_ctx
//! ).unwrap();
//! let master_token = client.finalize(a_sub, e_sub, s_prime);
//! ```
//!
//! ## Security
//!
//! The implementation adheres strictly to the specification:
//! - Canonical scalar serialization with modulus checks.
//! - Subgroup validation on all deserialized group elements.
//! - Domain‑separated hashing via `H_ctx`.
//! - Constant‑time operations where possible.

#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_code)]
#![warn(missing_docs, rust_2018_idioms)]
#![cfg_attr(not(feature = "std"), no_std)]
#[cfg(feature = "std")]
extern crate std;

extern crate alloc;
// Re-export arkworks types for convenience
pub use ark_bls12_381::{Fr, G1Projective, G2Projective};
pub use ark_ec::CurveGroup;
pub use ark_ff::PrimeField;

// Core modules
pub mod error;
pub mod types;
pub mod hash;
pub mod setup;
pub mod commitments;
pub mod bbs_proof;
pub mod bulletproofs;

// Protocol phases
pub mod master_mint;
pub mod epoch_refresh;
pub mod spend;

// Server components (feature-gated)
#[cfg(feature = "server")]
pub mod server;

// Re-export key types and functions for user convenience
pub use error::{ActError, Result};
pub use types::{CompressedG1, CompressedG2, Scalar, HexScalar, HexG1, HexG2};
pub use setup::{Generators, ServerKeys};
pub use bbs_proof::{BbsProof, BbsSignature};
pub use hash::{compute_h_ctx, hash_to_g1, hash_to_scalar};
pub use commitments::{commit, verify_bridge, verify_bridge_single_base};
pub use master_mint::{MasterMintClient, MasterMintRequest, MasterMintServer, ProofOfKnowledge};
pub use epoch_refresh::{RefreshProof, RefreshResponse, RefreshProver, verify_refresh};
pub use spend::{SpendProof, SpendResponse, SpendProver, verify_spend};

/// The current version of the ACT protocol implementation.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The number of message generators available (h1..h3 for messages, plus h0 for randomness).
pub const MESSAGE_GENERATOR_COUNT: usize = 3;

/// The bit length used for all Bulletproofs range proofs (32 bits).
pub const RANGE_PROOF_BITS: usize = 32;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::thread_rng;

    #[test]
    fn end_to_end_flow() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("e2e-test", &keys.pk_master, &keys.pk_daily, &generators);

        // 1. Master Mint
        let (mint_client, mint_req) = MasterMintClient::begin(&mut rng, 100, 5000, &generators, h_ctx);
        let (a_sub, e_sub, s_prime) = MasterMintServer::issue(
            &mut rng, &mint_req, 100, 5000, &generators, &keys, h_ctx
        ).unwrap();
        let master_sig = mint_client.finalize(a_sub, e_sub, s_prime);
        let k_sub = mint_client.k_sub;

        // 2. Epoch Refresh
        let current_epoch = 1000u32;
        let (refresh_client, refresh_proof) = RefreshProver::prove(
            &mut rng,
            &master_sig,
            k_sub,
            100,
            5000,
            current_epoch,
            &generators,
            &keys.pk_master,
            h_ctx,
        ).unwrap();
        let refresh_resp = verify_refresh(
            &refresh_proof,
            current_epoch,
            &generators,
            &keys.pk_master,
            &keys,
            h_ctx,
            &mut rng,
        ).unwrap();
        let (daily_sig, k_daily) = refresh_client.finalize(refresh_resp);

        // 3. Spend
        let spend_amount = 30u32;
        let nonce = [0x42u8; 16];
        let (spend_client, spend_proof) = SpendProver::prove(
            &mut rng,
            &daily_sig,
            k_daily,
            100,
            current_epoch,
            spend_amount,
            &nonce,
            &generators,
            &keys.pk_daily,
            h_ctx,
        ).unwrap();
        let spend_resp = verify_spend(
            &spend_proof,
            current_epoch,
            &nonce,
            &generators,
            &keys.pk_daily,
            &keys,
            h_ctx,
            &mut rng,
        ).unwrap();

        // Finalize refund token
        let s_refund = spend_client.r_star + spend_resp.s_prime_refund;
        let refund_sig = BbsSignature {
            a: spend_resp.a_refund,
            e: spend_resp.e_refund,
            s: s_refund,
        };
        assert!(!refund_sig.a.is_zero());
    }
}
