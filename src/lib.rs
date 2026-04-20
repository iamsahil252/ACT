//! # Anonymous Credit Tokens (ACT)
//!
//! Privacy-preserving rate-limited credentials backed by BLS12-381 (blstrs).

#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_code)]
#![warn(missing_docs, rust_2018_idioms)]

#[cfg(feature = "std")]
extern crate std;

// Core modules
pub mod error;
pub mod types;
pub mod hash;
pub mod msm;
pub mod setup;
pub mod commitments;
#[cfg(feature = "std")]
pub mod bbs_proof;
#[cfg(feature = "std")]
pub mod batched_eq;

// Protocol phases
#[cfg(feature = "std")]
pub mod master_mint;
#[cfg(feature = "std")]
pub mod epoch_refresh;
#[cfg(feature = "std")]
pub mod spend;

// Server components (feature-gated)
#[cfg(feature = "server")]
pub mod server;

// Re-export key types and functions
pub use error::{ActError, Result};
pub use types::{CompressedG1, CompressedG2, HexG1, HexG2, HexScalar, Scalar};
pub use setup::{Generators, ServerKeys};
#[cfg(feature = "std")]
pub use bbs_proof::{BbsProof, BbsSignature};
pub use hash::{compute_h_ctx, hash_to_g1, hash_to_scalar};
pub use commitments::{commit, verify_bridge, verify_bridge_single_base};
#[cfg(feature = "std")]
pub use master_mint::{MasterMintClient, MasterMintRequest, MasterMintServer, ProofOfKnowledge};
#[cfg(feature = "std")]
pub use epoch_refresh::{RefreshProof, RefreshProver, RefreshResponse, verify_refresh, verify_refresh_batch};
#[cfg(feature = "std")]
pub use spend::{SpendProof, SpendProver, SpendResponse, verify_spend, verify_spend_batch};

/// The current version of the ACT protocol implementation.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The number of message generators (h1..h3 for messages; h0 for randomness).
pub const MESSAGE_GENERATOR_COUNT: usize = 3;

/// The bit length used for all Bulletproofs range proofs.
pub const RANGE_PROOF_BITS: usize = 32;

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use super::*;
    use group::Group as _;
    use rand::thread_rng;

    #[test]
    fn end_to_end_flow() {
        let mut rng = thread_rng();
        let generators = Generators::new();
        let keys = ServerKeys::generate(&mut rng);
        let h_ctx = compute_h_ctx("e2e-test", &keys.pk_master, &keys.pk_daily, &generators);

        // 1. Master Mint
        let (mint_client, mint_req) = MasterMintClient::begin(&mut rng, 100, 5000, &generators, h_ctx);
        let (a_sub, e_sub, s_prime) = MasterMintServer::issue(
            &mut rng, &mint_req, 100, 5000, &generators, &keys, h_ctx,
        ).unwrap();
        let k_sub = mint_client.k_sub;
        let master_sig = mint_client.finalize(a_sub, e_sub, s_prime);

        // 2. Epoch Refresh
        let current_epoch = 1000u32;
        let (refresh_client, refresh_proof) = RefreshProver::prove(
            &mut rng, &master_sig, k_sub, 100, 5000, current_epoch,
            &generators, &keys.pk_master, h_ctx,
        ).unwrap();
        let refresh_resp = verify_refresh(
            &refresh_proof, current_epoch, &generators, &keys.pk_master, &keys, h_ctx, &mut rng,
        ).unwrap();
        let (daily_sig, k_daily) = refresh_client.finalize(refresh_resp);

        // 3. Spend
        let spend_amount = 30u32;
        let nonce = [0x42u8; 16];
        let (spend_client, spend_proof) = SpendProver::prove(
            &mut rng, &daily_sig, k_daily, 100, current_epoch, spend_amount,
            &nonce, &generators, &keys.pk_daily, h_ctx,
        ).unwrap();
        let spend_resp = verify_spend(
            &spend_proof, current_epoch, &nonce, &generators, &keys.pk_daily, &keys, h_ctx, &mut rng,
        ).unwrap();

        // Finalize refund token
        let s_refund = spend_client.r_star + spend_resp.s_prime_refund;
        let refund_sig = BbsSignature {
            a: spend_resp.a_refund,
            e: spend_resp.e_refund,
            s: s_refund,
        };
        assert!(!bool::from(blstrs::G1Projective::is_identity(&refund_sig.a)));
    }
}
