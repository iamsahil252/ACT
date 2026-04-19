//! Pedersen commitments and Schnorr equality bridging.
//!
//! This module provides:
//! - Pedersen commitment creation and verification.
//! - Schnorr equality proofs linking scaled secrets from BBS+ proofs to external
//!   commitments (bridging).
//! - Helper functions for the bridging equalities used in epoch refresh and
//!   spending phases.

use ark_bls12_381::G1Projective;
use crate::types::Scalar;

/// Create a Pedersen commitment to a value with given blinding.
///
/// Commitment: `C = value * base_value + blinding * base_blinding`
pub fn commit(
    value: Scalar,
    blinding: Scalar,
    base_value: G1Projective,
    base_blinding: G1Projective,
) -> G1Projective {
    base_value * value.0 + base_blinding * blinding.0
}

/// Verify a Schnorr equality proof bridging a BBS+ scaled secret to an external
/// commitment.
///
/// This corresponds to the subtraction‑form verification equations in the
/// specification (Section 5.3 and 6.4):
///
/// ```text
/// z_value * base_value + z_blinding * base_blinding - T_bridge
///     == z_r1 * commitment - T_scale
/// ```
///
/// # Arguments
/// - `z_value`: response for the scaled secret value (e.g., `z_k_tilde`).
/// - `z_blinding`: response for the scaled blinding factor (e.g., `z_v`).
/// - `z_r1`: response for the BBS+ randomization scalar `r1`.
/// - `t_bridge`: the bridging commitment (e.g., `T_N`, `T_D`, `T_B`).
/// - `t_scale`: the scaled commitment (e.g., `T_scale_N`, `T_scale_D`).
/// - `c`: the Fiat–Shamir challenge (unused directly; equation subtracts).
/// - `commitment`: the external commitment (e.g., `N_T`, `K_daily`).
/// - `base_value`: the generator for the committed value.
/// - `base_blinding`: the generator for the blinding factor.
pub fn verify_bridge(
    z_value: Scalar,
    z_blinding: Scalar,
    z_r1: Scalar,
    t_bridge: G1Projective,
    t_scale: G1Projective,
    commitment: G1Projective,
    base_value: G1Projective,
    base_blinding: G1Projective,
) -> bool {
    let lhs = base_value * z_value.0 + base_blinding * z_blinding.0 - t_bridge;
    let rhs = commitment * z_r1.0 - t_scale;
    lhs == rhs
}

/// A variant used when the external commitment involves two bases (e.g., one
/// for the value and one for a separate blinding factor, but no separate
/// blinding in the bridge because it's already captured).
///
/// This covers cases like the nullifier bridge where the external commitment
/// is `N_T = k_sub * H_T` and there is no blinding term.
pub fn verify_bridge_single_base(
    z_value: Scalar,
    z_r1: Scalar,
    t_bridge: G1Projective,
    t_scale: G1Projective,
    commitment: G1Projective,
    base_value: G1Projective,
) -> bool {
    let lhs = base_value * z_value.0 - t_bridge;
    let rhs = commitment * z_r1.0 - t_scale;
    lhs == rhs
}

/// Generate the blinding scalars and bridging commitments for the refresh phase.
///
/// This is a convenience struct returned by the prover to keep track of the
/// external randomness used.
#[derive(Clone, Debug)]
pub struct RefreshBridging {
    pub r_daily: Scalar,
    pub r_delta: Scalar,
    pub k_daily: Scalar,
}

/// Generate the blinding scalars and bridging commitments for the spend phase.
#[derive(Clone, Debug)]
pub struct SpendBridging {
    pub r_star: Scalar,
    pub r_bp: Scalar,
    pub k_star: Scalar,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::setup::Generators;
    use ark_std::rand::thread_rng;

    #[test]
    fn commit_and_verify_bridge() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let value = Scalar::from(42u64);
        let blinding = Scalar::rand(&mut rng);
        let base_val = gens.h[4];
        let base_blind = gens.h[0];

        let commitment = commit(value, blinding, base_val, base_blind);

        // Simulate a proof: we know r1, scaled secrets, and responses.
        let r1 = Scalar::rand_nonzero(&mut rng);
        let scaled_value = value * r1;
        let scaled_blinding = blinding * r1;

        // Prover generates random blinders
        let rho_val = Scalar::rand(&mut rng);
        let rho_blind = Scalar::rand(&mut rng);
        let rho_r1 = Scalar::rand(&mut rng);

        // Compute T_bridge = rho_val * base_val + rho_blind * base_blind
        let t_bridge = base_val * rho_val.0 + base_blind * rho_blind.0;
        // T_scale = rho_r1 * commitment
        let t_scale = commitment * rho_r1.0;

        // Challenge (simulate)
        let c = Scalar::rand(&mut rng);

        // Responses
        let z_value = rho_val + c * scaled_value;
        let z_blind = rho_blind + c * scaled_blinding;
        let z_r1 = rho_r1 + c * r1;

        // Verification should pass
        assert!(verify_bridge(
            z_value, z_blind, z_r1,
            t_bridge, t_scale,
            commitment,
            base_val, base_blind
        ));
    }

    #[test]
    fn verify_bridge_single_base_works() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let k_sub = Scalar::rand(&mut rng);
        let h_t = gens.h[1]; // pretend this is H_T
        let n_t = h_t * k_sub.0;

        let r1 = Scalar::rand_nonzero(&mut rng);
        let scaled_k = k_sub * r1;

        let rho_k = Scalar::rand(&mut rng);
        let rho_r1 = Scalar::rand(&mut rng);

        let t_bridge = h_t * rho_k.0;
        let t_scale = n_t * rho_r1.0;

        let c = Scalar::rand(&mut rng);
        let z_k = rho_k + c * scaled_k;
        let z_r1 = rho_r1 + c * r1;

        assert!(verify_bridge_single_base(
            z_k, z_r1,
            t_bridge, t_scale,
            n_t,
            h_t
        ));
    }
}
