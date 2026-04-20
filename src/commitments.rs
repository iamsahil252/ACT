//! Pedersen commitments and Schnorr equality bridging.

use blstrs::G1Projective;
use crate::types::Scalar;

/// Create a Pedersen commitment: `C = value·base_value + blinding·base_blinding`.
pub fn commit(
    value: Scalar,
    blinding: Scalar,
    base_value: G1Projective,
    base_blinding: G1Projective,
) -> G1Projective {
    &(&base_value * &value.0) + &(&base_blinding * &blinding.0)
}

/// Verify a Schnorr equality proof bridging a BBS+ scaled secret to an external
/// commitment (two-base variant).
///
/// Checks `z_value·base_value + z_blinding·base_blinding − T_bridge
///       == z_r1·commitment − T_scale`.
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
    let lhs = &(&(&base_value * &z_value.0) + &(&base_blinding * &z_blinding.0)) - &t_bridge;
    let rhs = &(&commitment * &z_r1.0) - &t_scale;
    lhs == rhs
}

/// Single-base bridge verification: `z_value·base_value − T_bridge == z_r1·commitment − T_scale`.
pub fn verify_bridge_single_base(
    z_value: Scalar,
    z_r1: Scalar,
    t_bridge: G1Projective,
    t_scale: G1Projective,
    commitment: G1Projective,
    base_value: G1Projective,
) -> bool {
    let lhs = (&base_value * &z_value.0) - &t_bridge;
    let rhs = &(&commitment * &z_r1.0) - &t_scale;
    lhs == rhs
}

/// Blinding scalars for the refresh-phase bridging.
#[derive(Clone, Debug)]
pub struct RefreshBridging {
    pub r_daily: Scalar,
    pub r_delta: Scalar,
    pub k_daily: Scalar,
}

/// Blinding scalars for the spend-phase bridging.
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
    use rand::thread_rng;

    #[test]
    fn commit_and_verify_bridge() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let value = Scalar::from(42u64);
        let blinding = Scalar::rand(&mut rng);
        let base_val = gens.h[4];
        let base_blind = gens.h[0];

        let commitment = commit(value, blinding, base_val, base_blind);

        let r1 = Scalar::rand_nonzero(&mut rng);
        let scaled_value = value * r1;
        let scaled_blinding = blinding * r1;

        let rho_val = Scalar::rand(&mut rng);
        let rho_blind = Scalar::rand(&mut rng);
        let rho_r1 = Scalar::rand(&mut rng);

        let t_bridge = &(&base_val * &rho_val.0) + &(&base_blind * &rho_blind.0);
        let t_scale = &commitment * &rho_r1.0;

        let c = Scalar::rand(&mut rng);
        let z_value = rho_val + c * scaled_value;
        let z_blind = rho_blind + c * scaled_blinding;
        let z_r1 = rho_r1 + c * r1;

        assert!(verify_bridge(z_value, z_blind, z_r1, t_bridge, t_scale, commitment, base_val, base_blind));
    }

    #[test]
    fn verify_bridge_single_base_works() {
        let mut rng = thread_rng();
        let gens = Generators::new();

        let k_sub = Scalar::rand(&mut rng);
        let h_t = gens.h[1];
        let n_t = &h_t * &k_sub.0;

        let r1 = Scalar::rand_nonzero(&mut rng);
        let scaled_k = k_sub * r1;

        let rho_k = Scalar::rand(&mut rng);
        let rho_r1 = Scalar::rand(&mut rng);

        let t_bridge = &h_t * &rho_k.0;
        let t_scale = &n_t * &rho_r1.0;

        let c = Scalar::rand(&mut rng);
        let z_k = rho_k + c * scaled_k;
        let z_r1 = rho_r1 + c * r1;

        assert!(verify_bridge_single_base(z_k, z_r1, t_bridge, t_scale, n_t, h_t));
    }
}
