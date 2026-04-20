//! Multi-scalar multiplication (MSM) helpers for G1 over blstrs.
//!
//! Uses blstrs's native `G1Projective * &Scalar` which internally calls the
//! highly-optimised blst assembly.  For the proof sizes used in ACT (≤ 32
//! bases) the per-multiplication cost is dominated by the blst scalar mult; a
//! Pippenger bucket reduction would add complexity without significant gain at
//! this scale.

use blstrs::{G1Affine, G1Projective, Scalar};
use group::Group;

/// Compute `∑ bases[i] * scalars[i]` over G1.
///
/// Returns the identity element if `bases` is empty.
///
/// # Panics
/// Panics if `bases.len() != scalars.len()`.
pub fn g1_msm(bases: &[G1Affine], scalars: &[Scalar]) -> G1Projective {
    assert_eq!(bases.len(), scalars.len(), "MSM: bases/scalars length mismatch");
    bases
        .iter()
        .zip(scalars.iter())
        .map(|(b, s)| {
            let p = G1Projective::from(b);
            &p * s
        })
        .fold(G1Projective::identity(), |acc, p| &acc + &p)
}

/// Batch-normalise a slice of projective G1 points into their affine forms.
///
/// Each conversion uses a single field inversion internally.  For 10–20 points
/// the practical cost difference to a batch inversion is negligible.
pub fn batch_normalize(points: &[G1Projective]) -> Vec<G1Affine> {
    points.iter().map(G1Affine::from).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;
    use group::Group;

    #[test]
    fn msm_empty() {
        let result = g1_msm(&[], &[]);
        assert!(bool::from(result.is_identity()));
    }

    #[test]
    fn msm_single_zero_scalar() {
        let base = G1Affine::from(G1Projective::generator());
        let result = g1_msm(&[base], &[Scalar::ZERO]);
        assert!(bool::from(result.is_identity()));
    }

    #[test]
    fn msm_single_one_scalar() {
        let g = G1Projective::generator();
        let g_aff = G1Affine::from(g);
        let result = g1_msm(&[g_aff], &[Scalar::ONE]);
        assert_eq!(result, g);
    }

    #[test]
    fn msm_two_generators() {
        let mut rng = rand::thread_rng();
        let g = G1Projective::generator();
        let g_aff = G1Affine::from(g);
        let s1 = Scalar::random(&mut rng);
        let s2 = Scalar::random(&mut rng);
        let expected = &(&g * &s1) + &(&g * &s2);
        let result = g1_msm(&[g_aff, g_aff], &[s1, s2]);
        assert_eq!(result, expected);
    }
}
