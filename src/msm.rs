//! Multi-scalar multiplication (MSM) helpers for G1 over blstrs.
//!
//! `g1_msm` delegates to `G1Projective::multi_exp`, which is blstrs's built-in
//! Pippenger MSM backed by the highly-optimised blst C/ASM library.
//!
//! `batch_normalize` uses `group::Curve::batch_normalize`, which performs a
//! Montgomery batch-inversion to convert N projective points to affine with a
//! single field inversion and 3N multiplications instead of N inversions.

use blstrs::{G1Affine, G1Projective, Scalar};
use group::{Curve, Group};

/// Compute `∑ bases[i] * scalars[i]` over G1 using Pippenger MSM.
///
/// Delegates to `G1Projective::multi_exp`, which calls blst's highly-optimised
/// Pippenger algorithm.  This is significantly faster than a naive scalar-mul
/// loop for all batch sizes ≥ 2.
///
/// Returns the identity element if `bases` is empty.
///
/// # Panics
/// Panics if `bases.len() != scalars.len()`.
pub fn g1_msm(bases: &[G1Affine], scalars: &[Scalar]) -> G1Projective {
    assert_eq!(bases.len(), scalars.len(), "MSM: bases/scalars length mismatch");
    if bases.is_empty() {
        return G1Projective::identity();
    }
    // Convert affine → projective (cheap: just sets Z = 1).
    // G1Projective::multi_exp then runs Pippenger internally.
    let proj: Vec<G1Projective> = bases.iter().map(G1Projective::from).collect();
    G1Projective::multi_exp(&proj, scalars)
}

/// Batch-normalise a slice of projective G1 points into their affine forms.
///
/// Uses `group::Curve::batch_normalize`, which applies Montgomery's batch-
/// inversion trick: one field inversion + 3N multiplications, compared with N
/// independent field inversions for a naive sequential conversion.  Calling
/// this in a loop doing N individual `G1Affine::from` conversions requires N
/// inversions, which is significantly more expensive for N > 1.
pub fn batch_normalize(points: &[G1Projective]) -> Vec<G1Affine> {
    if points.is_empty() {
        return Vec::new();
    }
    let mut affines = vec![G1Affine::default(); points.len()];
    G1Projective::batch_normalize(points, &mut affines);
    affines
}

/// Multiply a G1 point by a 32-bit unsigned scalar using a 32-iteration
/// double-and-add loop.
///
/// For small scalars (spend amounts, epoch numbers) this avoids the full
/// 256-bit scalar-multiplication loop and runs ≈ 8× faster.
#[inline]
pub fn g1_mul_u32(point: G1Projective, scalar: u32) -> G1Projective {
    if scalar == 0 {
        return G1Projective::identity();
    }
    if scalar == 1 {
        return point;
    }
    let mut result = G1Projective::identity();
    let mut addend = point;
    let mut n = scalar;
    while n > 0 {
        if n & 1 == 1 {
            result = &result + &addend;
        }
        addend = &addend + &addend;
        n >>= 1;
    }
    result
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

    #[test]
    fn g1_mul_u32_matches_scalar_mul() {
        use blstrs::Scalar as BlsScalar;
        let g = G1Projective::generator();
        for &n in &[0u32, 1, 2, 7, 30, 100, 5000, u32::MAX] {
            let expected = &g * &BlsScalar::from(n as u64);
            let got = g1_mul_u32(g, n);
            assert_eq!(got, expected, "mismatch at n={n}");
        }
    }
}
