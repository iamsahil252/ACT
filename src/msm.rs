//! Multi-scalar multiplication (MSM) helpers for G1 over blstrs.
//!
//! `g1_msm` delegates to `G1Projective::multi_exp`, which is blstrs's built-in
//! Pippenger MSM backed by the highly-optimised blst C/ASM library.
//!
//! `batch_normalize` uses `group::Curve::batch_normalize`, which performs a
//! Montgomery batch-inversion to convert N projective points to affine with a
//! single field inversion and 3N multiplications instead of N inversions.
//!
//! `FixedBaseTable` provides precomputed window tables for fixed-base scalar
//! multiplication.  For the five protocol generators (g1, h0–h4) known at
//! startup, this replaces the variable-base Pippenger loop with `NUM_WINDOWS`
//! affine point additions and zero doublings.

use blstrs::{G1Affine, G1Projective, Scalar};
use group::{prime::PrimeCurveAffine, Curve, Group};

/// Compute `∑ bases[i] * scalars[i]` over G1 using Pippenger MSM.
///
/// Delegates to `G1Projective::multi_exp`, which calls blst's highly-optimised
/// Pippenger algorithm.  This is significantly faster than a naive scalar-mul
/// loop for all batch sizes ≥ 12.
///
/// For small batches (< 12 points) the Pippenger algorithm's bucket-setup
/// overhead dominates; a plain fold using `&G1Projective + &G1Affine` mixed
/// addition is used instead, avoiding both the heap allocation of a temporary
/// projective vector and the algorithm's fixed setup cost.
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
    // For small batches the Pippenger set-up cost dominates.  A plain fold
    // using the blstrs mixed-addition operator (&G1Projective + &G1Affine) is
    // faster and requires no temporary heap allocation.
    if bases.len() < 12 {
        return bases.iter().zip(scalars.iter()).fold(
            G1Projective::identity(),
            |acc, (base, scalar)| &acc + &(base * scalar),
        );
    }
    // For larger batches use Pippenger MSM.
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

// ============================================================================
// Fixed-base precomputed scalar multiplication
// ============================================================================

/// Number of bits per window (w = 4 → 16 table entries per window).
const WINDOW_BITS: usize = 4;
/// Number of non-identity (non-zero digit) entries per window: 2^WINDOW_BITS − 1.
const NON_ZERO_DIGITS: usize = (1 << WINDOW_BITS) - 1; // 15
/// Number of windows needed to cover a 255-bit BLS12-381 scalar stored in 32 bytes
/// (256 bits, upper bit always 0).
const NUM_WINDOWS: usize = 256 / WINDOW_BITS; // 64

/// Precomputed lookup table for fixed-base scalar multiplication over G1.
///
/// At construction time stores, for window index `w ∈ 0..NUM_WINDOWS` and
/// non-zero digit `d ∈ 1..=NON_ZERO_DIGITS`:
///
/// ```text
/// table[w * NON_ZERO_DIGITS + (d − 1)] = d · (2^(WINDOW_BITS·w)) · B
/// ```
///
/// Multiplying by a scalar `s` requires exactly `NUM_WINDOWS` conditional
/// mixed additions (projective += affine) and zero doublings, compared with
/// ≈256 doublings + ≈128 additions for a standard double-and-add.
///
/// Memory cost: `NUM_WINDOWS × NON_ZERO_DIGITS × sizeof(G1Affine)`
///            = `64 × 15 × 96 bytes ≈ 90 KB` per table.
#[derive(Clone, Debug)]
pub struct FixedBaseTable {
    /// Flat table: `table[w * NON_ZERO_DIGITS + (d − 1)] = d · 2^(W·w) · B`.
    table: Vec<G1Affine>,
}

impl FixedBaseTable {
    /// Build the precomputed table for `base`.
    ///
    /// Called once per generator at process startup (inside the `Generators`
    /// singleton).  Internally performs `NUM_WINDOWS` batch-normalize calls,
    /// one per window, to amortise field inversions.
    pub fn new(base: &G1Affine) -> Self {
        let total = NUM_WINDOWS * NON_ZERO_DIGITS;
        let mut table = Vec::with_capacity(total);

        // base_exp = 2^(WINDOW_BITS·w) · base, advanced once per window.
        let mut base_exp = G1Projective::from(*base);

        let mut proj_buf = [G1Projective::identity(); NON_ZERO_DIGITS];
        let mut aff_buf  = [G1Affine::identity();     NON_ZERO_DIGITS];

        for _ in 0..NUM_WINDOWS {
            // proj_buf[i] = (i + 1) · base_exp
            proj_buf[0] = base_exp;
            for i in 1..NON_ZERO_DIGITS {
                proj_buf[i] = &proj_buf[i - 1] + &base_exp;
            }
            G1Projective::batch_normalize(&proj_buf, &mut aff_buf);
            table.extend_from_slice(&aff_buf);

            // Advance: base_exp ← 2^WINDOW_BITS · base_exp
            for _ in 0..WINDOW_BITS {
                base_exp = base_exp.double();
            }
        }

        Self { table }
    }

    /// Compute `scalar · base` using the precomputed table.
    ///
    /// Decomposes `scalar` into 4-bit windows (little-endian), then performs
    /// one conditional mixed addition per window (projective += affine).
    /// No doublings are needed: the window powers are baked into the table.
    #[inline]
    pub fn mul(&self, scalar: &Scalar) -> G1Projective {
        let bytes = scalar.to_bytes_le();
        let mut result = G1Projective::identity();

        for w in 0..NUM_WINDOWS {
            // Extract the w-th 4-bit chunk.  With WINDOW_BITS = 4 each chunk
            // falls within a single byte (shift is 0 or 4).
            let byte_idx  = w >> 1;           // w / 2
            let bit_shift = (w & 1) << 2;     // (w % 2) * 4
            let digit = ((bytes[byte_idx] >> bit_shift) & 0xf) as usize;
            if digit != 0 {
                // Mixed addition: G1Projective += &G1Affine (no extra inversion).
                result += &self.table[w * NON_ZERO_DIGITS + digit - 1];
            }
        }

        result
    }
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

    #[test]
    fn fixed_base_table_zero_scalar() {
        let g_aff = G1Affine::from(G1Projective::generator());
        let table = FixedBaseTable::new(&g_aff);
        let result = table.mul(&Scalar::ZERO);
        assert!(bool::from(result.is_identity()));
    }

    #[test]
    fn fixed_base_table_one_scalar() {
        let g = G1Projective::generator();
        let g_aff = G1Affine::from(g);
        let table = FixedBaseTable::new(&g_aff);
        let result = table.mul(&Scalar::ONE);
        assert_eq!(result, g);
    }

    #[test]
    fn fixed_base_table_matches_scalar_mul() {
        use ff::Field;
        let mut rng = rand::thread_rng();
        let g = G1Projective::generator();
        let g_aff = G1Affine::from(g);
        let table = FixedBaseTable::new(&g_aff);
        for _ in 0..8 {
            let s = Scalar::random(&mut rng);
            let expected = &g * &s;
            let got = table.mul(&s);
            assert_eq!(got, expected, "FixedBaseTable result mismatch");
        }
    }
}
