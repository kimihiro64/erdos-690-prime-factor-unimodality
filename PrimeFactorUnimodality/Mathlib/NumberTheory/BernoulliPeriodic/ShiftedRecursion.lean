/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ShiftedCells

/-! # Higher-order recursion for the complete complex-shifted Bernoulli tail

Pass the finite cell identity to the improper integral. Reciprocal powers
vanish at infinity, but the initial boundary value is retained. This is the
integration-by-parts step needed for arbitrary-order complex Stirling errors.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Polynomial

/-- The full complex-shifted tail satisfies integration by parts without a boundary at infinity. -/
theorem bernoulliPeriodic_inv_pow_tail_recursion {k p : ℕ} (hk : 1 ≤ k) (hp : 1 < p)
    {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p) =
      -(bernoulliNormalizedReal (k + 1) 0 : ℂ) * z⁻¹ ^ p +
      (p : ℂ) * ∫ x : ℝ in Ioi 0,
        (bernoulliPeriodic (k + 1) x : ℂ) * (z + (x : ℂ))⁻¹ ^ (p + 1) := by
  have hF := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_bernoulliPeriodic_inv_pow k hp hz)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hG := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_bernoulliPeriodic_inv_pow (k + 1) (by omega : 1 < p + 1) hz)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hR := (((tendsto_inv_pow_add_nat (by omega : 0 < p) hz).sub_const (z⁻¹ ^ p)).const_mul
    (bernoulliNormalizedReal (k + 1) 0 : ℂ)).add (hG.const_mul (p : ℂ))
  have he : (fun N : ℕ => (bernoulliNormalizedReal (k + 1) 0 : ℂ) *
      ((z + N)⁻¹ ^ p - z⁻¹ ^ p) + (p : ℂ) *
      ∫ x : ℝ in 0..(N : ℝ),
        (bernoulliPeriodic (k + 1) x : ℂ) * (z + (x : ℂ))⁻¹ ^ (p + 1)) =
      (fun N : ℕ => ∫ x : ℝ in 0..(N : ℝ),
        (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p) := by
    funext N
    exact (bernoulliPeriodic_inv_pow_finite_recursion hk hp hz N).symm
  rw [he] at hR
  simpa only [zero_sub, mul_neg, neg_mul] using tendsto_nhds_unique hF hR

end Polynomial
