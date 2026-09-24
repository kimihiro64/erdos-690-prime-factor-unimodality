/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ShiftedReciprocal
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ExplicitBound

/-! # Periodic Bernoulli kernels on complex-shifted horizontal rays

The reciprocal base is genuinely complex, unlike the real-base complex
powers used for the zeta Euler tail. The explicit coefficient budget and
the reciprocal norm majorant prove absolute convergence on the whole ray.
-/

open Complex MeasureTheory Set

namespace Polynomial

/-- Every normalized periodic profile times an integrable reciprocal power is integrable. -/
theorem integrableOn_bernoulliPeriodic_inv_pow (k : ℕ) {p : ℕ} (hp : 1 < p)
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p)
      (Ioi 0) := by
  have hi := integrableOn_inv_pow_add_ofReal hp hz
  have hm := (continuous_ofReal.measurable.comp (measurable_bernoulliPeriodic k))
  refine (hi.norm.const_mul (bernoulliCoeffBound k : ℝ)).mono'
    (hm.aestronglyMeasurable.mul hi.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_bernoulliPeriodic_le_coeffBound k x) (norm_nonneg _)

/-- Restriction to a finite nonnegative interval preserves integrability. -/
theorem intervalIntegrable_bernoulliPeriodic_inv_pow (k : ℕ) {p : ℕ} (hp : 1 < p)
    {z : ℂ} (hz : 0 < z.re) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun x : ℝ => (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_bernoulliPeriodic_inv_pow k hp hz).mono_set
    (fun _ hx => lt_of_le_of_lt ha hx.1)

end Polynomial
