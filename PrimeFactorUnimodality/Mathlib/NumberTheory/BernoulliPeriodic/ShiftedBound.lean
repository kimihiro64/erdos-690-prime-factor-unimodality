/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ShiftedReciprocalBound
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ShiftedIntegrability

/-! # Explicit height-sensitive bounds for complex Bernoulli remainders

The rational coefficient budget bounds the periodic profile. Integrating the
reciprocal norm with the imaginary height retained gives a finite, explicit
bound for the whole tail, not a discretized or truncated replacement.
-/

open Complex MeasureTheory Set

namespace Polynomial

/-- Complete Bernoulli tail bound using any positive lower radius on the horizontal ray. -/
theorem norm_bernoulliPeriodic_inv_pow_tail_le_of_lower_bound (k : ℕ) {p : ℕ} (hp : 1 < p)
    {z : ℂ} (hz : 0 < z.re) {H : ℝ} (hH : 0 < H)
    (hB : ∀ x : ℝ, 0 ≤ x → H ≤ ‖z + (x : ℂ)‖) :
    ‖∫ x : ℝ in Ioi 0, (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p‖ ≤
      (bernoulliCoeffBound k : ℝ) *
        ((1 + 1 / ((p : ℝ) - 1)) * H ^ (1 - (p : ℝ))) := by
  have hi := integrableOn_bernoulliPeriodic_inv_pow k hp hz
  have hj := (integrableOn_inv_pow_add_ofReal hp hz).norm
  have hC : (0 : ℝ) ≤ (bernoulliCoeffBound k : ℝ) := by
    exact_mod_cast bernoulliCoeffBound_nonneg k
  calc
    _ ≤ ∫ x : ℝ in Ioi 0,
        ‖(bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi 0, (bernoulliCoeffBound k : ℝ) * ‖(z + (x : ℂ))⁻¹ ^ p‖ := by
      apply integral_mono_ae hi.norm (hj.const_mul _)
      filter_upwards with x
      rw [norm_mul, norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_bernoulliPeriodic_le_coeffBound k x) (norm_nonneg _)
    _ = (bernoulliCoeffBound k : ℝ) * ∫ x : ℝ in Ioi 0, ‖(z + (x : ℂ))⁻¹ ^ p‖ :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_norm_inv_pow_add_ofReal_le_of_lower_bound hp hz hH hB) hC

/-- Imaginary height gives a rapidly decreasing remainder at every order greater than one. -/
theorem norm_bernoulliPeriodic_inv_pow_tail_le_im (k : ℕ) {p : ℕ} (hp : 1 < p)
    {z : ℂ} (hz : 0 < z.re) (him : 0 < |z.im|) :
    ‖∫ x : ℝ in Ioi 0, (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p‖ ≤
      (bernoulliCoeffBound k : ℝ) *
        ((1 + 1 / ((p : ℝ) - 1)) * |z.im| ^ (1 - (p : ℝ))) :=
  norm_bernoulliPeriodic_inv_pow_tail_le_of_lower_bound k hp hz him
    (fun x _ => by simpa using abs_im_le_norm (z + (x : ℂ)))

end Polynomial
