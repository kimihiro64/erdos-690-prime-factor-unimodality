import PrimeFactorUnimodality.Helpers.Analytic.XiZeroNumericalBounds

/-! # Common elementary bounds at the Dusart psi endpoint

The half-logarithmic decay and elementary correction hold on the complete
starting ray, independently of smoothing order or the zero cutoff.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- A rational lower base point controls the half-logarithmic decay. -/
theorem dusartEndpoint_half_log_decay_le {x : ℝ} (hx : (1440000000000 : ℝ) ≤ x) :
    exp (-(1 / 2) * Real.log x) ≤ (1 / 1200000 : ℝ) := by
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1200000 ^ 2)
    (by norm_num at hx ⊢; exact hx : (1200000 : ℝ) ^ 2 ≤ x)
  rw [Real.log_pow] at hl
  norm_num at hl
  have he : -(1 / 2) * Real.log x ≤ - Real.log (1200000 : ℝ) := by nlinarith
  simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 1200000), one_div] using
    Real.exp_le_exp.mpr he

/-- The normalized elementary correction is negligible on this ray. -/
theorem dusartEndpoint_correction_le {x : ℝ} (hx : (1440000000000 : ℝ) ≤ x) :
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x ≤ (4 / 1440000000000 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hd : 1 ≤ 2 * (x ^ 2 - 1) := by nlinarith
  have hr : 1 / (2 * (x ^ 2 - 1)) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
  have hl : Real.log (2 * π) ≤ 3 := by
    have hl := Real.log_le_log (by positivity : 0 < 2 * π)
      (by linarith [pi_lt_four] : 2 * π ≤ 2 ^ 3)
    rw [Real.log_pow] at hl
    norm_num at hl
    linarith [Real.log_two_lt_d9]
  exact (div_le_div_of_nonneg_right (by linarith : 1 / (2 * (x ^ 2 - 1)) +
    Real.log (2 * π) ≤ 4) hxpos.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx)

end

end PrimeFactorUnimodality
