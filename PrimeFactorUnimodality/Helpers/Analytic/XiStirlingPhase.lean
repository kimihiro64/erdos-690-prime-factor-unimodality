import PrimeFactorUnimodality.Helpers.Analytic.XiEvaluationError

/-! # An explicit elementary approximation to the normalized xi phase

The existing shifted-Gamma remainder bounds the phase error by one tenth
at every real height. Combining it with any rigorous zeta approximation
gives a certified normalized real-value enclosure.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- Elementary Stirling phase, including the actual pole-factor argument. -/
def turingStirlingPhase (t : ℝ) : ℝ :=
  (3 / 4 : ℝ) * arg ((5 / 4 : ℂ) + (t : ℂ) / 2 * I) +
    t / 2 * Real.log ‖(5 / 4 : ℂ) + (t : ℂ) / 2 * I‖ -
      t / 2 - t / 2 * Real.log Real.pi + arg ((1 / 2 : ℂ) + t * I - 1)

/-- The complete Gamma remainder gives a uniform phase error, including negative heights. -/
theorem abs_turingCountingPhase_sub_stirling_le (t : ℝ) :
    |turingCountingPhase t - turingStirlingPhase t| ≤ 1 / 10 := by
  have h := abs_xiGamma_half_contour_sub_stirling_le (σ := 2) (by norm_num) t
  rw [xiGamma_half_contour_eq_left (by norm_num)] at h
  convert h using 1
  unfold turingCountingPhase turingStirlingPhase
  congr 1
  ring

/-- Any zeta approximation gives a normalized xi enclosure using the explicit phase. -/
theorem abs_xiNormalizedValue_sub_stirlingApprox_le {t ε : ℝ} {w : ℂ}
    (hw : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ ε) :
    |xiNormalizedValue t - (exp (I * turingStirlingPhase t) * w).re| ≤
      ε + ‖w‖ / 10 := by
  simpa only [mul_one_div] using
    abs_xiNormalizedValue_sub_approx_le hw (abs_turingCountingPhase_sub_stirling_le t)

end

end PrimeFactorUnimodality
