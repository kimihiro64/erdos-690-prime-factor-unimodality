import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSymmetry
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedBound

/-! # Closed real bounds for the complete Rosser zero tail

An arbitrary power `1<p<q` gives elementary integrals. The selected
coefficient uses the sharper cutoff value when valid and the global peak
otherwise. All zero multiplicities and both signs remain controlled by
the existing complete-tail theorem; no integral remains in the new bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- An elementary bound on the full two-sided tail, including the counting-envelope boundary. -/
def xiRosserClosedTailBound (a q p u : ℝ) : ℝ :=
  2 * (logDampedPowerMajorant a q p u * logDampedPowerIntegralFactor p (2 * π) u +
    2 * (Real.log u + 17) * logDampedPower a q u)

/-- The actual weighted improper integrals have an elementary majorant. -/
theorem xiRosserTailIntegral_le_closed {a q p u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hp : 1 < p) (hpq : p < q) (hu : 10 < u) :
    xiRosserTailIntegral a q u ≤
      logDampedPowerMajorant a q p u * logDampedPowerIntegralFactor p (2 * π) u := by
  exact integral_logDampedPower_density_le_of_majorant ha hq hp (by positivity)
    (by linarith) (by linarith [Real.pi_lt_four])
    (fun t ht => logDampedPower_le_rpow_mul_majorant ha hpq (by linarith) ht)

/-- No zero sum or improper integral remains in the bound for the actual full tail. -/
theorem xiRosserAbsoluteTail_le_closed {a q p u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hp : 1 < p) (hpq : p < q) (hu : 10 < u)
    (hw : exp (sqrt (a / q)) ≤ u) :
    xiRosserAbsoluteTail a q u ≤ xiRosserClosedTailBound a q p u :=
  (xiRosserAbsoluteTail_le_integral ha hq hu hw).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (xiRosserTailIntegral_le_closed ha hq hp hpq hu) le_rfl) (by norm_num))

/-- The scalar tail bound is nonnegative throughout the admissible parameter domain. -/
theorem xiRosserClosedTailBound_nonneg {a q p u : ℝ}
    (hp : 1 < p) (hu : 10 < u) : 0 ≤ xiRosserClosedTailBound a q p u := by
  have hfactor := logDampedPowerIntegralFactor_nonneg hp
    (by positivity : 0 < 2 * π) (by linarith [Real.pi_lt_four] : 2 * π ≤ u)
  have hlog : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  unfold xiRosserClosedTailBound
  exact mul_nonneg (by norm_num) (add_nonneg
    (mul_nonneg (logDampedPowerMajorant_pos _ _ _ _).le hfactor)
    (mul_nonneg (by linarith) (logDampedPower_pos _ _ _).le))

end

end PrimeFactorUnimodality
