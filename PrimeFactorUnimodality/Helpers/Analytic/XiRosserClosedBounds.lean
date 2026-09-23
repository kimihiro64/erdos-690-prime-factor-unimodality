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

/-- The zero-damping majorant retains the full integrable height power. -/
def xiRosserPowerTailBound (q U : ℝ) : ℝ :=
  2 * (logDampedPowerIntegralFactor q (2 * π) U +
    2 * (Real.log U + 17) * logDampedPower 0 q U)

/-- At zero damping, exponent splitting is unnecessary: use the full power. -/
theorem xiRosserAbsoluteTail_zero_le_power {q U : ℝ} (hq : 2 ≤ q) (hU : 10 < U) :
    xiRosserAbsoluteTail 0 q U ≤
      xiRosserPowerTailBound q U := by
  have hi : xiRosserTailIntegral 0 q U ≤ logDampedPowerIntegralFactor q (2 * π) U := by
    have ht := integral_logDampedPower_density_le_of_majorant (a := 0) (q := q)
      (p := q) (C := 1) le_rfl hq (by linarith : 1 < q)
      (by positivity : 0 < 2 * π) (by linarith : 1 < U)
      (by linarith [Real.pi_lt_four] : 2 * π ≤ U) (by
        intro t ht
        have hUt : U ≤ t := ht
        rw [logDampedPower_eq_rpow_mul (by linarith : 0 < t)]
        simp)
    simpa only [xiRosserTailIntegral, one_mul] using ht
  exact (xiRosserAbsoluteTail_le_integral le_rfl hq hU (by simp; linarith)).trans
    (mul_le_mul_of_nonneg_left (add_le_add hi le_rfl) (by norm_num))

end

end PrimeFactorUnimodality
