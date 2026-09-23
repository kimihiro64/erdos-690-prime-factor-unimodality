import PrimeFactorUnimodality.Helpers.Analytic.XiRosserClosedBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedPolynomial

/-! # Polynomial damping for the actual complete zero tail

Apply the scalar Taylor majorant to the multiplicity-counted summable
tail. The remaining zero-damping tail has an elementary bound, including
the cutoff and both ordinate signs. No high-height turning point is used.
-/

namespace PrimeFactorUnimodality

open Real

/-- Any natural damping order leaves an explicitly bounded complete power tail. -/
theorem xiRosserAbsoluteTail_le_polynomial (n : ℕ) {a q U : ℝ}
    (ha : 0 < a) (hq : 3 ≤ q) (hU : 10 < U) :
    xiRosserAbsoluteTail a q U ≤
      ((n.factorial : ℝ) ^ 2 / a ^ n) * xiRosserPowerTailBound (q - 1) U := by
  let C := (n.factorial : ℝ) ^ 2 / a ^ n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := summable_xi_abs_logDampedPower ha.le (by linarith : 2 ≤ q)
    (by linarith : 1 < U) (fun _ hp => hp)
  have ht := summable_xi_abs_logDampedPower (a := 0) le_rfl (by linarith : 2 ≤ q - 1)
    (by linarith : 1 < U) (fun _ hp => hp)
  have hb : xiRosserAbsoluteTail a q U ≤ C * xiRosserAbsoluteTail 0 (q - 1) U := by
    rw [xiRosserAbsoluteTail, xiRosserAbsoluteTail, ← tsum_mul_left]
    apply hs.tsum_le_tsum _ (ht.mul_left C)
    intro p
    exact Real.logDampedPower_le_polynomial n ha
      ((show 1 < U by linarith).trans_le p.2)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (xiRosserAbsoluteTail_zero_le_power (by linarith) hU) hC)

end PrimeFactorUnimodality
