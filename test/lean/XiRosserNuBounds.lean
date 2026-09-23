import PrimeFactorUnimodality.Helpers.Analytic.XiRosserNuTail
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserNuWindow

/-! # Actual parameterized zero bounds and their endpoint domains -/

namespace PrimeFactorUnimodality.Tests

open Real

example {X q ν : ℝ} (hX : 0 < X) (hν : 0 < ν) (hmargin : 1 < (q - 1) * ν ^ 2) :
    xiRosserClosedTailBound (X ^ 2) q (q - 1 / ν ^ 2) (exp (ν * X)) =
      xiRosserNuTailBound X q ν := xiRosserClosedTailBound_eq_nu hX hν hmargin

example {X q ν : ℝ} (hX : 0 < X) (hq : 2 ≤ q) (hν : 0 < ν)
    (hmargin : 1 < (q - 1) * ν ^ 2) (hT : 10 < exp (ν * X)) :
    xiRosserAbsoluteTail (X ^ 2) q (exp (ν * X)) ≤ xiRosserNuTailBound X q ν :=
  xiRosserAbsoluteTail_le_nu hX hq hν hmargin hT

-- The high-tail result does not impose the finite-window condition nu<=1.
example {X : ℝ} (hX : 0 < X) (hT : 10 < exp (2 * X)) :
    xiRosserAbsoluteTail (X ^ 2) 2 (exp (2 * X)) ≤ xiRosserNuTailBound X 2 2 :=
  xiRosserAbsoluteTail_le_nu hX le_rfl (by norm_num) (by norm_num) hT

example {X q ν : ℝ} (hX : 0 < X) (hν : 0 < ν)
    (hmargin : 1 < (q - 1) * ν ^ 2) (hT : 10 < exp (ν * X)) :
    0 ≤ xiRosserNuTailBound X q ν := xiRosserNuTailBound_nonneg hX hν hmargin hT

example {X ν u : ℝ} (hX : 0 < X) (hν : 0 < ν) (hu : 10 ≤ u) (huv : u ≤ exp (ν * X)) :
    xiRosserIncreasingBound (X ^ 2) u (exp (ν * X)) ≤ xiRosserNuWindowBound X ν :=
  xiRosserIncreasingBound_le_nu hX hν hu huv

example {X ν : ℝ} (hX : 0 < X) (hν : 0 < ν) (hT : 10 ≤ exp (ν * X)) :
    0 ≤ xiRosserNuWindowBound X ν := xiRosserNuWindowBound_nonneg hX hν hT

example {X ν u : ℝ} (hX : 0 < X) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hu : 10 ≤ u) (huv : u ≤ exp (ν * X)) :
    (∑ p ∈ xiHeightWindowIndices u (exp (ν * X)),
      logDampedPower (X ^ 2) 1 (riemannXiDivisorZeroValue p).im) ≤ xiRosserNuWindowBound X ν :=
  sum_xi_logDampedPower_one_le_nu hX hν hν1 hu huv

-- Equality at the turning height is included in the finite-window result.
example {X u : ℝ} (hX : 0 < X) (hu : 10 ≤ u) (huv : u ≤ exp X) :
    (∑ p ∈ xiHeightWindowIndices u (exp X),
      logDampedPower (X ^ 2) 1 (riemannXiDivisorZeroValue p).im) ≤ xiRosserNuWindowBound X 1 := by
  simpa only [one_mul] using sum_xi_logDampedPower_one_le_nu hX
    (by norm_num : (0 : ℝ) < 1) le_rfl hu (by simpa using huv)

example {X ν H : ℝ} (hX : 0 < X) (hν : 0 < ν) (hH : 20 ≤ H) (hHT : H ≤ exp (ν * X)) :
    xiRosserIncreasingBandBound (X ^ 2) H (exp (ν * X)) ≤ 2 * xiRosserNuWindowBound X ν :=
  xiRosserIncreasingBandBound_le_nu hX hν hH hHT

example {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (hbt : b ≤ t) :
    0 ≤ logDampedWindowPrimitive a b t := logDampedWindowPrimitive_nonneg ha hb hbt

end PrimeFactorUnimodality.Tests
