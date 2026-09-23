import PrimeFactorUnimodality.Helpers.Analytic.XiRosserWindow
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedWindow

/-! # An elementary increasing-window Rosser bound

The finite exponent-one density is bounded by an explicit upper primitive,
as in Dusart HDR section 2.4, Lemma 48. The actual zero-counting estimate
uses the already proved envelope `log(t)+17`. Equal endpoints cost zero;
the negative density correction and favorable endpoint terms are discarded
only after their signs have been proved.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- The complete increasing-window bound, retaining the lower primitive endpoint. -/
def xiRosserIncreasingBound (a u v : ℝ) : ℝ :=
  if u < v then
    (1 / (2 * π)) * (logDampedWindowPrimitive a (2 * π) v -
      logDampedWindowPrimitive a (2 * π) u) +
      2 * (Real.log v + 17) * logDampedPower a 1 v
  else 0

/-- An empty window contributes neither a density nor an endpoint cost. -/
@[simp] theorem xiRosserIncreasingBound_self (a u : ℝ) :
    xiRosserIncreasingBound a u u = 0 := by simp [xiRosserIncreasingBound]

/-- Actual multiplicity-counted zeros on an increasing window have an elementary bound. -/
theorem sum_xi_logDampedPower_one_le_increasing {a u v : ℝ}
    (ha : 0 < a) (hu : 10 ≤ u) (huv : u ≤ v) (hv : v ≤ exp (sqrt a)) :
    (∑ p ∈ xiHeightWindowIndices u v, logDampedPower a 1 (riemannXiDivisorZeroValue p).im) ≤
      xiRosserIncreasingBound a u v := by
  rcases huv.eq_or_lt with rfl | huv'
  · simp
  have hu1 : 1 < u := by linarith
  have hpeak : xiRosserPeak a 1 u v = v := by
    simp only [xiRosserPeak, div_one, min_eq_left hv, max_eq_right huv'.le]
  have hs := sum_xi_logDampedPower_le ha.le (by norm_num : (0 : ℝ) < 1) hu huv'.le
  rw [xiRosserWindowBound, ite_eq_left huv', hpeak] at hs
  simp only [Icc_self, integral_singleton, Measure.real, measure_singleton,
    ENNReal.toReal_zero, zero_smul, add_zero] at hs
  have he : (∫ t in Icc u v,
      ((1 / (2 * π)) * Real.log (t / (2 * π))) * logDampedPower a 1 t) =
      (1 / (2 * π)) * ∫ t in Icc u v, Real.log (t / (2 * π)) * logDampedPower a 1 t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  rw [he] at hs
  have hcorr : 0 ≤ ∫ t in Icc u v, logDampedPower a 1 t / t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg (logDampedPower_pos _ _ _).le
      (lt_trans zero_lt_one (hu1.trans_le ht.1)).le
  have hd := mul_le_mul_of_nonneg_left
    (integral_logDampedPower_one_le_sub ha (by positivity : 0 < 2 * π) hu1
      (by linarith [Real.pi_lt_four] : 2 * π ≤ u) huv'.le)
    (by positivity : 0 ≤ 1 / (2 * π))
  rw [xiRosserIncreasingBound, ite_eq_left huv']
  linarith

/-- The closed bound is nonnegative, witnessed by the actual positive-kernel sum. -/
theorem xiRosserIncreasingBound_nonneg {a u v : ℝ}
    (ha : 0 < a) (hu : 10 ≤ u) (huv : u ≤ v) (hv : v ≤ exp (sqrt a)) :
    0 ≤ xiRosserIncreasingBound a u v :=
  (Finset.sum_nonneg (fun p _ => (logDampedPower_pos a 1
    (riemannXiDivisorZeroValue p).im).le)).trans
      (sum_xi_logDampedPower_one_le_increasing ha hu huv hv)

end

end PrimeFactorUnimodality
