import PrimeFactorUnimodality.Helpers.Analytic.XiWeightedCountingPeak
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedShape

/-! # Rosser damped-power sums over actual xi zeros

The turning height is clamped to the window. The increasing and decreasing
branches join with only one peak contribution, retaining the signed
integrals of the error-envelope derivative. This is the weighted-counting
step of Dusart HDR section 2.4, using the proved envelope `log(t)+17`.
The parameters remain arbitrary; no numerical zero-free constant is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- The central element of the two endpoints and the unconstrained turning height. -/
def xiRosserPeak (a q u v : ℝ) : ℝ := max u (min v (exp (sqrt (a / q))))

/-- The finite-window integral majorant, including the peak and signed density corrections. -/
def xiRosserWindowBound (a q u v : ℝ) : ℝ :=
  if u < v then
    (∫ t in Icc u v, ((1 / (2 * π)) * Real.log (t / (2 * π))) * logDampedPower a q t) -
    (∫ t in Icc u (xiRosserPeak a q u v), logDampedPower a q t / t) +
    (∫ t in Icc (xiRosserPeak a q u v) v, logDampedPower a q t / t) +
    2 * (Real.log (xiRosserPeak a q u v) + 17) * logDampedPower a q (xiRosserPeak a q u v)
  else 0

/-- An empty window incurs no peak cost. -/
@[simp] theorem xiRosserWindowBound_self (a q u : ℝ) : xiRosserWindowBound a q u u = 0 := by
  simp [xiRosserWindowBound]

/-- The clamped turning height belongs to the closed window, including coincident endpoints. -/
theorem xiRosserPeak_mem {a q u v : ℝ} (huv : u ≤ v) : xiRosserPeak a q u v ∈ Icc u v :=
  ⟨le_max_left _ _, max_le huv (min_le_left _ _)⟩

/-- Actual multiplicity-counted damped zero sums satisfy the Rosser window bound. -/
theorem sum_xi_logDampedPower_le {a q u v : ℝ}
    (ha : 0 ≤ a) (hq : 0 < q) (hu : 10 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ xiHeightWindowIndices u v, logDampedPower a q (riemannXiDivisorZeroValue p).im) ≤
      xiRosserWindowBound a q u v := by
  rcases huv.eq_or_lt with rfl | huv'
  · simp
  rw [xiRosserWindowBound, ite_eq_left huv']
  have ht (t : ℝ) (ht : t ∈ Icc u v) : 1 < t := by linarith [ht.1]
  have hf (t : ℝ) (h : t ∈ Icc u v) :
      HasDerivAt (logDampedPower a q) (logDampedPowerSlope a q t) t :=
    hasDerivAt_logDampedPower (ht t h)
  have hg := continuousOn_logDampedPowerSlope (a := a) (q := q) ht
  have hU := abs_le.mp (abs_xiZeroCountingRemainder_le_log_add hu)
  have hV := abs_le.mp (abs_xiZeroCountingRemainder_le_log_add (hu.trans huv))
  have hpu := (logDampedPower_pos a q u).le
  have hpv := (logDampedPower_pos a q v).le
  by_cases hv : v ≤ exp (sqrt (a / q))
  · have hpeak : xiRosserPeak a q u v = v := by
      simp only [xiRosserPeak, min_eq_left hv, max_eq_right huv]
    have he := sum_xi_weighted_window_le_of_slope_nonneg hu huv hf hg
      (fun t h => logDampedPowerSlope_nonneg_before ha hq (ht t h) (h.2.trans hv))
    rw [hpeak]
    simp only [Icc_self, integral_singleton, Measure.real, measure_singleton,
      ENNReal.toReal_zero, zero_smul, add_zero]
    nlinarith [mul_nonneg
      (show 0 ≤ xiZeroCountingRemainder u + (Real.log u + 17) by linarith) hpu,
      mul_nonpos_of_nonpos_of_nonneg
        (show xiZeroCountingRemainder v - (Real.log v + 17) ≤ 0 by linarith) hpv]
  by_cases hw : exp (sqrt (a / q)) ≤ u
  · have hpeak : xiRosserPeak a q u v = u := by
      exact max_eq_left ((min_le_right _ _).trans hw)
    have he := sum_xi_weighted_window_le_of_slope_nonpos hu huv hf hg
      (fun t h => logDampedPowerSlope_nonpos_after ha hq (ht t h) (hw.trans h.1))
    rw [hpeak]
    simp only [Icc_self, integral_singleton, Measure.real, measure_singleton,
      ENNReal.toReal_zero, zero_smul, sub_zero]
    nlinarith [mul_nonneg
      (show 0 ≤ xiZeroCountingRemainder u + (Real.log u + 17) by linarith) hpu,
      mul_nonpos_of_nonpos_of_nonneg
        (show xiZeroCountingRemainder v - (Real.log v + 17) ≤ 0 by linarith) hpv]
  have huw : u ≤ exp (sqrt (a / q)) := (lt_of_not_ge hw).le
  have hwv : exp (sqrt (a / q)) ≤ v := (lt_of_not_ge hv).le
  have hpeak : xiRosserPeak a q u v = exp (sqrt (a / q)) := by
    simp only [xiRosserPeak, min_eq_right hwv, max_eq_right huw]
  rw [hpeak]
  exact sum_xi_weighted_window_le_peak_envelope hu huw hwv hf hg
    (fun t h => logDampedPowerSlope_nonneg_before ha hq
      (by linarith [h.1]) h.2)
    (fun t h => logDampedPowerSlope_nonpos_after ha hq
      (by linarith [h.1]) h.1) hpu hpv

/-- The explicit window bound is nonnegative since it bounds a sum of positive kernels. -/
theorem xiRosserWindowBound_nonneg {a q u v : ℝ}
    (ha : 0 ≤ a) (hq : 0 < q) (hu : 10 ≤ u) (huv : u ≤ v) :
    0 ≤ xiRosserWindowBound a q u v :=
  (Finset.sum_nonneg (fun p _ => (logDampedPower_pos a q
    (riemannXiDivisorZeroValue p).im).le)).trans (sum_xi_logDampedPower_le ha hq hu huv)

end

end PrimeFactorUnimodality
