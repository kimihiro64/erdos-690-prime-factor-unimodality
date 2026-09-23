import PrimeFactorUnimodality.Helpers.Analytic.XiRosserAbel
import PrimeFactorUnimodality.Helpers.Analytic.XiWeightedCountingBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDamped

/-! # The strict Rosser tail from the actual counting envelope

Beyond the turning height, the decreasing finite-window estimate passes
to infinity. Both weighted integrals are proved integrable, and the lower
counting discrepancy is retained so cutoff multiplicities can be restored
without paying an extra independent boundary bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-- The logarithmic zero-density integral is absolutely convergent. -/
theorem integrableOn_xi_rosser_density {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    IntegrableOn (fun t => ((1 / (2 * π)) * Real.log (t / (2 * π))) *
      logDampedPower a q t) (Ioi u) := by
  have hi : IntegrableOn (fun t => (1 / (2 * π)) *
      (Real.log (t / (2 * π)) * logDampedPower a q t)) (Ioi u) :=
    (integrableOn_log_div_mul_logDampedPower ha hq hu
      (by positivity : 0 < 2 * π)).const_mul (1 / (2 * π))
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  dsimp
  ring

/-- The two convergent improper integrals controlling the decreasing tail. -/
def xiRosserTailIntegral (a q u : ℝ) : ℝ :=
  (∫ t in Ioi u, ((1 / (2 * π)) * Real.log (t / (2 * π))) * logDampedPower a q t) +
  ∫ t in Ioi u, logDampedPower a q t / t

/-- The upper endpoint discrepancy has favorable sign and can be discarded. -/
theorem sum_xi_damped_window_le_tail_integrals {a q u v : ℝ}
    (ha : 0 ≤ a) (hq : 0 < q) (hu : 10 ≤ u) (huv : u ≤ v)
    (hw : exp (sqrt (a / q)) ≤ u) :
    (∑ p ∈ xiHeightWindowIndices u v, logDampedPower a q (riemannXiDivisorZeroValue p).im) ≤
      (∫ t in Icc u v, ((1 / (2 * π)) * Real.log (t / (2 * π))) * logDampedPower a q t) +
      (∫ t in Icc u v, logDampedPower a q t / t) -
      (xiZeroCountingRemainder u - (Real.log u + 17)) * logDampedPower a q u := by
  have ht (t : ℝ) (ht : t ∈ Icc u v) : 1 < t := by linarith [ht.1]
  have he := sum_xi_weighted_window_le_of_slope_nonpos hu huv
    (fun t h => hasDerivAt_logDampedPower (a := a) (q := q) (ht t h))
    (continuousOn_logDampedPowerSlope ht)
    (fun t h => logDampedPowerSlope_nonpos_after ha hq (ht t h) (hw.trans h.1))
  have hV := (abs_le.mp (abs_xiZeroCountingRemainder_le_log_add (hu.trans huv))).2
  have hn := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hV) (logDampedPower_pos a q v).le
  linarith only [he, hn]

/-- The complete strict tail has the integral majorant with its signed lower discrepancy. -/
theorem xi_strict_damped_tail_le_integral {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 10 ≤ u) (hw : exp (sqrt (a / q)) ≤ u) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // u < (riemannXiDivisorZeroValue p).im},
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) ≤
      xiRosserTailIntegral a q u -
        (xiZeroCountingRemainder u - (Real.log u + 17)) * logDampedPower a q u := by
  have hu1 : 1 < u := by linarith
  have hsum := tendsto_sum_xi_height_window (by linarith : 0 ≤ u)
    (summable_xi_logDampedPower ha hq hu1)
  have hD := intervalIntegral_tendsto_integral_Ioi u
    (integrableOn_xi_rosser_density ha hq hu1) tendsto_id
  have hE := intervalIntegral_tendsto_integral_Ioi u
    (integrableOn_logDampedPower_div ha hq hu1) tendsto_id
  apply le_of_tendsto_of_tendsto hsum ((hD.add hE).sub_const
    ((xiZeroCountingRemainder u - (Real.log u + 17)) * logDampedPower a q u))
  filter_upwards [eventually_ge_atTop u] with v hv
  simpa only [id_eq, intervalIntegral.integral_of_le hv, ← integral_Icc_eq_integral_Ioc] using
    sum_xi_damped_window_le_tail_integrals ha (by linarith) hu hv hw

end

end PrimeFactorUnimodality
