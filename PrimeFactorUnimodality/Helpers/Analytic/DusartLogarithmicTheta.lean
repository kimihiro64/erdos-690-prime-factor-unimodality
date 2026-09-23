import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserTheta
import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicPsi
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiEndpoint

/-! # Both published theta margins on the full analytic ray

The constant endpoint estimate supplies the upper margin. For the lower
margin use that estimate up to logarithmic height one hundred, then the
decreasing logarithmic psi estimate. The elementary prime-power correction
fits inside the remaining allowance on both ranges. All scalar conditions
are discharged; finite low-zero verification and the finite theta prefix
are the remaining inputs for this theta provider.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- All three prime-power correction terms are bounded by the slowest exponential. -/
theorem dusartThetaRootRelativeCorrection_le_half_exp {x : ℝ} (hx : 1 ≤ x) :
    dusartThetaRootRelativeCorrection x ≤ 18 * exp (-Real.log x / 2) := by
  have hb : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 := Real.exp_le_exp.mpr (by linarith : -2 * Real.log x / 3 ≤ -Real.log x / 2)
  have h4 := Real.exp_le_exp.mpr (by linarith : -4 * Real.log x / 5 ≤ -Real.log x / 2)
  have hc : Real.log 4 + 4 ≤ 6 := by
    have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  unfold dusartThetaRootRelativeCorrection
  calc
    _ ≤ 6 * (exp (-Real.log x / 2) + exp (-2 * Real.log x / 3) +
        exp (-4 * Real.log x / 5)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by linarith

/-- Above logarithmic height one hundred the root correction costs at most one hundredth. -/
theorem dusartThetaRootRelativeCorrection_le_logarithmic {x : ℝ}
    (hx : 1 < x) (hb : 100 ≤ Real.log x) :
    dusartThetaRootRelativeCorrection x ≤ (1 / 100 : ℝ) / Real.log x := by
  have hbpos : 0 < Real.log x := Real.log_pos hx
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hb 3
  calc
    _ ≤ 18 * exp (-Real.log x / 2) := dusartThetaRootRelativeCorrection_le_half_exp hx.le
    _ ≤ 18 * (384 / Real.log x ^ 4) := mul_le_mul_of_nonneg_left
      (dusartLog_half_exp_le hbpos) (by norm_num)
    _ = 6912 / Real.log x ^ 4 := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (pow_pos hbpos 4) hbpos).mpr
      nlinarith only [hbpos, mul_nonneg
        (by linarith : 0 ≤ Real.log x ^ 3 - 100 ^ 3) hbpos.le]

/-- The original endpoint also controls the entire normalized prime-power correction. -/
theorem dusartThetaRootRelativeCorrection_endpoint_le {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x) :
    dusartThetaRootRelativeCorrection x ≤ (3 / 200000 : ℝ) := by
  have he := dusartEndpoint_half_log_decay_le (by linarith : (1440000000000 : ℝ) ≤ x)
  rw [show -(1 / 2) * Real.log x = -Real.log x / 2 by ring] at he
  exact (dusartThetaRootRelativeCorrection_le_half_exp (by linarith : 1 ≤ x)).trans
    (by linarith)

/-- Both exact published margins hold at every point of the analytic ray. -/
theorem dusartTheta_margins_of_billion_low_gap {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    Chebyshev.theta x - x < x / 36260 ∧
      |Chebyshev.theta x - x| < (12323 / 10000 : ℝ) * x / Real.log x := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hbpos : 0 < Real.log x := Real.log_pos hx1
  have hu := abs_psi_sub_div_lt_of_billion_low_gap hx hgap
  apply dusartTheta_margins_of_normalized_psi hxpos le_rfl hu
  by_cases hb : 100 ≤ Real.log x
  · have hp := abs_psi_sub_div_le_logarithmic_of_billion_low_gap hx1 hb hgap
    have hc := dusartThetaRootRelativeCorrection_le_logarithmic hx1 hb
    calc
      _ ≤ (103 / 100 : ℝ) / Real.log x + (1 / 100 : ℝ) / Real.log x := add_le_add hp hc
      _ = (104 / 100 : ℝ) / Real.log x := by ring
      _ < _ := (div_lt_div_iff_of_pos_right hbpos).mpr (by norm_num)
  · have hc := dusartThetaRootRelativeCorrection_endpoint_le hx
    calc
      _ < (1 / 36260 : ℝ) + 3 / 200000 := add_lt_add_of_lt_of_le hu hc
      _ < (12323 / 10000 : ℝ) / 100 := by norm_num
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hbpos (le_of_not_ge hb)

/-- Finite theta data and finite low-zero verification suffice for the global theta provider. -/
theorem hasDusartThetaBounds_of_finite_and_billion_low_gap
    (finite : HasDusartSymmetricThetaBoundsBelow 1441000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : HasDusartThetaBounds := by
  apply hasDusartThetaBounds_of_below_and_above finite
  exact ⟨fun x hx => (dusartTheta_margins_of_billion_low_gap hx hgap).1,
    fun x _ hx => (dusartTheta_margins_of_billion_low_gap hx hgap).2⟩

end

end PrimeFactorUnimodality
