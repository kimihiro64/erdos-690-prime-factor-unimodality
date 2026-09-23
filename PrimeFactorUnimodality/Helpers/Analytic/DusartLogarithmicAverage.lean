import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPolynomialTail
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenAverage
import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicScalars
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroNumericalBounds

/-! # An actual psi average with decreasing logarithmic error

Use order-three smoothing, the proved region constant fifty-six, and
fourth-order polynomial damping. The full high tail, low block and
elementary correction fit within half the reciprocal logarithm for a
whole interval of smoothing steps. Only the finite low-height critical
line condition remains as a zero-location input.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real intervalIntegral

/-- The actual complete high sum fits within six hundredths of the reciprocal logarithm. -/
theorem norm_dusartBoxXiHighSum_div_le_logarithmic {s x : ℝ}
    (hx : 1 < x) (hb : 50 ≤ Real.log x)
    (hs₀ : 1 / (60 * Real.log x) ≤ s) (hs₁ : s ≤ 1 / (20 * Real.log x)) :
    ‖dusartBoxXiHighSum 0 (s * x) x 1000000000‖ / x ≤
      (3 / 50 : ℝ) / Real.log x := by
  have hlpos : 0 < Real.log x := Real.log_pos hx
  have hspos : 0 < s := (by positivity : 0 < 1 / (60 * Real.log x)).trans_le hs₀
  have hregion : ∀ z : RiemannXiDivisorZeroIndex,
      (1000000000 : ℝ) ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (56 * Real.log |(riemannXiDivisorZeroValue z).im|) := by
    intro z hz
    have hg := xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero z) (by norm_num; exact hz)
    linarith
  have hh := norm_dusartBoxXiHighSum_div_le_polynomial 0 4 hspos hx
    (by norm_num : (0 : ℝ) < 56) (by norm_num : (10 : ℝ) < 1000000000) hregion
  norm_num at hh
  have hcoeff := dusartLog_coefficient_le hb hs₀ hs₁
  calc
    _ ≤ (8 * (1 + 3 * s) ^ 4 / s ^ 3) *
        (576 / (Real.log x / 56) ^ 4) * xiRosserPowerTailBound 3 1000000000 := hh
    _ ≤ (8 * (1 + 3 * s) ^ 4 / s ^ 3) *
        (576 / (Real.log x / 56) ^ 4) * (4 / 10 ^ 18) :=
      mul_le_mul_of_nonneg_left xiRosserPowerTailBound_three_billion_le (by positivity)
    _ ≤ (8 * (11 / 10 : ℝ) ^ 4 * (60 * Real.log x) ^ 3) *
        (576 / (Real.log x / 56) ^ 4) * (4 / 10 ^ 18) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by norm_num)
    _ ≤ _ := dusartLog_high_le hlpos

/-- A uniform step window gives a decreasing bound for the actual normalized psi average. -/
theorem abs_dusartPsiAverageError_div_le_logarithmic {s x : ℝ}
    (hx : 1 < x) (hb : 50 ≤ Real.log x)
    (hs₀ : 1 / (60 * Real.log x) ≤ s) (hs₁ : s ≤ 1 / (20 * Real.log x))
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |dusartPsiAverageError 3 (s * x) x| / x ≤ 1 / (2 * Real.log x) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hlpos : 0 < Real.log x := Real.log_pos hx
  have hspos : 0 < s := (by positivity : 0 < 1 / (60 * Real.log x)).trans_le hs₀
  have hl := norm_dusartBox_low_div_le_frozen 0 hspos hx le_rfl
    (by norm_num : (10 : ℝ) ≤ 10) (by norm_num : (10 : ℝ) < 1000000000)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hgap)
  have hlow : ((1 + 3 * s) * exp (-(1 / 2) * Real.log x)) *
      xiLowReciprocalNormBound 10 1000000000 (1 / 2) ≤ (6 / 25 : ℝ) / Real.log x := by
    calc
      _ ≤ ((1 + 3 * s) * exp (-(1 / 2) * Real.log x)) * 70 :=
        mul_le_mul_of_nonneg_left xiLowReciprocalNormBound_billion_half_le (by positivity)
      _ ≤ ((11 / 10 : ℝ) * exp (-(1 / 2) * Real.log x)) * 70 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (dusartLog_width_le hb hs₁) (Real.exp_pos _).le) (by norm_num)
      _ = 77 * exp (-Real.log x / 2) := by
        rw [show -(1 / 2) * Real.log x = -Real.log x / 2 by ring]
        ring
      _ ≤ _ := dusartLog_low_le hb
  have hu := norm_dusartBoxXiHighSum_div_le_logarithmic hx hb hs₀ hs₁
  have hz : ‖smoothedXiPairedSum (fun u => (dusartBoxWeight 0 (s * x) x u : ℂ))
      (dusartBoxSupport 0 (s * x) x) 0‖ / x ≤
        (6 / 25 : ℝ) / Real.log x + (3 / 50 : ℝ) / Real.log x := by
    rw [smoothedXiPairedSum_box_eq_low_add_high 0 (mul_pos hspos hxpos) hx 1000000000]
    exact (div_le_div_of_nonneg_right (norm_add_le _ _) hxpos.le).trans
      (by rw [add_div]; exact add_le_add (hl.trans hlow) hu)
  have hx2 : 2 ≤ x := by
    have he := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hxpos] at he
    linarith
  have hcorr := (dusartLog_correction_le hx2).trans
    (by simpa only [Real.exp_log hxpos] using dusartLog_four_div_exp_le hb)
  have he := div_le_div_of_nonneg_right
    (abs_dusartPsiAverageError_le_zero_sum 0 (mul_pos hspos hxpos) hx) hxpos.le
  calc
    _ ≤ (‖smoothedXiPairedSum (fun u => (dusartBoxWeight 0 (s * x) x u : ℂ))
        (dusartBoxSupport 0 (s * x) x) 0‖ + 1 / (2 * (x ^ 2 - 1)) +
          Real.log (2 * π)) / x := he
    _ = ‖smoothedXiPairedSum (fun u => (dusartBoxWeight 0 (s * x) x u : ℂ))
        (dusartBoxSupport 0 (s * x) x) 0‖ / x +
          (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x := by ring
    _ ≤ (6 / 25 : ℝ) / Real.log x + (3 / 50 : ℝ) / Real.log x +
        (4 / 25 : ℝ) / Real.log x := add_le_add hz hcorr
    _ ≤ _ := by apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log x)).mpr; field_simp; norm_num

end

end PrimeFactorUnimodality
