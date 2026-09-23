import PrimeFactorUnimodality.Helpers.Analytic.KadiriEndpointRows
import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianBounds
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroNumericalBounds

/-! # Common scalar choices for the three-step bootstrap to six

All three steps use the same smoothing angle, separation parameters and
height cutoff. The endpoint scale and real coordinate remain functions
of the previous and target constants. This module proves their uniform
ranges and the two separation constraints from small kernel enclosures.
No numerical correction or transform margin is assumed to be established.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Common choices for the steps from 56 to 8 to 13/2 to 6, starting at height 10^9. -/
def kadiriSixRow : KadiriEndpointRow :=
  ⟨185573 / 100000, 62 / 100, 439 / 1000, 100000, 109 / 100⟩

/-- The actual billion-height logarithm gives a single upper scale bound. -/
theorem kadiriSix_scale_bounds {r : ℝ} (hr : 6 ≤ r) :
    0 < KadiriEndpointRow.scale r 1000000000 ∧
      KadiriEndpointRow.scale r 1000000000 ≤ (81 / 10000 : ℝ) := by
  have hlog : (20718 / 1000 : ℝ) ≤ log 1000000000 := by
    rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num, log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.1]
  have hden : 0 < r * log 1000000000 := mul_pos (by linarith) (by linarith)
  constructor
  · exact one_div_pos.mpr hden
  · unfold KadiriEndpointRow.scale
    apply (div_le_iff₀ hden).mpr
    have hm := mul_le_mul hr hlog (by norm_num) (by linarith)
    nlinarith only [hm]

/-- The complete harmonic cutoff gives a uniform lower real coordinate at all three steps. -/
theorem kadiriSix_sigma_bounds {R : ℝ} (hR : 13 / 2 ≤ R) :
    (9933 / 10000 : ℝ) ≤ kadiriSixRow.sigma R 1000000000 16 ∧
      kadiriSixRow.sigma R 1000000000 16 ≤ 1 := by
  have hlog : (23 : ℝ) ≤ log (16 * 1000000000 + 100000) := by
    have he : log (16 * 1000000000 : ℝ) = 4 * log 2 + 9 * log 10 := by
      rw [show (16 * 1000000000 : ℝ) = 2 ^ 4 * 10 ^ 9 by norm_num,
        log_mul (by norm_num) (by norm_num), log_pow, log_pow]
      norm_num
    have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 16 * 1000000000)
      (by norm_num : (16 * 1000000000 : ℝ) ≤ 16 * 1000000000 + 100000)
    linarith [dusart_log_ten_bounds.1, log_two_gt_d9]
  have hden : 0 < R * log (16 * 1000000000 + 100000) :=
    mul_pos (by linarith) (by linarith)
  have hm := mul_le_mul hR hlog (by norm_num) (by linarith)
  have hfrac : 1 / (R * log (16 * 1000000000 + 100000)) ≤ (67 / 10000 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hm]
  change (9933 / 10000 : ℝ) ≤ 1 - 1 / (R * log (16 * 1000000000 + 100000)) ∧
    1 - 1 / (R * log (16 * 1000000000 + 100000)) ≤ 1
  constructor
  · linarith
  · linarith [one_div_pos.mpr hden]

/-- Coarse enclosures suffice for both exact kappa constraints, uniformly in the endpoint scale. -/
theorem kadiriSix_kappa_bounds {η σ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 81 / 10000)
    (hσ : 9933 / 10000 ≤ σ)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0)
    (hg' : kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ)) :
    (439 / 1000 : ℝ) ≤ kadiriKappa₂ (185573 / 100000) η (2 * σ - 1) (62 / 100) ∧
      (439 / 1000 : ℝ) ≤ kadiriKappa₃ (185573 / 100000) η (2 * σ - 1) (62 / 100) := by
  let g := kadiriKernel (185573 / 100000) 0
  let m := -kadiriKernel₂ (185573 / 100000) 0
  let b := 2 * σ - 1
  have hb : (4933 / 5000 : ℝ) ≤ b := by dsimp [b]; linarith
  have hbpos : 0 < b := by linarith
  have hgpos : 0 < g := by dsimp [g]; linarith
  have hmpos : 0 ≤ m := neg_kadiriKernel₂_zero_nonneg mossinghoffTrudgian_theta_mem
  have hηm : η ^ 2 * m ≤ (81 / 10000 : ℝ) ^ 2 * 1163 := by
    apply mul_le_mul _ hm hmpos (by positivity)
    nlinarith only [hη, hη']
  have hnum : (1367 / 10 : ℝ) ≤ g * b - η ^ 2 * m / b := by
    have hmain := mul_le_mul hg hb (by norm_num) hgpos.le
    have herr : η ^ 2 * m / b ≤ ((81 / 10000 : ℝ) ^ 2 * 1163) / (4933 / 5000) := by
      calc
        _ ≤ ((81 / 10000 : ℝ) ^ 2 * 1163) / b := div_le_div_of_nonneg_right hηm hbpos.le
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hb
    dsimp [g] at hmain ⊢
    norm_num at herr
    linarith
  have hi₁ : 1 / ((62 / 100 : ℝ) + b) ≤ 1 / ((62 / 100 : ℝ) + 4933 / 5000) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hi₂ : 1 / ((62 / 100 : ℝ) + b) ^ 2 ≤
      1 / ((62 / 100 : ℝ) + 4933 / 5000) ^ 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    gcongr
  have hi₃ : 1 / ((62 / 100 : ℝ) + b) ^ 3 ≤
      1 / ((62 / 100 : ℝ) + 4933 / 5000) ^ 3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    gcongr
  have hden₂ : (1 + 2 * (62 / 100 : ℝ)) * g +
      (1 / (62 / 100 : ℝ) + 1 / ((62 / 100 : ℝ) + b)) * (η ^ 2 * m) ≤ 31133 / 100 := by
    have hfirst := mul_le_mul_of_nonneg_left hg' (by norm_num : (0 : ℝ) ≤ 1 + 2 * (62 / 100))
    have hsecond := mul_le_mul (add_le_add (le_refl (1 / (62 / 100 : ℝ))) hi₁) hηm
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / (62 / 100) + 1 / (62 / 100 + 4933 / 5000))
    dsimp [g] at *
    norm_num at hfirst hsecond ⊢
    linarith
  have hden₃ : (1 / (62 / 100 : ℝ) + (1 + (62 / 100 : ℝ)) / ((62 / 100 : ℝ) + b) ^ 2) * g +
      (1 / (62 / 100 : ℝ) ^ 3 + 1 / ((62 / 100 : ℝ) + b) ^ 3) * (η ^ 2 * m) ≤
        31133 / 100 := by
    have hpart : (1 + (62 / 100 : ℝ)) / ((62 / 100 : ℝ) + b) ^ 2 ≤
        (1 + (62 / 100 : ℝ)) / ((62 / 100 : ℝ) + 4933 / 5000) ^ 2 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hi₂
        (by norm_num : (0 : ℝ) ≤ 1 + (62 / 100))
    have hfirst := mul_le_mul (add_le_add (le_refl (1 / (62 / 100 : ℝ))) hpart) hg' hgpos.le
      (by norm_num : (0 : ℝ) ≤ 1 / (62 / 100) + (1 + (62 / 100)) / (62 / 100 + 4933 / 5000) ^ 2)
    have hsecond := mul_le_mul (add_le_add (le_refl (1 / (62 / 100 : ℝ) ^ 3)) hi₃) hηm
      (by positivity)
      (by norm_num : (0 : ℝ) ≤ 1 / (62 / 100) ^ 3 + 1 / (62 / 100 + 4933 / 5000) ^ 3)
    norm_num at hfirst hsecond ⊢
    linarith
  change (439 / 1000 : ℝ) ≤ (g * b - η ^ 2 * m / b) /
    ((1 + 2 * (62 / 100)) * g + (1 / (62 / 100) + 1 / (62 / 100 + b)) * (η ^ 2 * m)) ∧
    (439 / 1000 : ℝ) ≤ (g * b - η ^ 2 * m / b) /
    ((1 / (62 / 100) + (1 + (62 / 100)) / (62 / 100 + b) ^ 2) * g +
      (1 / (62 / 100) ^ 3 + 1 / (62 / 100 + b) ^ 3) * (η ^ 2 * m))
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    linarith
  · apply (le_div_iff₀ (by positivity)).mpr
    linarith

/-- Only the common kernel enclosures and three endpoint inequalities remain for a row. -/
theorem kadiriSix_valid {R r : ℝ} (hR : 13 / 2 ≤ R) (hr : 6 ≤ r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hcor : kadiriSixRow.correction R r 1000000000 16 mossinghoffTrudgianCoefficient ≤ 0)
    (hlo : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (Finset.range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1)
          (kadiriBootstrapLowerArgument R r 16 100000 1000000000))
    (hhi : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (Finset.range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) 1) :
    kadiriSixRow.Valid R r 1000000000 16 mossinghoffTrudgianCoefficient := by
  obtain ⟨hη, hη'⟩ := kadiriSix_scale_bounds hr
  obtain ⟨hσ, hσ'⟩ := kadiriSix_sigma_bounds hR
  obtain ⟨hk₂, hk₃⟩ := kadiriSix_kappa_bounds hη.le hη' hσ hg.1 hg.2 hm
  refine ⟨by linarith, by linarith, by norm_num, by norm_num [kadiriSixRow], by norm_num,
    mossinghoffTrudgian_theta_mem, by linarith, by linarith,
    by norm_num [kadiriSixRow], by norm_num [kadiriSixRow], by norm_num [kadiriSixRow],
    hk₂, hk₃, ?_, ?_, ?_, by norm_num [kadiriSixRow], hd, he, hcor, ?_, ?_⟩
  · change 0 < kadiriSixRow.sigma R 1000000000 16 -
      KadiriEndpointRow.scale r 1000000000 + 62 / 100
    linarith
  · change 0 ≤ 2 * kadiriSixRow.sigma R 1000000000 16 - 1 - (439 / 1000) * (1 + 2 * (62 / 100))
    linarith
  · change (439 / 1000) * (1 + 2 * (62 / 100)) + 1 - kadiriSixRow.sigma R 1000000000 16 ≤
      (2 * kadiriSixRow.sigma R 1000000000 16 - 1 - (439 / 1000) * (1 + 2 * (62 / 100))) *
        100000 ^ 2
    linarith
  · simpa only [kadiriSixRow, mossinghoffTrudgianCoefficient_zero] using hlo
  · simpa only [kadiriSixRow, mossinghoffTrudgianCoefficient_zero] using hhi

end

end PrimeFactorUnimodality
