import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Correction

/-! # Rational transform points suffice for the bootstrap to six

Bound the exact logarithmic arguments in rational intervals, retain the
proved endpoint minimum of the signed transform, and use a conservative
first-harmonic coefficient. The resulting checks involve only four small
rational transform points, not a scale grid or logarithmic point family.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Real

/-- The large logarithm in the exact moving coordinate has a rational upper bound. -/
theorem kadiriSix_cutoff_log_le : log (16 * 1000000000 + 100000 : ℝ) ≤ 47 / 2 := by
  have he : (16 * 1000000000 + 100000 : ℝ) = (2 ^ 4 * 10 ^ 9) * (1 + 1 / 160000) := by
    norm_num
  rw [he, log_mul (by norm_num) (by norm_num),
    log_mul (by norm_num) (by norm_num), log_pow, log_pow]
  norm_num
  have hl := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 160000)
  norm_num at hl
  linarith [dusart_log_ten_bounds.2, log_two_lt_d9]

/-- A rational ratio comparison locates the actual transform argument, including its upper end. -/
theorem kadiriSix_argument_mem {R r l : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hl : l ≤ (r / R) * ((20718 / 1000) / (47 / 2))) :
    kadiriBootstrapLowerArgument R r 16 100000 1000000000 ∈ Set.Icc l 1 := by
  have hL : (20718 / 1000 : ℝ) ≤ log 1000000000 := by
    rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num, log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.1]
  have hA : 0 < log (16 * 1000000000 + 100000 : ℝ) := log_pos (by norm_num)
  have hratio : (20718 / 1000 : ℝ) / (47 / 2) ≤
      log 1000000000 / log (16 * 1000000000 + 100000 : ℝ) := by
    calc
      _ ≤ log 1000000000 / (47 / 2) := div_le_div_of_nonneg_right hL (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith) hA kadiriSix_cutoff_log_le
  have hratio' : log 1000000000 / log (16 * 1000000000 + 100000 : ℝ) ≤ 1 := by
    exact log_div_log_affine_le_one (by norm_num : (1 : ℝ) ≤ 16)
      (by norm_num : (0 : ℝ) ≤ 100000) (by norm_num : (1 : ℝ) < 1000000000)
  have hr' : r / R ≤ 1 := (div_le_iff₀ hR).mpr (by linarith)
  constructor
  · exact hl.trans (mul_le_mul_of_nonneg_left hratio (div_nonneg hr hR.le))
  · change (r / R) * (log 1000000000 / log (16 * 1000000000 + 100000 : ℝ)) ≤ 1
    calc
      _ ≤ (r / R) * 1 := mul_le_mul_of_nonneg_left hratio' (div_nonneg hr hR.le)
      _ ≤ 1 := by simpa using hr'

/-- The exact logarithmic arguments for all three steps lie in the selected rational intervals. -/
theorem kadiriSix_three_argument_intervals :
    kadiriBootstrapLowerArgument 56 8 16 100000 1000000000 ∈ Set.Icc (12 / 100 : ℝ) 1 ∧
      kadiriBootstrapLowerArgument 8 (13 / 2) 16 100000 1000000000 ∈
        Set.Icc (71 / 100 : ℝ) 1 ∧
      kadiriBootstrapLowerArgument (13 / 2) 6 16 100000 1000000000 ∈
        Set.Icc (81 / 100 : ℝ) 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply kadiriSix_argument_mem <;> norm_num

/-- The common leading logarithmic coefficient fits below one rational constant. -/
theorem kadiriSix_log_coefficient_le
    (hg : kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ)) :
    kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (range 17) mossinghoffTrudgianCoefficient ≤ 138 := by
  have hg₀ := (kadiriKernel_zero_pos mossinghoffTrudgian_theta_mem).le
  have hs₀ : 0 ≤ ∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i :=
    sum_nonneg (fun i hi =>
      mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi)))
  have hs := sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2
  unfold kadiriBootstrapLogCoefficient
  calc
    _ ≤ (1388 / 10 : ℝ) * (1 - 439 / 1000) / 2 * (3524 / 1000) := by gcongr
    _ ≤ 138 := by norm_num

/-- Rounding the first harmonic downward is justified by the actual nonnegative kernel integral. -/
theorem kadiriSix_rounded_gap_le (w : ℝ) :
    kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) w ≤
      kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) w := by
  unfold kadiriTransformGapClosedForm
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_right mossinghoffTrudgianCoefficient_one_bounds.1
      (kadiriKernelExpIntegral_nonneg mossinghoffTrudgian_theta_mem (w - 1))) _

/-- Two rational-point margins control the actual signed transform throughout their interval. -/
theorem kadiriSix_gap_le_of_rounded_endpoints {b l w : ℝ} (hw : w ∈ Set.Icc l 1)
    (hlo : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) l)
    (hhi : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) 1) :
    b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) w := by
  have h := min_kadiriTransformGap_endpoints_le mossinghoffTrudgian_theta_mem
    (by norm_num : (0 : ℝ) < 1) mossinghoffTrudgianCoefficient_one_pos hw
  simp only [kadiriTransformGap_eq_closedForm mossinghoffTrudgian_theta_mem] at h
  exact (le_min (hlo.trans (kadiriSix_rounded_gap_le l))
    (hhi.trans (kadiriSix_rounded_gap_le 1))).trans h

end

end PrimeFactorUnimodality
