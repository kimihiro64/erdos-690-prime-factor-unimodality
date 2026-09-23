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

/-- The harmonic logarithm at the reduced cutoff has a rational upper bound. -/
theorem kadiriSix_cutoff_log_le : log (16 * 25000000 + 100000 : ℝ) ≤ 991 / 50 := by
  have he : (16 * 25000000 + 100000 : ℝ) = (2 ^ 4 * 25000000) * (1 + 1 / 4000) := by
    norm_num
  rw [he, log_mul (by norm_num) (by norm_num),
    log_mul (by norm_num) (by norm_num), log_pow]
  norm_num
  have hl := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 4000)
  norm_num at hl
  linarith [dusart_log_outer_reduced_bounds.2, log_two_lt_d9]

/-- The same rational argument interval works at every larger height. -/
theorem kadiriSix_argument_mem {T R r l : ℝ} (hT : 25000000 ≤ T)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hl : l ≤ (r / R) * ((17034 / 1000) / (991 / 50))) :
    kadiriBootstrapLowerArgument R r 16 100000 T ∈ Set.Icc l 1 := by
  have hL := dusart_log_outer_reduced_bounds.1
  have hA : 0 < log (16 * 25000000 + 100000 : ℝ) := log_pos (by norm_num)
  have hratio : (17034 / 1000 : ℝ) / (991 / 50) ≤
      log T / log (16 * T + 100000 : ℝ) := by
    calc
      _ ≤ log 25000000 / (991 / 50) := div_le_div_of_nonneg_right hL (by norm_num)
      _ ≤ log 25000000 / log (16 * 25000000 + 100000 : ℝ) :=
        div_le_div_of_nonneg_left (by linarith) hA kadiriSix_cutoff_log_le
      _ ≤ _ := log_div_log_affine_le (by norm_num) (by norm_num) (by norm_num) hT
  have hratio' : log T / log (16 * T + 100000 : ℝ) ≤ 1 :=
    log_div_log_affine_le_one (by norm_num) (by norm_num) (by linarith)
  have hr' : r / R ≤ 1 := (div_le_iff₀ hR).mpr (by linarith)
  constructor
  · exact hl.trans (mul_le_mul_of_nonneg_left hratio (div_nonneg hr hR.le))
  · change (r / R) * (log T / log (16 * T + 100000 : ℝ)) ≤ 1
    calc
      _ ≤ (r / R) * 1 := mul_le_mul_of_nonneg_left hratio' (div_nonneg hr hR.le)
      _ ≤ 1 := by simpa using hr'

/-- The reduced chain's three moving arguments lie in common rational intervals. -/
theorem kadiriSix_three_argument_intervals {T : ℝ} (hT : 25000000 ≤ T) :
    kadiriBootstrapLowerArgument 69 8 16 100000 T ∈ Set.Icc (9 / 100 : ℝ) 1 ∧
      kadiriBootstrapLowerArgument 8 (13 / 2) 16 100000 T ∈
        Set.Icc (69 / 100 : ℝ) 1 ∧
      kadiriBootstrapLowerArgument (13 / 2) 6 16 100000 T ∈
        Set.Icc (79 / 100 : ℝ) 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply kadiriSix_argument_mem hT <;> norm_num

/-- The common leading logarithmic coefficient fits below one rational constant. -/
theorem kadiriSix_log_coefficient_le
    (hg : kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ)) :
    kadiriBootstrapLogCoefficient (185573 / 100000) (437 / 1000)
      (range 17) mossinghoffTrudgianCoefficient ≤ 138 := by
  have hg₀ := (kadiriKernel_zero_pos mossinghoffTrudgian_theta_mem).le
  have hs₀ : 0 ≤ ∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i :=
    sum_nonneg (fun i hi =>
      mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi)))
  have hs := sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2
  unfold kadiriBootstrapLogCoefficient
  calc
    _ ≤ (1388 / 10 : ℝ) * (1 - 437 / 1000) / 2 * (3524 / 1000) := by gcongr
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
