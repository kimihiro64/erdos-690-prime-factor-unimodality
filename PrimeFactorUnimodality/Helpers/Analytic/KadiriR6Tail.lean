import PrimeFactorUnimodality.Helpers.Analytic.KadiriConservativeBudget
import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.PiBounds

/-! # Coarse uniform harmonic-tail budgets for the bootstrap to six

The full positive-harmonic mass is below four. Combine this with the actual
Lehman coefficients at the fixed height and cutoff. These bounds leave
ample slack in the correction polynomial and require no individual
harmonic logarithm evaluation or zero enumeration.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Real

private theorem inverse_pi_height_le : (1 : ℝ) / (π * 100000) ≤ 1 / 300000 := by
  apply one_div_le_one_div_of_le (by norm_num)
  linarith [pi_gt_three]

/-- A single rational bound for the logarithmic slope of the complete tail. -/
theorem kadiriSix_lehman_log_coefficient_le :
    xiLehmanLogCoefficient 1000000000 100000 ≤ (1 / 100000 : ℝ) := by
  have h := inverse_pi_height_le
  have h' : (1 : ℝ) / (2 * π * 1000000000) ≤ 1 / 6000000000 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [pi_gt_three]
  unfold xiLehmanLogCoefficient
  linarith only [h, h']

/-- The constant part of the positive-height tail has the same convenient coarse bound. -/
theorem kadiriSix_lehman_affine_constant_le :
    xiLehmanAffineConstant 1000000000 100000 ≤ (1 / 100000 : ℝ) := by
  unfold xiLehmanAffineConstant
  linarith only [inverse_pi_height_le]

/-- The inverse-height-square pole sum is small on the complete harmonic set. -/
theorem kadiriSix_pole_coefficient_le :
    kadiriPoleCoefficient (range 17) mossinghoffTrudgianCoefficient 1000000000 ≤
      (1 / 1000 : ℝ) := by
  have hs : kadiriPoleCoefficient (range 17) mossinghoffTrudgianCoefficient 1000000000 ≤
      (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i) / 10000 := by
    rw [kadiriPoleCoefficient, sum_div]
    apply sum_le_sum
    intro i hi
    have hi₁ : (1 : ℝ) ≤ i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mem_erase.mp hi).1
    apply div_le_div_of_nonneg_left
      (mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi)))
      (by norm_num)
    have h : (100 : ℝ) ≤ (i : ℝ) * 1000000000 := by linarith
    nlinarith only [h]
  linarith [sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2]

/-- The complete weighted tail slope is bounded with its zero harmonic excluded. -/
theorem kadiriSix_tail_log_coefficient_le :
    kadiriTailLogCoefficient 1000000000 100000 (range 17) mossinghoffTrudgianCoefficient ≤
      (1 / 1000 : ℝ) := by
  have hm : (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i) ≤ 4 := by
    linarith [sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2]
  have hn : 0 ≤ ∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i :=
    sum_nonneg (fun i hi =>
      mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi)))
  unfold kadiriTailLogCoefficient
  have h := mul_le_mul kadiriSix_lehman_log_coefficient_le hm hn
    (by norm_num : (0 : ℝ) ≤ 1 / 100000)
  linarith only [h]

/-- The conservative zero-height term and every positive harmonic fit below one. -/
theorem kadiriSix_tail_constant_le :
    kadiriTailConservativeConstant 1000000000 100000 (range 17)
      mossinghoffTrudgianCoefficient ≤ 1 := by
  have hz : xiLehmanZeroElementaryBound 100000 ≤ (1 / 2 : ℝ) := by
    unfold xiLehmanZeroElementaryBound
    linarith [log_four_mul_pi_gt_5061_div_2000]
  have hb (i : ℕ) (hi : i ∈ (range 17).erase 0) :
      xiLehmanLogCoefficient 1000000000 100000 * log (i : ℝ) +
        xiLehmanAffineConstant 1000000000 100000 ≤ (17 / 100000 : ℝ) := by
    have hi₁ : (1 : ℝ) ≤ i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mem_erase.mp hi).1
    have hi₁₆ : (i : ℝ) ≤ 16 := by
      exact_mod_cast (show i ≤ 16 by have h := mem_range.mp (mem_of_mem_erase hi); omega)
    have hl : log (i : ℝ) ≤ 16 := by
      linarith [log_le_sub_one_of_pos (show 0 < (i : ℝ) by linarith)]
    have hp := mul_le_mul kadiriSix_lehman_log_coefficient_le hl (log_nonneg hi₁)
      (by norm_num : (0 : ℝ) ≤ 1 / 100000)
    linarith only [hp, kadiriSix_lehman_affine_constant_le]
  have hs : (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i *
      (xiLehmanLogCoefficient 1000000000 100000 * log (i : ℝ) +
        xiLehmanAffineConstant 1000000000 100000)) ≤
      (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i) * (17 / 100000) := by
    rw [sum_mul]
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hb i hi)
      (mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi)))
  have hm := sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2
  unfold kadiriTailConservativeConstant
  rw [mossinghoffTrudgianCoefficient_zero, one_mul]
  linarith only [hz, hs, hm]

end

end PrimeFactorUnimodality
