import PrimeFactorUnimodality.Helpers.Analytic.KadiriConservativeBudget
import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.PiBounds

/-! # Coarse uniform harmonic-tail budgets for the bootstrap to six

The full positive-harmonic mass is below four. Combine this with the actual
Lehman coefficients above height 25000000 and at fixed separation 100000. These bounds leave
ample slack in the correction polynomial and require no individual
harmonic logarithm evaluation or zero enumeration.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Real

private theorem inverse_pi_height_le : (1 : ℝ) / (π * 100000) ≤ 1 / 300000 := by
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [pi_gt_three]

/-- A single rational bound for the logarithmic slope of the complete tail. -/
theorem kadiriSix_lehman_log_coefficient_le {T : ℝ} (hT : 25000000 ≤ T) :
    xiLehmanLogCoefficient T 100000 ≤ (1 / 100000 : ℝ) := by
  have h := inverse_pi_height_le
  have h' : (1 : ℝ) / (2 * π * T) ≤ 1 / 150000000 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [pi_gt_three]
  unfold xiLehmanLogCoefficient
  linarith only [h, h']

/-- The constant part of the positive-height tail has the same convenient coarse bound. -/
theorem kadiriSix_lehman_affine_constant_le {T : ℝ} (hT : 25000000 ≤ T) :
    xiLehmanAffineConstant T 100000 ≤ (1 / 100000 : ℝ) := by
  have hTpos : 0 < T := by linarith
  calc
    _ = (100000 * (1 / (π * 100000) + 8 / 100000 ^ 2) + 4 / 100000) *
        (1 / T) + 68 / 100000 ^ 2 := by unfold xiLehmanAffineConstant; ring
    _ ≤ (100000 * ((1 / 300000 : ℝ) + 8 / 100000 ^ 2) + 4 / 100000) *
        (1 / 25000000) + 68 / 100000 ^ 2 := by
      gcongr
      nlinarith [pi_gt_three]
    _ ≤ _ := by norm_num

/-- The inverse-height-square pole sum is small on the complete harmonic set. -/
theorem kadiriSix_pole_coefficient_le {T : ℝ} (hT : 25000000 ≤ T) :
    kadiriPoleCoefficient (range 17) mossinghoffTrudgianCoefficient T ≤
      (1 / 1000 : ℝ) := by
  have hs : kadiriPoleCoefficient (range 17) mossinghoffTrudgianCoefficient T ≤
      (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i) / 10000 := by
    rw [kadiriPoleCoefficient, sum_div]
    apply sum_le_sum
    intro i hi
    have hi₁ : (1 : ℝ) ≤ i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mem_erase.mp hi).1
    apply div_le_div_of_nonneg_left
      (mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi)))
      (by norm_num)
    have h : (100 : ℝ) ≤ (i : ℝ) * T := by nlinarith
    nlinarith only [h]
  linarith [sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2]

/-- The complete weighted tail slope is bounded with its zero harmonic excluded. -/
theorem kadiriSix_tail_log_coefficient_le {T : ℝ} (hT : 25000000 ≤ T) :
    kadiriTailLogCoefficient T 100000 (range 17) mossinghoffTrudgianCoefficient ≤
      (1 / 1000 : ℝ) := by
  have hm : (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i) ≤ 4 := by
    linarith [sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2]
  have hn : 0 ≤ ∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i :=
    sum_nonneg (fun i hi =>
      mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi)))
  unfold kadiriTailLogCoefficient
  have h := mul_le_mul (kadiriSix_lehman_log_coefficient_le hT) hm hn
    (by norm_num : (0 : ℝ) ≤ 1 / 100000)
  linarith only [h]

/-- The conservative zero-height term and every positive harmonic fit below one. -/
theorem kadiriSix_tail_constant_le {T : ℝ} (hT : 25000000 ≤ T) :
    kadiriTailConservativeConstant T 100000 (range 17)
      mossinghoffTrudgianCoefficient ≤ 1 := by
  have hz : xiLehmanZeroElementaryBound 100000 ≤ (1 / 2 : ℝ) := by
    unfold xiLehmanZeroElementaryBound
    linarith [log_four_mul_pi_gt_5061_div_2000]
  have hb (i : ℕ) (hi : i ∈ (range 17).erase 0) :
      xiLehmanLogCoefficient T 100000 * log (i : ℝ) +
        xiLehmanAffineConstant T 100000 ≤ (17 / 100000 : ℝ) := by
    have hi₁ : (1 : ℝ) ≤ i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mem_erase.mp hi).1
    have hi₁₆ : (i : ℝ) ≤ 16 := by
      exact_mod_cast (show i ≤ 16 by have h := mem_range.mp (mem_of_mem_erase hi); omega)
    have hl : log (i : ℝ) ≤ 16 := by
      linarith [log_le_sub_one_of_pos (show 0 < (i : ℝ) by linarith)]
    have hp := mul_le_mul (kadiriSix_lehman_log_coefficient_le hT) hl (log_nonneg hi₁)
      (by norm_num : (0 : ℝ) ≤ 1 / 100000)
    linarith only [hp, kadiriSix_lehman_affine_constant_le hT]
  have hs : (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i *
      (xiLehmanLogCoefficient T 100000 * log (i : ℝ) +
        xiLehmanAffineConstant T 100000)) ≤
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
