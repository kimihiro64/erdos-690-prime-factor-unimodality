import PrimeFactorUnimodality.Helpers.Analytic.KadiriGammaBudget
import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.PiBounds

/-! # A uniform negative Gamma residual for the bootstrap to six

Retain the negative first harmonic, bound all remaining logarithms above
by one, and use the exact coefficient mass. The previously proved
height-decaying Gamma error is small at the selected cutoff. This proves
a signed bound without evaluating a list of transcendental expressions.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Real

private theorem harmonic_log_le {T : ℝ} (hT : 25000000 ≤ T) {i : ℕ} (hi : i < 17) :
    log ((i : ℝ) / 2 + 2 / T) - log π ≤ 1 := by
  have hTpos : 0 < T := by linarith
  have he : (2 : ℝ) / T ≤ 2 / 25000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  have hi' : (i : ℝ) ≤ 16 := by exact_mod_cast (show i ≤ 16 by omega)
  have hx : 0 < (i : ℝ) / 2 + 2 / T := by positivity
  rw [← log_div hx.ne' pi_pos.ne']
  apply (log_le_iff_le_exp (div_pos hx pi_pos)).mpr
  apply (div_le_iff₀ pi_pos).mpr
  have hm := mul_le_mul_of_nonneg_right exp_one_gt_d9.le pi_pos.le
  nlinarith [pi_gt_three]

private theorem first_log_le {T : ℝ} (hT : 25000000 ≤ T) :
    log ((1 : ℝ) / 2 + 2 / T) - log π ≤ -(163 / 100 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have he : (2 : ℝ) / T ≤ 2 / 25000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  have h := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / 2 + 2 / T)
  linarith [log_pi_gt_57_div_50]

/-- The actual weighted logarithms have a uniform negative margin at the initial height. -/
theorem kadiriSix_gamma_log_sum_le {T : ℝ} (hT : 25000000 ≤ T) :
    mossinghoffTrudgianCoefficient 0 * (log 2 - log π) +
      (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i *
        (log ((i : ℝ) / 2 + 2 / T) - log π)) ≤ -(149 / 100 : ℝ) := by
  let S := (range 17).erase 0
  let a := mossinghoffTrudgianCoefficient
  let f := fun i : ℕ => a i * (log ((i : ℝ) / 2 + 2 / T) - log π)
  have h₁ : 1 ∈ S := by simp [S]
  have ha : ∀ i ∈ S, 0 ≤ a i := fun i hi =>
    mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi))
  have hrest : (∑ i ∈ S.erase 1, f i) ≤ ∑ i ∈ S.erase 1, a i := by
    apply sum_le_sum
    intro i hi
    have hiS := mem_of_mem_erase hi
    simpa [f] using mul_le_mul_of_nonneg_left
      (harmonic_log_le hT (mem_range.mp (mem_of_mem_erase hiS))) (ha i hiS)
  have hmass : (∑ i ∈ S.erase 1, a i) ≤ (1783 / 1000 : ℝ) := by
    have he := add_sum_erase S a h₁
    have hb : (∑ i ∈ S, a i) ≤ (3524 / 1000 : ℝ) :=
      sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2
    have hf : (1741 / 1000 : ℝ) ≤ a 1 := mossinghoffTrudgianCoefficient_one_bounds.1
    linarith
  have hfirst : f 1 ≤ (1741 / 1000 : ℝ) * (-(163 / 100)) := by
    have h := mul_le_mul_of_nonneg_left (first_log_le hT) (ha 1 h₁)
    have h' := mul_le_mul_of_nonpos_right mossinghoffTrudgianCoefficient_one_bounds.1
      (by norm_num : (-(163 / 100) : ℝ) ≤ 0)
    simpa only [f, Nat.cast_one] using h.trans h'
  have hzero : log 2 - log π ≤ -(44 / 100 : ℝ) := by
    linarith [log_pi_gt_57_div_50, log_two_lt_d9]
  rw [mossinghoffTrudgianCoefficient_zero, one_mul]
  change log 2 - log π + ∑ i ∈ S, f i ≤ _
  rw [← add_sum_erase S f h₁]
  linarith only [hfirst, hrest, hmass, hzero]

/-- The reciprocal-weight error uses no more than the total positive-frequency mass. -/
theorem kadiriSix_reciprocal_mass_le :
    (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i / (i : ℝ)) ≤ 4 := by
  have hs : (∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i / (i : ℝ)) ≤
      ∑ i ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient i := by
    apply sum_le_sum
    intro i hi
    have hi₁ : (1 : ℝ) ≤ i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mem_erase.mp hi).1
    exact div_le_self
      (mossinghoffTrudgianCoefficient_nonneg (mem_range.mp (mem_of_mem_erase hi))) hi₁
  linarith [sum_mossinghoffTrudgianCoefficient_erase_zero_bounds.2]

/-- The complete Gamma residual is negative on the entire real-coordinate range used by the rows. -/
theorem kadiriSix_gamma_residual_le {T σ : ℝ} (hT : 25000000 ≤ T) (hσ : 9922 / 10000 ≤ σ) :
    kadiriGammaResidual (437 / 1000) σ T (range 17)
      mossinghoffTrudgianCoefficient ≤ -(1 / 4 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hb := kadiriGammaResidual_le_height (κ := 437 / 1000) (σ := σ)
    (by linarith : (0 : ℝ) < T) (range 17) (by simp)
    mossinghoffTrudgianCoefficient
    (fun i hi => mossinghoffTrudgianCoefficient_nonneg (mem_range.mp hi))
  have hzero : (437 / 1000 : ℝ) / (σ + 2) ≤ 147 / 1000 := by
    apply (div_le_iff₀ (by linarith : 0 < σ + 2)).mpr
    linarith
  have hlog := mul_le_mul_of_nonneg_left (kadiriSix_gamma_log_sum_le hT)
    (by norm_num : (0 : ℝ) ≤ (1 - 437 / 1000) / 2)
  have herror := mul_le_mul_of_nonneg_left kadiriSix_reciprocal_mass_le
    (by positivity : (0 : ℝ) ≤ 2 * (1 + 437 / 1000) / T)
  simp only [mossinghoffTrudgianCoefficient_zero, one_mul] at hb hlog
  have he : 2 * (1 + 437 / 1000 : ℝ) / T ≤ 2 * (1 + 437 / 1000) / 25000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  linarith only [hb, hlog, hzero, herror, he]

end

end PrimeFactorUnimodality
