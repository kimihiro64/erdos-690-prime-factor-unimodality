/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Integrability

/-! # Explicit rational bounds for the complete Bernoulli power tail

The coefficient absolute sum bounds each normalized profile on the unit
interval. Unlike the compactness constant in the original WIP integrability
proof, this bound is a finite rational expression at each specified order.
The integral estimate retains the whole improper tail.
-/

namespace Polynomial

/-- Compute the normalized coefficient majorant without traversing polynomial support. -/
def bernoulliCoeffBudget (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1),
    |(_root_.bernoulli (k - j) * k.choose j) / (k.factorial : ℚ)|

noncomputable section

/-- An explicit rational majorant for the normalized periodic profile. -/
def bernoulliCoeffBound (k : ℕ) : ℚ :=
  ∑ j ∈ (bernoulliNormalized k).support, |(bernoulliNormalized k).coeff j|

/-- The computable finite formula is exactly the analytic coefficient majorant. -/
theorem bernoulliCoeffBound_eq_budget (k : ℕ) :
    bernoulliCoeffBound k = bernoulliCoeffBudget k := by
  have hc (j : ℕ) : (bernoulliNormalized k).coeff j =
      if j ≤ k then (_root_.bernoulli (k - j) * k.choose j) / (k.factorial : ℚ) else 0 := by
    rw [bernoulliNormalized, coeff_C_mul, coeff_bernoulli]
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  have hs : (bernoulliNormalized k).support ⊆ Finset.range (k + 1) := by
    intro j hj
    have hj' := mem_support_iff.mp hj
    rw [hc] at hj'
    split_ifs at hj' with h
    · exact Finset.mem_range.mpr (by omega)
    · exact (hj' rfl).elim
  unfold bernoulliCoeffBound bernoulliCoeffBudget
  calc
    _ = ∑ j ∈ Finset.range (k + 1), |(bernoulliNormalized k).coeff j| := by
      apply Finset.sum_subset hs
      intro j _ hnot
      rw [notMem_support_iff.mp hnot, abs_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc, ite_eq_left (by have := Finset.mem_range.mp hj; omega)]

/-- The coefficient majorant is nonnegative at every order. -/
theorem bernoulliCoeffBound_nonneg (k : ℕ) : 0 ≤ bernoulliCoeffBound k :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Fractional parts lie in the unit interval, so the rational coefficient sum suffices. -/
theorem abs_bernoulliPeriodic_le_coeffBound (k : ℕ) (x : ℝ) :
    |bernoulliPeriodic k x| ≤ (bernoulliCoeffBound k : ℝ) := by
  rw [bernoulliPeriodic, bernoulliNormalizedReal, eval_map, eval₂_eq_sum, sum_def]
  calc
    _ ≤ ∑ j ∈ (bernoulliNormalized k).support,
        |((bernoulliNormalized k).coeff j : ℝ) * Int.fract x ^ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (bernoulliNormalized k).support,
        |((bernoulliNormalized k).coeff j : ℝ)| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_pow, abs_of_nonneg (Int.fract_nonneg x)]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (pow_le_one₀ (Int.fract_nonneg x) (Int.fract_lt_one x).le)
    _ = _ := by push_cast [bernoulliCoeffBound]; rfl

/-- Explicit majorant for the full absolutely convergent periodic power tail. -/
theorem norm_bernoulliPeriodic_cpow_tail_le (k : ℕ) {a : ℝ} {z : ℂ}
    (ha : 0 < a) (hz : z.re < -1) :
    ‖∫ x in Set.Ioi a, (bernoulliPeriodic k x : ℂ) * (x : ℂ) ^ z‖ ≤
      (bernoulliCoeffBound k : ℝ) * (-a ^ (z.re + 1) / (z.re + 1)) := by
  let C : ℝ := bernoulliCoeffBound k
  have hInt := ((bernoulliPeriodic_cpow_tail_bound k).choose_spec.2 a z ha hz).1
  have hMajor := (integrableOn_Ioi_rpow_of_lt hz ha).const_mul C
  have hBound : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioi a),
      ‖(bernoulliPeriodic k x : ℂ) * (x : ℂ) ^ z‖ ≤ C * x ^ z.re := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx),
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_bernoulliPeriodic_le_coeffBound k x)
      (Real.rpow_nonneg (ha.trans hx).le _)
  calc
    _ ≤ ∫ x in Set.Ioi a, ‖(bernoulliPeriodic k x : ℂ) * (x : ℂ) ^ z‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioi a, C * x ^ z.re :=
      MeasureTheory.integral_mono_ae hInt.norm hMajor hBound
    _ = _ := by rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hz ha]

end

end Polynomial
