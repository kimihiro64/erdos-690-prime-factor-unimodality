import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.FinsetAbel

/-! # Exact interfaces and endpoint regressions for integrated zero verification -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset MeasureTheory

variable {ι : Type*} {a b : ℝ} {f g : ℝ → ℝ}

example (s : Finset ι) (r c : ι → ℝ)
    (hg : IntegrableOn g (Set.Icc a b)) :
    IntegrableOn (fun x => (∑ i ∈ s with r i ≤ x, c i) * g x) (Set.Icc a b) := by
  exact Finset.integrableOn_sum_filter_mul s r c hg

example (s : Finset ι) (r c : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc a b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (g x) x)
    (hg : IntegrableOn g (Set.Icc a b)) :
    ∑ i ∈ s, c i * f (r i) = (∑ i ∈ s, c i) * f b -
      ∫ x in Set.Icc a b, (∑ i ∈ s with r i ≤ x, c i) * g x := by
  exact Finset.sum_mul_eq_sum_mul_sub_integral_count s r c hr hf hg

example (s : Finset ι) (r : ι → ℝ) :
    IntegrableOn (fun x => ((s.filter (fun i => r i ≤ x)).card : ℝ)) (Set.Icc a b) := by
  exact Finset.integrableOn_count_le s r

example (s : Finset ι) (r : ι → ℝ) (hab : a ≤ b)
    (hr : ∀ i ∈ s, r i ≤ b) :
    (∫ x in Set.Icc a b, ((s.filter (fun i => r i ≤ x)).card : ℝ)) =
      ∑ i ∈ s, (b - max a (r i)) := by
  exact Finset.integral_count_le_eq_sum_sub_max s r hab hr


example : (∫ x in Set.Icc (1 : ℝ) 3,
    (((Finset.univ : Finset (Fin 2)).filter (fun _ => (2 : ℝ) ≤ x)).card : ℝ)) = 2 := by
  rw [Finset.integral_count_le_eq_sum_sub_max _ _ (by norm_num) (by norm_num)]
  norm_num

example : (∫ x in Set.Icc (2 : ℝ) 4,
    (((Finset.univ : Finset (Fin 4)).filter
      (fun i => (![(-1 : ℝ), 2, 3, 4] i) ≤ x)).card : ℝ)) = 5 := by
  rw [Finset.integral_count_le_eq_sum_sub_max _ _ (by norm_num)
    (by intro i _; fin_cases i <;> norm_num)]
  norm_num [Fin.sum_univ_succ]

example (a b : ℝ) (hab : a ≤ b) :
    (∫ x in Set.Icc a b,
      (((∅ : Finset ℕ).filter (fun i : ℕ => (i : ℝ) ≤ x)).card : ℝ)) = 0 := by
  rw [Finset.integral_count_le_eq_sum_sub_max _ _ hab (by simp)]
  simp

example (a : ℝ) :
    (∫ x in Set.Icc a a,
      (((Finset.univ : Finset (Fin 2)).filter (fun _ => a ≤ x)).card : ℝ)) = 0 := by
  rw [Finset.integral_count_le_eq_sum_sub_max _ _ le_rfl (by simp)]
  simp

end

end PrimeFactorUnimodality.Tests
