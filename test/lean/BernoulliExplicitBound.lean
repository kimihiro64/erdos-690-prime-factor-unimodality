import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ExplicitBound

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex
open Polynomial MeasureTheory Set

example (k : ℕ) : bernoulliCoeffBound k = bernoulliCoeffBudget k :=
  bernoulliCoeffBound_eq_budget k

example : bernoulliCoeffBudget 0 = 1 := by decide +kernel
example : bernoulliCoeffBudget 1 = 3 / 2 := by decide +kernel
example : bernoulliCoeffBudget 2 = 13 / 12 := by decide +kernel

example (k : ℕ) : 0 ≤ bernoulliCoeffBound k := by
  exact Polynomial.bernoulliCoeffBound_nonneg k

example (k : ℕ) (x : ℝ) :
    |bernoulliPeriodic k x| ≤ (bernoulliCoeffBound k : ℝ) := by
  exact Polynomial.abs_bernoulliPeriodic_le_coeffBound k x

example (k : ℕ) {a : ℝ} {z : ℂ}
    (ha : 0 < a) (hz : z.re < -1) :
    ‖∫ x in Set.Ioi a, (bernoulliPeriodic k x : ℂ) * (x : ℂ) ^ z‖ ≤
      (bernoulliCoeffBound k : ℝ) * (-a ^ (z.re + 1) / (z.re + 1)) := by
  exact Polynomial.norm_bernoulliPeriodic_cpow_tail_le k ha hz

example (x : ℝ) : |bernoulliPeriodic 0 x| ≤ (bernoulliCoeffBound 0 : ℝ) :=
  abs_bernoulliPeriodic_le_coeffBound 0 x

example (k : ℕ) :
    ‖∫ x in Set.Ioi (1 : ℝ), (bernoulliPeriodic k x : ℂ) * (x : ℂ) ^ (-2 : ℂ)‖ ≤
      (bernoulliCoeffBound k : ℝ) := by
  have h := norm_bernoulliPeriodic_cpow_tail_le k
    (a := 1) (z := -2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end

end PrimeFactorUnimodality.Tests
