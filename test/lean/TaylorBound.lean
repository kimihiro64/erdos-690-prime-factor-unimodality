import PrimeFactorUnimodality.Mathlib.Analysis.Calculus.TaylorBound

/-! Sharp factorial remainders cover both segment orientations and coincident endpoints. -/

open Finset Set
open scoped ContDiff Nat

example {f : ℝ → ℂ} {a w C : ℝ} (hf : ContDiff ℝ 4 f)
    (hC : ∀ y ∈ uIcc a (a + w), ‖iteratedDeriv 4 f y‖ ≤ C) :
    ‖f (a + w) - ∑ k ∈ range 4, (w ^ k / (k ! : ℝ)) • iteratedDeriv k f a‖ ≤
      C * |w| ^ 4 / 24 := by
  simpa only [add_sub_cancel_left, show (4 ! : ℝ) = 24 by norm_num] using
    norm_sub_sum_taylor_le (n := 3) hf hC

example {f : ℝ → ℂ} {a C : ℝ} (hf : ContDiff ℝ 2 f)
    (hC : ∀ y ∈ uIcc a (a - 2), ‖iteratedDeriv 2 f y‖ ≤ C) :
    ‖f (a - 2) - ∑ k ∈ range 2, ((-2 : ℝ) ^ k / (k ! : ℝ)) • iteratedDeriv k f a‖ ≤
      C * 4 / 2 := by
  convert norm_sub_sum_taylor_le (n := 1) hf hC using 1 <;> norm_num

example {f : ℝ → ℂ} {n : ℕ} {a C : ℝ} (hf : ContDiff ℝ (n + 1 : ℕ) f)
    (hC : ‖iteratedDeriv (n + 1) f a‖ ≤ C) :
    ‖f a - ∑ k ∈ range (n + 1), ((a - a) ^ k / (k ! : ℝ)) • iteratedDeriv k f a‖ ≤ 0 := by
  simpa only [sub_self, abs_zero, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_div] using
    norm_sub_sum_taylor_le (a := a) (x := a) hf (by simpa using hC)
