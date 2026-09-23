import PrimeFactorUnimodality.Mathlib.NumberTheory.Chebyshev.Intervals

/-! # Complete prime-block transitions and coverage regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Chebyshev

example {a b : ℕ} (hab : a ≤ b) :
    theta b - theta a = ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p := by
  exact Chebyshev.theta_sub_eq_sum_primes_sdiff hab

example {a b : ℕ} (hab : a ≤ b) :
    Nat.primeCounting b - Nat.primeCounting a =
      (Nat.primesLE b \ Nat.primesLE a).card := by
  exact Chebyshev.primeCounting_sub_eq_card_primes_sdiff hab

example {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ((Nat.primeCounting b - Nat.primeCounting a : ℕ) : ℝ) * Real.log a ≤
      theta b - theta a := by
  exact Chebyshev.primeCounting_sub_mul_log_le_theta_sub ha hab

example {a b : ℕ} (hab : a ≤ b) :
    theta b - theta a ≤
      ((Nat.primeCounting b - Nat.primeCounting a : ℕ) : ℝ) * Real.log b := by
  exact Chebyshev.theta_sub_le_primeCounting_sub_mul_log hab

example : theta (0 : ℕ) - theta (0 : ℕ) ≤
    ((Nat.primeCounting 0 - Nat.primeCounting 0 : ℕ) : ℝ) * Real.log (0 : ℕ) :=
  theta_sub_le_primeCounting_sub_mul_log le_rfl

example (n : ℕ) (hn : 0 < n) :
    ((Nat.primeCounting n - Nat.primeCounting n : ℕ) : ℝ) * Real.log n ≤
      theta n - theta n := primeCounting_sub_mul_log_le_theta_sub hn le_rfl

example : theta (3 : ℕ) - theta (1 : ℕ) =
    ∑ p ∈ Nat.primesLE 3 \ Nat.primesLE 1, Real.log p :=
  theta_sub_eq_sum_primes_sdiff (by norm_num)

end

end PrimeFactorUnimodality.Tests
