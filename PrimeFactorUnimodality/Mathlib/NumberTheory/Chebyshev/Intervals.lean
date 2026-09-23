/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.Chebyshev

/-! # Chebyshev increments from interval prime counts

The exact prime-set difference identifies both the theta increment and its
number of terms. Logarithmic monotonicity bounds the complete increment by
that count times either endpoint logarithm, without evaluating each prime's
logarithm separately. Natural subtraction is used only on ordered endpoints.
-/

namespace Chebyshev

open Finset

/-- The theta increment is the logarithmic sum over the exact prime-set difference. -/
theorem theta_sub_eq_sum_primes_sdiff {a b : ℕ} (hab : a ≤ b) :
    theta b - theta a = ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p := by
  rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log]
  exact (eq_sub_iff_add_eq.mpr (sum_sdiff (Nat.primesLE_mono hab))).symm

/-- The same prime-set difference counts precisely the primes added in the interval. -/
theorem primeCounting_sub_eq_card_primes_sdiff {a b : ℕ} (hab : a ≤ b) :
    Nat.primeCounting b - Nat.primeCounting a =
      (Nat.primesLE b \ Nat.primesLE a).card := by
  rw [card_sdiff_of_subset (Nat.primesLE_mono hab), Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]

/-- The left endpoint logarithm bounds every newly included prime weight from below. -/
theorem primeCounting_sub_mul_log_le_theta_sub {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ((Nat.primeCounting b - Nat.primeCounting a : ℕ) : ℝ) * Real.log a ≤
      theta b - theta a := by
  rw [theta_sub_eq_sum_primes_sdiff hab, primeCounting_sub_eq_card_primes_sdiff hab]
  rw [← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpb, hpa⟩ := mem_sdiff.mp hp
  have hprime := (Nat.mem_primesLE.mp hpb).2
  have hap : a < p := by
    by_contra! h
    exact hpa (Nat.mem_primesLE.mpr ⟨h, hprime⟩)
  exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hap.le)

/-- The right endpoint logarithm bounds every newly included prime weight from above. -/
theorem theta_sub_le_primeCounting_sub_mul_log {a b : ℕ} (hab : a ≤ b) :
    theta b - theta a ≤
      ((Nat.primeCounting b - Nat.primeCounting a : ℕ) : ℝ) * Real.log b := by
  rw [theta_sub_eq_sum_primes_sdiff hab, primeCounting_sub_eq_card_primes_sdiff hab]
  rw [← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro p hp
  have hpb := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
  exact Real.log_le_log (by exact_mod_cast hpb.2.pos) (by exact_mod_cast hpb.1)

end Chebyshev
