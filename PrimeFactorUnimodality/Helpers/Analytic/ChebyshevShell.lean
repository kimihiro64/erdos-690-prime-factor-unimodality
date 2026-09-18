import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

/-! # Elementary prime counts from Chebyshev theta

This file isolates a finite inequality used to replace unnecessary explicit
prime-counting estimates.  It depends only on Mathlib's proved definition of
`Chebyshev.theta`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Nat Real

/-- The theta mass in `(x,y]` is at most the number of primes there times
`log y`. -/
theorem theta_sub_le_primeCounting_sub_mul_log
    {x y : Nat} (hxy : x ≤ y) :
    Chebyshev.theta y - Chebyshev.theta x ≤
      (Nat.primeCounting y - Nat.primeCounting x : Nat) * Real.log y := by
  have subset : Nat.primesLE x ⊆ Nat.primesLE y := Nat.primesLE_mono hxy
  have thetaDifference :
      Chebyshev.theta y - Chebyshev.theta x =
        ∑ p ∈ Nat.primesLE y \ Nat.primesLE x, Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE_log,
      Chebyshev.theta_eq_sum_primesLE_log]
    rw [← Finset.sum_sdiff subset]
    ring
  rw [thetaDifference]
  calc
    ∑ p ∈ Nat.primesLE y \ Nat.primesLE x, Real.log p ≤
        ∑ _p ∈ Nat.primesLE y \ Nat.primesLE x, Real.log y := by
      apply Finset.sum_le_sum
      intro p hp
      have primeAndLe := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
      have py : p ≤ y := primeAndLe.1
      exact Real.log_le_log (by exact_mod_cast primeAndLe.2.pos)
        (by exact_mod_cast py)
    _ = ((Nat.primesLE y \ Nat.primesLE x).card : Nat) * Real.log y := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.primeCounting y - Nat.primeCounting x : Nat) *
        Real.log y := by
      have cardEq : (Nat.primesLE y \ Nat.primesLE x).card =
          (Nat.primesLE y).card - (Nat.primesLE x).card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr subset]
      rw [cardEq, Nat.primesLE_card_eq_primeCounting,
        Nat.primesLE_card_eq_primeCounting]

/-- A strict lower estimate for a theta shell gives a lower estimate for its
prime count after multiplication by `log y`. -/
theorem count_mul_log_gt_of_theta_shell_gt
    {x y : Nat} (hxy : x ≤ y) {mass : Real}
    (shell : mass < Chebyshev.theta y - Chebyshev.theta x) :
    mass < (Nat.primeCounting y - Nat.primeCounting x : Nat) * Real.log y :=
  shell.trans_le (theta_sub_le_primeCounting_sub_mul_log hxy)

end

end PrimeFactorUnimodality
