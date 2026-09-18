import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryChebyshevConsequences

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! A theta difference controls the number of primes in the corresponding
interval.  This is the shell-count interface needed by the elementary tail;
it avoids introducing a separate explicit `pi` estimate. -/
theorem theta_sub_le_primeCounting_sub_mul_log
    {x y : Nat} (hxy : x ≤ y) (hy : 1 ≤ y) :
    Chebyshev.theta y - Chebyshev.theta x ≤
      ((Nat.primeCounting y - Nat.primeCounting x : Nat) : Real) *
        Real.log y := by
  have hsub : Nat.primesLE x ⊆ Nat.primesLE y := Nat.primesLE_mono hxy
  have hsum :
      (∑ p ∈ Nat.primesLE y, Real.log p) -
          ∑ p ∈ Nat.primesLE x, Real.log p =
        ∑ p ∈ Nat.primesLE y \ Nat.primesLE x, Real.log p := by
    rw [← Finset.sum_sdiff hsub]
    ring
  rw [Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log, hsum]
  have each_bound : ∀ p ∈ Nat.primesLE y \ Nat.primesLE x,
      Real.log p ≤ Real.log y := by
    intro p hp
    apply Real.strictMonoOn_log.monotoneOn
    · change (0 : Real) < p
      exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.pos
    · change (0 : Real) < y
      exact_mod_cast hy
    · exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).1
  have sum_bound := Finset.sum_le_sum each_bound
  rw [show (∑ p ∈ Nat.primesLE y \ Nat.primesLE x, Real.log y) =
      (((Nat.primesLE y \ Nat.primesLE x).card : Nat) : Real) * Real.log y by
    simp] at sum_bound
  have card_eq : (Nat.primesLE y \ Nat.primesLE x).card =
      Nat.primeCounting y - Nat.primeCounting x := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  rw [card_eq] at sum_bound
  exact sum_bound

theorem nat_le_primeCounting_sub_of_theta_bounds
    {x y target : Nat} {lower upper : Real}
    (hxy : x ≤ y) (hy : 1 ≤ y)
    (theta_lower : (lower : Real) * y ≤ Chebyshev.theta y)
    (theta_upper : Chebyshev.theta x ≤ (upper : Real) * x)
    (log_y_pos : 0 < Real.log y)
    (numeric : (target : Real) * Real.log y < lower * y - upper * x) :
    target ≤ Nat.primeCounting y - Nat.primeCounting x := by
  have theta_gap : (target : Real) * Real.log y <
      Chebyshev.theta y - Chebyshev.theta x := by
    nlinarith
  have count_gap := theta_sub_le_primeCounting_sub_mul_log hxy hy
  have target_lt : (target : Real) <
      (Nat.primeCounting y - Nat.primeCounting x : Nat) := by
    nlinarith
  exact_mod_cast (show target < Nat.primeCounting y - Nat.primeCounting x by
    exact_mod_cast target_lt)
      |>.le

theorem elementary_49_shell_count
    {q target : Nat} (hlarge : 250000 ≤ 4 * primorial q)
    (numeric : (target : Real) *
        Real.log ((9 * primorial q : Nat) : Real) <
      (86 : Real) / 100 * (9 * primorial q) -
        (111 : Real) / 100 * (4 * primorial q)) :
    target ≤ Nat.primeCounting (9 * primorial q) -
      Nat.primeCounting (4 * primorial q) := by
  apply nat_le_primeCounting_sub_of_theta_bounds (x := 4 * primorial q)
    (y := 9 * primorial q) (lower := (86 : Real) / 100)
    (upper := (111 : Real) / 100)
  · omega
  · have : 1 ≤ 9 * primorial q := by
      have := primorial_pos q
      omega
    exact this
  · apply elementary_theta_lower_from_250000
    exact_mod_cast (show 250000 ≤ 9 * primorial q by omega)
  · apply elementary_theta_upper_from_250000
    exact_mod_cast hlarge
  · have : 1 < (9 * primorial q : Nat) := by
      have := primorial_pos q
      omega
    exact Real.log_pos (by exact_mod_cast this)
  · norm_num only [Nat.cast_mul, Nat.cast_ofNat] at numeric ⊢
    exact numeric

end

end PrimeFactorUnimodality
