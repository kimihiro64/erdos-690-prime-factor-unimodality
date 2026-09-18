import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive

set_option autoImplicit false

/-! # Interface for an explicit prime in a short interval -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's explicit short-interval theorem, stated in the precise form used
by the uniform CRT construction. -/
def HasDusartShortIntervalPrime : Prop :=
  ∀ x : Real, 3275 ≤ x →
    ∃ q : Nat, q.Prime ∧ x < q ∧
      (q : Real) ≤ x * (1 + 1 / (2 * (Real.log x) ^ 2))

/-! Dusart's published prime-in-interval result is often stated with the
stronger width `x / log(x)^3`.  Keep that statement separate and provide the
exact conversion needed by the CRT construction. -/
def HasLogCubedShortIntervalPrime : Prop :=
  ∀ x : Real, 3275 ≤ x →
    ∃ q : Nat, q.Prime ∧ x < q ∧
      (q : Real) ≤ x + x / (Real.log x) ^ 3

/-! The following lemma is the local version of the fully proved
`HasPrimeInInterval.iff_theta_ge` argument in PrimeNumberTheoremAnd.  Keeping
the conversion here makes the eventual explicit provider depend only on
Chebyshev's finite prime sum, rather than on that repository's larger
secondary-definition import closure. -/
theorem exists_prime_of_theta_increment {x h : Real}
    (x_nonneg : 0 ≤ x) (h_pos : 0 < h)
    (theta_increment : Chebyshev.theta (x + h) > Chebyshev.theta x) :
    ∃ q : Nat, q.Prime ∧ x < q ∧ (q : Real) ≤ x + h := by
  have x_le_xh : x ≤ x + h := by linarith
  have floor_mono : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_mono x_le_xh
  by_contra no_prime
  push_neg at no_prime
  have prime_set_eq : Nat.primesLE ⌊x⌋₊ = Nat.primesLE ⌊x + h⌋₊ := by
    apply Finset.Subset.antisymm (Nat.primesLE_mono floor_mono)
    intro q hq
    rw [Nat.mem_primesLE] at hq ⊢
    have q_le_upper : q ≤ ⌊x + h⌋₊ := hq.1
    have q_le_real : (q : Real) ≤ x + h := by
      exact (Nat.cast_le.mpr q_le_upper).trans (Nat.floor_le (by linarith))
    have not_above_x : ¬ x < (q : Real) := by
      intro x_lt_q
      exact (not_lt_of_ge q_le_real) (no_prime q hq.2 x_lt_q)
    have q_le_x : (q : Real) ≤ x := le_of_not_gt not_above_x
    have q_le_floor_x : q ≤ ⌊x⌋₊ := by
      exact Nat.le_floor q_le_x
    exact ⟨q_le_floor_x, hq.2⟩
  rw [Chebyshev.theta_eq_sum_primesLE,
    Chebyshev.theta_eq_sum_primesLE, prime_set_eq] at theta_increment
  exact (lt_irrefl _ theta_increment)

theorem hasDusartShortIntervalPrime_of_logCubed
    (shortInterval : HasLogCubedShortIntervalPrime) :
    HasDusartShortIntervalPrime := by
  intro x hx
  obtain ⟨q, qPrime, hxq, hq⟩ := shortInterval x hx
  have x_pos : (0 : Real) < x := by linarith
  have log_x_gt_two : (2 : Real) < Real.log x := by
    have exp_two_lt : Real.exp 2 < (9 : Real) := by
      rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
      have exp_one_lt_three : Real.exp 1 < 3 :=
        Real.exp_one_lt_d9.trans (by norm_num)
      nlinarith [mul_self_lt_mul_self (Real.exp_pos 1).le exp_one_lt_three]
    apply (Real.lt_log_iff_exp_lt x_pos).2
    exact exp_two_lt.trans (by linarith)
  have log_x_pos : 0 < Real.log x := by linarith
  have width_le : x / (Real.log x) ^ 3 ≤ x / (2 * (Real.log x) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : 2 * (Real.log x) ^ 2 ≤ (Real.log x) ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_right log_x_gt_two.le
        (sq_nonneg (Real.log x))
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq x_pos.le]
  refine ⟨q, qPrime, hxq, ?_⟩
  calc
    (q : Real) ≤ x + x / (Real.log x) ^ 3 := hq
    _ ≤ x + x / (2 * (Real.log x) ^ 2) := by linarith [width_le]
    _ = x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by ring

/-- Applying the short-interval theorem at the left member of a consecutive
prime pair bounds the right member. -/
theorem ConsecutivePrimes.right_le_shortInterval_upper
    (shortInterval : HasDusartShortIntervalPrime) {qPrev q : Nat}
    (consecutive : ConsecutivePrimes qPrev q) (qPrev_large : 3275 ≤ qPrev) :
    (q : Real) ≤ qPrev * (1 + 1 / (2 * (Real.log qPrev) ^ 2)) := by
  obtain ⟨ell, ellPrime, prev_lt_ell, ell_upper⟩ :=
    shortInterval qPrev (by exact_mod_cast qPrev_large)
  have q_le_ell : q ≤ ell := by
    by_contra h
    have ell_lt_q : ell < q := Nat.lt_of_not_ge h
    exact consecutive.no_prime_between ell (by exact_mod_cast prev_lt_ell)
      ell_lt_q ellPrime
  exact (by exact_mod_cast q_le_ell : (q : Real) ≤ ell).trans ell_upper

/-- Two applications of the short-interval theorem locate a prime `q` and
its predecessor `qPrev`, with both lower bounds needed by the symmetric CRT
gap.  The last hypothesis is a purely numerical comparison at `x / 2`. -/
theorem exists_consecutive_primes_near
    (shortInterval : HasDusartShortIntervalPrime) {x : Real}
    (half_large : 3275 ≤ x / 2)
    (half_upper_lt :
      x / 2 * (1 + 1 / (2 * (Real.log (x / 2)) ^ 2)) < x) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      x / 2 < qPrev ∧ x < q ∧
      (q : Real) ≤ x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  have x_large : 3275 ≤ x := by linarith
  obtain ⟨q, qPrime, x_lt_q, q_upper⟩ := shortInterval x x_large
  obtain ⟨s, sPrime, half_lt_s, s_upper⟩ := shortInterval (x / 2) half_large
  have s_lt_q : s < q := by
    have s_lt_x : (s : Real) < x := s_upper.trans_lt half_upper_lt
    exact_mod_cast s_lt_x.trans x_lt_q
  have q_gt_two : 2 < q := by
    have : (2 : Real) < q := by
      exact (by norm_num : (2 : Real) < 3275).trans_le x_large |>.trans x_lt_q
    exact_mod_cast this
  let qPrev := primeAt (Nat.primeCounting' q - 1)
  have consecutive : ConsecutivePrimes qPrev q :=
    consecutivePrimes_predecessor qPrime q_gt_two
  have s_le_prev : s ≤ qPrev := by
    dsimp only [qPrev]
    exact prime_le_primeAt_primeCounting'_sub_one sPrime s_lt_q
  refine ⟨qPrev, q, consecutive, ?_, x_lt_q, q_upper⟩
  exact half_lt_s.trans_le (by exact_mod_cast s_le_prev)

/-- The same construction with the sharper lower information on the
predecessor retained in division-free form. -/
theorem exists_consecutive_primes_near_sharp
    (shortInterval : HasDusartShortIntervalPrime) {x : Real}
    (half_large : 3275 ≤ x / 2)
    (half_upper_lt :
      x / 2 * (1 + 1 / (2 * (Real.log (x / 2)) ^ 2)) < x) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      x / 2 < qPrev ∧ x < q ∧
      (q : Real) ≤ x * (1 + 1 / (2 * (Real.log x) ^ 2)) ∧
      x < qPrev * (1 + 1 / (2 * (Real.log qPrev) ^ 2)) := by
  obtain ⟨qPrev, q, consecutive, half_lt_prev, x_lt_q, q_upper⟩ :=
    exists_consecutive_primes_near shortInterval half_large half_upper_lt
  have prev_large : 3275 ≤ qPrev := by
    have : (3275 : Real) ≤ qPrev := half_large.trans half_lt_prev.le
    exact_mod_cast this
  have q_le := consecutive.right_le_shortInterval_upper shortInterval prev_large
  exact ⟨qPrev, q, consecutive, half_lt_prev, x_lt_q, q_upper,
    x_lt_q.trans_le q_le⟩

/-- A single fixed prime below `x` is enough to put the predecessor in the
domain of the short-interval theorem.  This version supports the optimized
cutoff, where `x` exceeds `3275` but `x / 2` need not. -/
theorem exists_consecutive_primes_above_fixed
    (shortInterval : HasDusartShortIntervalPrime) {x : Real} {s : Nat}
    (x_large : 3275 ≤ x) (s_large : 3275 ≤ s) (s_prime : s.Prime)
    (s_lt_x : (s : Real) < x) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧ s ≤ qPrev ∧ x < q ∧
      (q : Real) ≤ x * (1 + 1 / (2 * (Real.log x) ^ 2)) ∧
      x < qPrev * (1 + 1 / (2 * (Real.log qPrev) ^ 2)) := by
  obtain ⟨q, qPrime, x_lt_q, q_upper⟩ := shortInterval x x_large
  have q_gt_two : 2 < q := by
    have : (2 : Real) < q := (by norm_num : (2 : Real) < 3275).trans_le
      x_large |>.trans x_lt_q
    exact_mod_cast this
  let qPrev := primeAt (Nat.primeCounting' q - 1)
  have consecutive : ConsecutivePrimes qPrev q :=
    consecutivePrimes_predecessor qPrime q_gt_two
  have s_lt_q : s < q := by exact_mod_cast s_lt_x.trans x_lt_q
  have s_le_prev : s ≤ qPrev := by
    dsimp only [qPrev]
    exact prime_le_primeAt_primeCounting'_sub_one s_prime s_lt_q
  have prev_large : 3275 ≤ qPrev := s_large.trans s_le_prev
  have q_le := consecutive.right_le_shortInterval_upper shortInterval prev_large
  exact ⟨qPrev, q, consecutive, s_le_prev, x_lt_q, q_upper,
    x_lt_q.trans_le q_le⟩

end

end PrimeFactorUnimodality
