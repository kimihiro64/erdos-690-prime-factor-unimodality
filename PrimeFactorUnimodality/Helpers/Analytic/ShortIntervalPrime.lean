import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
