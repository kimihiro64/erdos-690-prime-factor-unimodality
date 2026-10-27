import Mathlib.NumberTheory.Bertrand
import PrimeFactorUnimodality.Helpers.Analytic.SharpThetaBounds
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive

set_option autoImplicit false

/-! # A first primorial crossing without a prime-counting hypothesis -/

namespace PrimeFactorUnimodality

open Real Finset

theorem theta_consecutive_step {p q : Nat} (h : ConsecutivePrimes p q) :
    Chebyshev.theta q = Chebyshev.theta p + log q := by
  have hpq := h.left_lt_right
  have hs : Nat.primesLE q = insert q (Nat.primesLE p) := by
    ext r
    simp only [Nat.mem_primesLE, Finset.mem_insert]
    constructor
    next =>
      intro hr
      by_cases hrq : r = q
      next => exact Or.inl hrq
      next =>
        apply Or.inr
        refine And.intro ?_ hr.2
        by_contra hnot
        exact h.no_prime_between r (by omega) (by omega) hr.2
    next =>
      intro hr
      cases hr with
      | inl hr => subst r; exact And.intro le_rfl h.right_prime
      | inr hr => exact And.intro (hr.1.trans h.left_lt_right.le) hr.2
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, hs,
    Finset.sum_insert (by simp only [Nat.mem_primesLE]; omega)]
  ring

theorem exists_first_primorial_crossing (ell : Real) (hell : 3670 <= ell) :
    Exists (fun p : Nat => Exists (fun q : Nat =>
      And (ConsecutivePrimes p q)
        (And (Chebyshev.theta p < ell)
          (And (ell <= Chebyshev.theta q) ((q : Real) < 5 * ell))))) := by
  classical
  obtain hprime := Nat.exists_infinite_primes (Nat.ceil (max 1000 (2.5 * ell)))
  cases hprime with
  | intro q hq =>
    have hlarge : max 1000 (2.5 * ell) <= (q : Real) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hq.1)
    have h1000 : (1000 : Real) <= q := (le_max_left _ _).trans hlarge
    have htheta := Chebyshev.theta_lower_040_from_1000 q h1000
    have hex : Exists (fun n : Nat => ell <= Chebyshev.theta (primeAt n)) := by
      apply Exists.intro (Nat.primeCounting' q)
      rw [primeAt_primeCounting' q hq.2]
      nlinarith [(le_max_right (1000 : Real) (2.5 * ell)).trans hlarge]
    let n := Nat.find hex
    have hcross : ell <= Chebyshev.theta (primeAt n) := Nat.find_spec hex
    have hlog4 : log (4 : Real) < 1.4 := by
      rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, log_pow]
      norm_num
      linarith [LogTables.log_2_lt]
    have hn : 0 < n := by
      by_contra hnot
      have hn0 : n = 0 := by omega
      have hzero : primeAt 0 = 2 := Nat.nth_prime_zero_eq_two
      rw [hn0, hzero] at hcross
      norm_num only [Nat.cast_ofNat] at hcross
      have hu := Chebyshev.theta_le_log4_mul_x (by norm_num : (0 : Real) <= 2)
      nlinarith
    have hstep : n - 1 + 1 = n := by omega
    have hpair : ConsecutivePrimes (primeAt (n - 1)) (primeAt n) := by
      simpa only [hstep] using consecutivePrimes_primeAt (n - 1)
    have hprev : Chebyshev.theta (primeAt (n - 1)) < ell :=
      lt_of_not_ge (Nat.find_min hex (show n - 1 < n by omega))
    have hprevBound : (primeAt (n - 1) : Real) < 2.5 * ell := by
      by_cases hp : (1000 : Real) <= primeAt (n - 1)
      next => nlinarith [Chebyshev.theta_lower_040_from_1000 (primeAt (n - 1)) hp]
      next => linarith
    obtain hbertrand := Nat.exists_prime_lt_and_le_two_mul (primeAt (n - 1))
      (prime_primeAt (n - 1)).ne_zero
    cases hbertrand with
    | intro s hs =>
      have hqle : primeAt n <= s := by
        by_contra hnot
        exact hpair.no_prime_between s hs.2.1 (by omega) hs.1
      have hbound : (primeAt n : Real) < 5 * ell := by
        have hle : (primeAt n : Real) <= 2 * primeAt (n - 1) := by
          exact_mod_cast hqle.trans hs.2.2
        linarith
      exact Exists.intro (primeAt (n - 1)) (Exists.intro (primeAt n)
        (And.intro hpair (And.intro hprev (And.intro hcross hbound))))

end PrimeFactorUnimodality
