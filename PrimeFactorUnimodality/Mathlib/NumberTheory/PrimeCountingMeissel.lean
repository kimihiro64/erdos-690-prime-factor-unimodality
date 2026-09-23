/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Intervals
import PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSievePrimeLeaves

/-! # Exact combinatorial prime counting by a partial sieve

Telescoping one-prime removal from a cube-root cutoff to a square-root
cutoff leaves only prime-count lookups at smaller quotient endpoints.
The cutoff inequalities are explicit, including their strict boundaries.
-/

namespace Nat

open Finset

/-- The canonical prime prefix contains every smaller prime exactly once. -/
theorem primesBelow_nth_prime (a : ℕ) :
    primesBelow (nth Prime a) = (range a).image (nth Prime) := by
  ext p
  simp only [mem_primesBelow, mem_image, mem_range]
  constructor
  · rintro ⟨hpa, hp⟩
    refine ⟨count Prime p, ?_, nth_count hp⟩
    apply (nth_lt_nth infinite_setOfPred_prime).mp
    simpa only [nth_count hp] using hpa
  · rintro ⟨i, hi, rfl⟩
    exact ⟨nth_strictMono infinite_setOfPred_prime hi, prime_nth_prime i⟩

/-- Product form of completeness of the canonical prime prefix. -/
theorem prod_nth_prime_eq_primorial (a : ℕ) :
    (∏ i ∈ range a, nth Prime i) = primorial (nth Prime a - 1) := by
  rw [primorial_eq_prod_primesLE, ← primesBelow_eq_primesLE_sub_one,
    primesBelow_nth_prime, prod_image (nth_injective infinite_setOfPred_prime).injOn]

/-- Distinct entries of the prime enumeration are coprime. -/
theorem coprime_nth_prime_of_lt {i j : ℕ} (hji : j < i) :
    Coprime (nth Prime i) (nth Prime j) :=
  (coprime_primes (prime_nth_prime i) (prime_nth_prime j)).mpr
    (ne_of_gt (nth_strictMono infinite_setOfPred_prime hji))

/-- The square-root stopping rule for an indexed canonical partial sieve. -/
theorem sievePhi_nth_prime_leaf {a n : ℕ} (hn : 1 ≤ n)
    (ha : nth Prime a - 1 ≤ n) (hsq : n < nth Prime a ^ 2) :
    sievePhi (nth Prime) a n = primeCounting n - a + 1 := by
  rw [sievePhi_eq _ _ _ (fun i _ => prime_nth_prime i)
    (fun _ _ _ hij => coprime_nth_prime_of_lt hij), prod_nth_prime_eq_primorial]
  have hp := (prime_nth_prime a).one_le
  rw [coprimeCount_primorial_eq hn ha (by simpa only [Nat.sub_add_cancel hp] using hsq),
    primeCounting_sub_one, primeCounting'_nth_eq]

/-- Telescoping the exact removal recurrence uses no truncated subtraction. -/
theorem sievePhi_nth_prime_telescope {a b : ℕ} (hab : a ≤ b) (n : ℕ) :
    sievePhi (nth Prime) a n = sievePhi (nth Prime) b n +
      ∑ i ∈ Ico a b, sievePhi (nth Prime) i (n / nth Prime i) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab]
    have h := sievePhi_succ_add (nth Prime) b n (fun i _ => prime_nth_prime i)
      (fun _ _ _ hij => coprime_nth_prime_of_lt hij)
    omega

/-- Meissel's identity with local quotient stopping conditions and natural arithmetic. -/
theorem primeCounting_meissel_of_quotient_bounds {n a b : ℕ} (hab : a ≤ b)
    (hn : 1 ≤ n) (hb : nth Prime b - 1 ≤ n) (hsq : n < nth Prime b ^ 2)
    (hleaf : ∀ i ∈ Ico a b, nth Prime i - 1 ≤ n / nth Prime i ∧
      1 ≤ n / nth Prime i ∧ n / nth Prime i < nth Prime i ^ 2) :
    primeCounting n = sievePhi (nth Prime) a n + b - 1 -
      ∑ i ∈ Ico a b, (primeCounting (n / nth Prime i) - i + 1) := by
  have ht := sievePhi_nth_prime_telescope hab n
  rw [sievePhi_nth_prime_leaf hn hb hsq] at ht
  have he : (∑ i ∈ Ico a b, sievePhi (nth Prime) i (n / nth Prime i)) =
      ∑ i ∈ Ico a b, (primeCounting (n / nth Prime i) - i + 1) := by
    apply sum_congr rfl
    intro i hi
    exact sievePhi_nth_prime_leaf (hleaf i hi).2.1 (hleaf i hi).1 (hleaf i hi).2.2
  rw [he] at ht
  have hmono := monotone_primeCounting hb
  rw [primeCounting_sub_one, primeCounting'_nth_eq] at hmono
  omega

/-- Cube and square comparisons suffice for every quotient stopping condition. -/
theorem primeCounting_meissel {n a b : ℕ} (hab : a ≤ b) (hn : 1 ≤ n)
    (hb : nth Prime b - 1 ≤ n) (hsq : n < nth Prime b ^ 2)
    (hcube : n < nth Prime a ^ 3)
    (hsquares : ∀ i ∈ Ico a b, nth Prime i ^ 2 ≤ n) :
    primeCounting n = sievePhi (nth Prime) a n + b - 1 -
      ∑ i ∈ Ico a b, (primeCounting (n / nth Prime i) - i + 1) := by
  apply primeCounting_meissel_of_quotient_bounds hab hn hb hsq
  intro i hi
  have hai := (mem_Ico.mp hi).1
  have hp := (prime_nth_prime i).pos
  have hpi : nth Prime i ≤ n / nth Prime i :=
    (Nat.le_div_iff_mul_le hp).mpr (by simpa only [pow_two] using hsquares i hi)
  refine ⟨by omega, by omega, ?_⟩
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  have hmono := nth_monotone infinite_setOfPred_prime hai
  have hpow : nth Prime a ^ 3 ≤ nth Prime i ^ 3 := Nat.pow_le_pow_left hmono 3
  have hlt := hcube.trans_le hpow
  simpa only [pow_succ] using hlt

end Nat
