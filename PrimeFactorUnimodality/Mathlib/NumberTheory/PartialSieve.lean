/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-! # Exact counts of a partially sieved interval

The positive integers coprime to a modulus admit a one-prime removal
recurrence. This supplies the arithmetic identity behind combinatorial
prime counting without enumerating all primes up to the target endpoint.
-/

namespace Nat

open Finset

/-- Positive integers at most `n` that are coprime to `m`. -/
def coprimeSieve (m n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun a => Coprime a m)

/-- The exact count retained after removing all prime divisors of the modulus. -/
def coprimeCount (m n : ℕ) : ℕ := (coprimeSieve m n).card

/-- Membership keeps both the positive lower endpoint and the coprimality condition. -/
@[simp] theorem mem_coprimeSieve {m n a : ℕ} :
    a ∈ coprimeSieve m n ↔ 1 ≤ a ∧ a ≤ n ∧ Coprime a m := by
  simp [coprimeSieve, and_assoc]

/-- With no excluded prime, the count is the full positive interval. -/
@[simp] theorem coprimeCount_one (n : ℕ) : coprimeCount 1 n = n := by
  simp [coprimeCount, coprimeSieve]

/-- An empty interval contributes nothing for every modulus, including zero. -/
@[simp] theorem coprimeCount_zero (m : ℕ) : coprimeCount m 0 = 0 := by
  simp [coprimeCount, coprimeSieve]

/-- Multiples of a new coprime prime correspond to the quotient interval. -/
theorem card_coprimeSieve_filter_dvd (m n p : ℕ) (hp : 0 < p) (hpm : Coprime p m) :
    ((coprimeSieve m n).filter (fun a => p ∣ a)).card = coprimeCount m (n / p) := by
  symm
  unfold coprimeCount
  apply card_bij (fun a _ => p * a)
  · intro a ha
    obtain ⟨ha1, han, ham⟩ := mem_coprimeSieve.mp ha
    simp only [mem_filter, mem_coprimeSieve]
    refine ⟨⟨by nlinarith, ?_, coprime_mul_iff_left.mpr ⟨hpm, ham⟩⟩, dvd_mul_right p a⟩
    exact (by simpa [mul_comm] using (Nat.le_div_iff_mul_le hp).mp han)
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hp hab
  · intro b hb
    obtain ⟨hb, a, rfl⟩ := mem_filter.mp hb
    obtain ⟨hba, hbn, hbm⟩ := mem_coprimeSieve.mp hb
    refine ⟨a, mem_coprimeSieve.mpr ⟨?_, ?_, (coprime_mul_iff_left.mp hbm).2⟩, rfl⟩
    · by_contra h
      have : a = 0 := by omega
      simp_all
    · exact (Nat.le_div_iff_mul_le hp).mpr (by simpa [mul_comm] using hbn)

/-- Removing a new prime partitions the old count into survivors and divisible integers. -/
theorem coprimeCount_mul_prime_add (m n : ℕ) {p : ℕ} (hp : p.Prime)
    (hpm : Coprime p m) :
    coprimeCount (m * p) n + coprimeCount m (n / p) = coprimeCount m n := by
  have hcp (a : ℕ) : Coprime a (m * p) ↔ Coprime a m ∧ ¬p ∣ a := by
    rw [coprime_mul_iff_right, show Coprime a p ↔ Coprime p a from coprime_comm,
      hp.coprime_iff_not_dvd]
  have he : coprimeSieve (m * p) n =
      (coprimeSieve m n).filter (fun a => ¬p ∣ a) := by
    ext a
    simp only [mem_filter, mem_coprimeSieve, hcp]
    tauto
  rw [← card_coprimeSieve_filter_dvd m n p hp.pos hpm]
  unfold coprimeCount
  rw [he, add_comm]
  exact card_filter_add_card_filter_not (fun a => p ∣ a)

/-- The subtraction form used by recursive partial-sieve implementations is exact. -/
theorem coprimeCount_mul_prime (m n : ℕ) {p : ℕ} (hp : p.Prime)
    (hpm : Coprime p m) :
    coprimeCount (m * p) n = coprimeCount m n - coprimeCount m (n / p) := by
  have h := coprimeCount_mul_prime_add m n hp hpm
  omega

/-- Executable partial-sieve recurrence, starting with the full positive interval. -/
def partialSieveCount : List ℕ → ℕ → ℕ
  | [], n => n
  | p :: ps, n => partialSieveCount ps n - partialSieveCount ps (n / p)

/-- Distinct prime steps give the exact survivor count, not merely a heuristic sieve estimate. -/
theorem partialSieveCount_eq (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime)
    (hpair : ps.Pairwise Coprime) (n : ℕ) :
    partialSieveCount ps n = coprimeCount ps.prod n := by
  induction ps generalizing n with
  | nil => simp [partialSieveCount]
  | cons p ps ih =>
    obtain ⟨hcop, hpair⟩ := List.pairwise_cons.mp hpair
    have hp := hprime p (by simp)
    have hprimes : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (by simp [hq])
    have hpm : Coprime p ps.prod := coprime_list_prod_right_iff.mpr hcop
    rw [partialSieveCount, ih hprimes hpair, ih hprimes hpair, List.prod_cons, mul_comm p]
    exact (coprimeCount_mul_prime _ _ hp hpm).symm

/-- Indexed form for externally generated, shared dependency rows. -/
def sievePhi (p : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | a + 1, n => sievePhi p a n - sievePhi p a (n / p a)

/-- The indexed recurrence has the same exact partial-sieve semantics. -/
theorem sievePhi_eq (p : ℕ → ℕ) (a n : ℕ)
    (hprime : ∀ i < a, (p i).Prime)
    (hcop : ∀ i < a, ∀ j < i, Coprime (p i) (p j)) :
    sievePhi p a n = coprimeCount (∏ i ∈ range a, p i) n := by
  induction a generalizing n with
  | zero => simp [sievePhi]
  | succ a ih =>
    have hprimes : ∀ i < a, (p i).Prime := fun i hi => hprime i (by omega)
    have hpair : ∀ i < a, ∀ j < i, Coprime (p i) (p j) :=
      fun i hi j hj => hcop i (by omega) j hj
    have hpm : Coprime (p a) (∏ i ∈ range a, p i) :=
      coprime_prod_right_iff.mpr (fun i hi => hcop a (by omega) i (mem_range.mp hi))
    rw [sievePhi, ih n hprimes hpair, ih (n / p a) hprimes hpair, prod_range_succ]
    exact (coprimeCount_mul_prime _ _ (hprime a (by omega)) hpm).symm

/-- Only the finite prime prefix used by a recurrence needs to agree. -/
theorem sievePhi_congr {p q : ℕ → ℕ} {a : ℕ}
    (hpq : ∀ i < a, p i = q i) (n : ℕ) : sievePhi p a n = sievePhi q a n := by
  induction a generalizing n with
  | zero => rfl
  | succ a ih =>
    have hsmall : ∀ i < a, p i = q i := fun i hi => hpq i (by omega)
    simp only [sievePhi, ih hsmall, hpq a (by omega)]

/-- For distinct primes the recursive subtraction loses no information. -/
theorem sievePhi_succ_add (p : ℕ → ℕ) (a n : ℕ)
    (hprime : ∀ i < a + 1, (p i).Prime)
    (hcop : ∀ i < a + 1, ∀ j < i, Coprime (p i) (p j)) :
    sievePhi p (a + 1) n + sievePhi p a (n / p a) = sievePhi p a n := by
  have hprimes : ∀ i < a, (p i).Prime := fun i hi => hprime i (by omega)
  have hpair : ∀ i < a, ∀ j < i, Coprime (p i) (p j) :=
    fun i hi j hj => hcop i (by omega) j hj
  have hpm : Coprime (p a) (∏ i ∈ range a, p i) :=
    coprime_prod_right_iff.mpr (fun i hi => hcop a (by omega) i (mem_range.mp hi))
  rw [sievePhi_eq p (a + 1) n hprime hcop,
    sievePhi_eq p a _ hprimes hpair, sievePhi_eq p a _ hprimes hpair, prod_range_succ]
  exact coprimeCount_mul_prime_add _ _ (hprime a (by omega)) hpm

end Nat
