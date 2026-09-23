/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.Primorial
import PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSieve

/-! # Prime-count leaves of a partial sieve

Once every possible least prime factor of a composite is excluded, the
positive survivors are exactly one and the remaining primes. The strict
square condition is necessary: the square of the next prime survives.
-/

namespace Nat

open Finset

/-- Coprimality to a primorial excludes exactly the primes below its endpoint. -/
theorem coprime_primorial_iff (n y : ℕ) :
    Coprime n (primorial y) ↔ ∀ p, p.Prime → p ≤ y → ¬p ∣ n := by
  constructor
  · intro h p hp hpy hpn
    apply hp.not_dvd_one
    simpa [h.gcd_eq_one] using dvd_gcd hpn (hp.dvd_primorial_iff.mpr hpy)
  · intro h
    by_contra hc
    obtain ⟨p, hp, hpn, hpy⟩ := Prime.not_coprime_iff_dvd.mp hc
    exact h p hp (hp.dvd_primorial_iff.mp hpy) hpn

/-- Below the next possible prime square, every nonunit survivor is a prime. -/
theorem mem_coprimeSieve_primorial_iff {n y k : ℕ} (hn : n < (y + 1) ^ 2) :
    k ∈ coprimeSieve (primorial y) n ↔
      (k = 1 ∧ 1 ≤ n) ∨ (k ≤ n ∧ k.Prime ∧ y < k) := by
  constructor
  · intro hk
    obtain ⟨hk1, hkn, hcop⟩ := mem_coprimeSieve.mp hk
    by_cases hunit : k = 1
    · exact Or.inl ⟨hunit, by omega⟩
    have hno := (coprime_primorial_iff k y).mp hcop
    have hmin : y < k.minFac := by
      by_contra h
      exact hno _ (minFac_prime hunit) (by omega) (minFac_dvd _)
    have hprime : k.Prime := by
      by_contra h
      have hc := minFac_sq_le_self (by omega : 0 < k) h
      nlinarith
    refine Or.inr ⟨hkn, hprime, ?_⟩
    by_contra h
    exact hno k hprime (by omega) (dvd_refl _)
  · rintro (⟨rfl, hkn⟩ | ⟨hkn, hprime, hyk⟩)
    · exact mem_coprimeSieve.mpr ⟨le_rfl, hkn, coprime_one_left _⟩
    · apply mem_coprimeSieve.mpr
      refine ⟨hprime.one_le, hkn, hprime.coprime_iff_not_dvd.mpr ?_⟩
      intro h
      exact not_le_of_gt hyk (hprime.dvd_primorial_iff.mp h)

/-- The survivors are the disjoint union of the unit and the unsieved prime interval. -/
theorem coprimeSieve_primorial_eq {n y : ℕ} (hn : 1 ≤ n) (hsq : n < (y + 1) ^ 2) :
    coprimeSieve (primorial y) n = insert 1 (primesLE n \ primesLE y) := by
  ext k
  rw [mem_coprimeSieve_primorial_iff hsq]
  simp only [mem_insert, mem_sdiff, mem_primesLE]
  constructor
  · rintro (⟨rfl, _⟩ | ⟨hkn, hprime, hyk⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨hkn, hprime⟩, fun h => not_le_of_gt hyk h.1⟩
  · rintro (rfl | ⟨⟨hkn, hprime⟩, hnot⟩)
    · exact Or.inl ⟨rfl, hn⟩
    · exact Or.inr ⟨hkn, hprime, by by_contra h; exact hnot ⟨by omega, hprime⟩⟩

/-- The exact stopping rule for a prime-count lookup, with no assumed distribution estimate. -/
theorem coprimeCount_primorial_eq {n y : ℕ} (hn : 1 ≤ n) (hy : y ≤ n)
    (hsq : n < (y + 1) ^ 2) :
    coprimeCount (primorial y) n = primeCounting n - primeCounting y + 1 := by
  unfold coprimeCount
  have hnot : 1 ∉ primesLE n \ primesLE y := by
    intro h
    have hprime := (mem_primesLE.mp (mem_sdiff.mp h).1).2
    have := hprime.two_le
    omega
  rw [coprimeSieve_primorial_eq hn hsq, card_insert_of_notMem hnot]
  rw [card_sdiff_of_subset (primesLE_mono hy), primesLE_card_eq_primeCounting,
    primesLE_card_eq_primeCounting]

/-- A complete prime prefix and a checked recurrence value imply the actual prime count. -/
theorem primeCounting_eq_of_partialSieveCount {ps : List ℕ} {n y c : ℕ}
    (hprime : ∀ p ∈ ps, p.Prime) (hpair : ps.Pairwise Coprime)
    (hprod : ps.prod = primorial y) (hn : 1 ≤ n) (hy : y ≤ n)
    (hsq : n < (y + 1) ^ 2) (hc : partialSieveCount ps n = c) :
    primeCounting n = c + primeCounting y - 1 := by
  rw [partialSieveCount_eq ps hprime hpair, hprod, coprimeCount_primorial_eq hn hy hsq] at hc
  have hmono := monotone_primeCounting hy
  omega

end Nat
