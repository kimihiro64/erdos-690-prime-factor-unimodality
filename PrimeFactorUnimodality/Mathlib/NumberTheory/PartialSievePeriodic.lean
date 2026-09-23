/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Data.Nat.Periodic
import PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSieve

/-! # Periodic table leaves for partial-sieve counts

A retained wheel table covers one period only. Quotient and remainder then
recover every larger endpoint, including the modulus-one boundary. The table
entries and period total must themselves be proved exact counts.
-/

namespace Nat

open Finset

/-- Positive coprime intervals are zero-based counts of the shifted predicate. -/
theorem coprimeCount_eq_count (m n : ℕ) :
    coprimeCount m n = count (fun a => Coprime (a + 1) m) n := by
  rw [count_eq_card_filter_range]
  unfold coprimeCount
  symm
  apply card_bij (fun a _ => a + 1)
  · intro a ha
    obtain ⟨ha, hc⟩ := mem_filter.mp ha
    exact mem_coprimeSieve.mpr ⟨by omega, by have := mem_range.mp ha; omega, hc⟩
  · intro a ha b hb hab
    omega
  · intro b hb
    obtain ⟨hb1, hbn, hc⟩ := mem_coprimeSieve.mp hb
    refine ⟨b - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
    simpa only [Nat.sub_add_cancel hb1] using hc

/-- One full positive period contains exactly the totient number of survivors. -/
theorem coprimeCount_self (m : ℕ) : coprimeCount m m = totient m := by
  have he : Icc 1 m = Ico 1 (1 + m) := by ext i; simp only [mem_Icc, mem_Ico]; omega
  simpa only [coprimeCount, coprimeSieve, he, coprime_comm] using
    filter_coprime_Ico_eq_totient m 1

/-- Exact table lookup decomposition; the modulus-zero case is also harmless. -/
theorem coprimeCount_eq_mod_add_div_mul (m n : ℕ) :
    coprimeCount m n = coprimeCount m (n % m) + (n / m) * totient m := by
  have hp : Function.Periodic (fun a => Coprime (a + 1) m) m := by
    intro a
    apply propext
    simpa only [Nat.add_right_comm a m 1] using
      (coprime_add_self_left (m := a + 1) (n := m))
  rw [← coprimeCount_self, coprimeCount_eq_count, coprimeCount_eq_count,
    coprimeCount_eq_count]
  exact count_eq_mod_add_div_mul hp n

/-- A table leaf may be reused at an arbitrary endpoint after a single scalar check. -/
theorem sievePhi_eq_of_periodic {p : ℕ → ℕ} {a n m r t v : ℕ}
    (hprime : ∀ i < a, (p i).Prime)
    (hcop : ∀ i < a, ∀ j < i, Coprime (p i) (p j))
    (hm : (∏ i ∈ range a, p i) = m)
    (hr : sievePhi p a (n % m) = r) (ht : totient m = t)
    (hv : r + (n / m) * t = v) : sievePhi p a n = v := by
  rw [sievePhi_eq p a n hprime hcop, hm, coprimeCount_eq_mod_add_div_mul]
  rw [sievePhi_eq p a (n % m) hprime hcop, hm] at hr
  rw [hr, ht, hv]

end Nat
