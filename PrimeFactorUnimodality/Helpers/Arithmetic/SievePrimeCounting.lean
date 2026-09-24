import Mathlib.NumberTheory.PrimeCounting
import PrimeCert.SieveCorrect
import PrimeFactorUnimodality.Mathlib.Data.Nat.BitCountPacked

/-! # Exact prime counts from a shared certified wheel sieve

The pinned PrimeCert sieve supplies primality equivalence only. This module
proves exact count semantics, including the exceptional primes two and three,
the excluded bit for one, and the partial final wheel cell. Packed bit
counts are used only after their complete finite-set identity is proved.
-/

open Finset PrimeCert.Sieve

namespace PrimeFactorUnimodality

/-- The exact number of wheel values at most the endpoint, including one when present. -/
def wheelLength (n : ℕ) : ℕ := (n + 1) / 6 + n / 6 + if n % 6 = 0 then 0 else 1

private theorem wheelLength_spec (n t : ℕ) : num t ≤ n ↔ t < wheelLength n := by
  unfold num wheelLength
  split_ifs <;> omega

/-- Nonzero wheel indices whose retained sieve bits are set, shifted down by one. -/
def wheelPrimeIndices (n bits : ℕ) : Finset ℕ :=
  (range (wheelLength n - 1)).filter (fun i => bits.testBit (i + 1))

/-- The two exceptional primes and every set wheel bit within the exact endpoint. -/
def sievePrimeSet (n bits : ℕ) : Finset ℕ :=
  (({2, 3} : Finset ℕ).filter (fun p => p ≤ n)) ∪
    ((wheelPrimeIndices n bits).image (fun i => num (i + 1)))

private theorem wheel_five_le {t : ℕ} (ht : t ≠ 0) : 5 ≤ num t := by
  simp only [num]
  omega

private theorem wheel_index {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) :
    num ((p - 1) / 3) = p := by
  simp only [num]
  omega

/-- A certified sieve recovers the complete prime set, with no out-of-range wheel value. -/
theorem sievePrimeSet_eq {n bits : ℕ} (h : IsSieve n bits) :
    sievePrimeSet n bits = Nat.primesLE n := by
  ext p
  simp only [sievePrimeSet, wheelPrimeIndices, mem_union, mem_filter, mem_insert, mem_singleton,
    mem_image, mem_range, Nat.mem_primesLE]
  constructor
  · rintro (⟨hp, hpn⟩ | ⟨t, ⟨ht, hb⟩, rfl⟩)
    · exact ⟨hpn, hp.elim (fun hp => hp ▸ Nat.prime_two) (fun hp => hp ▸ Nat.prime_three)⟩
    · have htn : num (t + 1) ≤ n := (wheelLength_spec n (t + 1)).mpr (by omega)
      exact ⟨htn, (h (t + 1) (by omega) htn).mp hb⟩
  · rintro ⟨hpn, hp⟩
    by_cases hp2 : p = 2
    · exact Or.inl ⟨Or.inl hp2, hpn⟩
    by_cases hp3 : p = 3
    · exact Or.inl ⟨Or.inr hp3, hpn⟩
    have hw := wheel_index (hp.mod_six_eq_one_or_five hp2 hp3)
    have h5 : 5 ≤ p := by
      have hmod := hp.mod_six_eq_one_or_five hp2 hp3
      have hpmin := hp.two_le
      omega
    have ht0 : (p - 1) / 3 ≠ 0 := by omega
    right
    have heq : (p - 1) / 3 - 1 + 1 = (p - 1) / 3 := by omega
    refine ⟨(p - 1) / 3 - 1, ⟨?_, ?_⟩, by simpa only [heq] using hw⟩
    · have hlt := (wheelLength_spec n ((p - 1) / 3)).mp (by simpa only [hw] using hpn)
      omega
    · rw [heq]
      exact (h _ ht0 (by simpa only [hw] using hpn)).mpr (by simpa only [hw] using hp)

/-- The two exceptional primes and the injective wheel image contribute disjoint counts. -/
theorem sievePrimeSet_card (n bits : ℕ) :
    (sievePrimeSet n bits).card =
      (if 2 ≤ n then 1 else 0) + (if 3 ≤ n then 1 else 0) +
        (wheelPrimeIndices n bits).card := by
  have hi : Function.Injective (fun i => num (i + 1)) := by
    intro a b hab
    simp only [num] at hab
    omega
  have hd : Disjoint (({2, 3} : Finset ℕ).filter (fun p => p ≤ n))
      ((wheelPrimeIndices n bits).image (fun i => num (i + 1))) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_filter.mp hp).1
    obtain ⟨i, _, rfl⟩ := mem_image.mp hq
    have h5 := wheel_five_le (show i + 1 ≠ 0 by omega)
    simp only [mem_insert, mem_singleton] at hp'
    omega
  rw [sievePrimeSet, card_union_of_disjoint hd, card_image_of_injective _ hi]
  rw [card_filter, sum_insert (by decide), sum_singleton]


/-- One certified sieve also supplies every smaller endpoint without another sieve computation. -/
theorem isSieve_restrict {N n bits : ℕ} (h : IsSieve N bits) (hn : n ≤ N) :
    IsSieve n bits := fun t ht htn => h t ht (htn.trans hn)

/-- A packed exact prefix count, including the two primes omitted by the mod-six wheel. -/
def sievePrimeCount (k n bits : ℕ) : ℕ :=
  (if 2 ≤ n then 1 else 0) + (if 3 ≤ n then 1 else 0) +
    Nat.bitCountBlockPacked k bits 1 (wheelLength n - 1)

/-- The retained sieve and sufficient bit-count depth give the actual prime-counting function. -/
theorem primeCounting_eq_sievePrimeCount {N n bits k : ℕ} (h : IsSieve N bits)
    (hn : n ≤ N) (hk : wheelLength n - 1 ≤ 2 ^ k) :
    Nat.primeCounting n = sievePrimeCount k n bits := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← sievePrimeSet_eq (isSieve_restrict h hn),
    sievePrimeSet_card, sievePrimeCount, Nat.bitCountBlockPacked_eq_card _ _ _ _ hk]
  simp only [wheelPrimeIndices, Nat.add_comm]

/-- Check the finite range, recursion depth and claimed count using only retained data. -/
def checkSievePrimeCount (N k bits n count : ℕ) : Bool :=
  decide (n ≤ N ∧ wheelLength n - 1 ≤ 2 ^ k ∧ sievePrimeCount k n bits = count)

/-- Accepted data is an exact prime count, not a rounded analytic estimate. -/
theorem primeCounting_eq_of_sieve_check {N k bits n count : ℕ} (h : IsSieve N bits)
    (hc : checkSievePrimeCount N k bits n count = true) : Nat.primeCounting n = count := by
  simp only [checkSievePrimeCount, decide_eq_true_eq] at hc
  exact (primeCounting_eq_sievePrimeCount h hc.1 hc.2.1).trans hc.2.2

end PrimeFactorUnimodality
