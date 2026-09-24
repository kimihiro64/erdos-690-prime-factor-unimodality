import Mathlib.NumberTheory.Primorial
import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeCounting
import PrimeFactorUnimodality.Mathlib.Data.Nat.BitProduct

/-! # Exact primorials from compact sieve-product rows

The checked sieve supplies the prime set. Adjacent balanced bit products
cover its wheel positions exactly once; row composition retains earlier
checks. The exceptional primes two and three are handled separately,
including endpoints below them. These products supply tight theta anchors
without a separate logarithm evaluation for every prime.
-/

namespace PrimeFactorUnimodality

open Finset PrimeCert.Sieve

/-- Evaluate the primorial proposal from a sieve and a sufficiently deep balanced product. -/
def sievePrimeProduct (k n bits : ℕ) : ℕ :=
  (if 2 ≤ n then 2 else 1) * (if 3 ≤ n then 3 else 1) *
    Nat.bitProductBlock num k bits 1 (wheelLength n - 1)

/-- The exact prime product is the product of the exceptional primes and selected wheel entries. -/
theorem primorial_eq_wheelProduct {N n bits : ℕ} (h : IsSieve N bits) (hn : n ≤ N) :
    primorial n = (if 2 ≤ n then 2 else 1) * (if 3 ≤ n then 3 else 1) *
      Nat.bitProductRange num bits 1 (wheelLength n - 1) := by
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
    simp only [mem_insert, mem_singleton] at hp'
    simp only [num] at hp'
    omega
  rw [primorial_eq_prod_primesLE, ← sievePrimeSet_eq (isSieve_restrict h hn),
    sievePrimeSet, prod_union hd, prod_image (fun _ _ _ _ hab => hi hab)]
  rw [prod_filter, prod_insert (by decide), prod_singleton]
  simp only [wheelPrimeIndices, Nat.bitProductRange, prod_filter, Nat.add_comm]

/-- Correct sieving and sufficient depth identify the executable product with the primorial. -/
theorem primorial_eq_sievePrimeProduct {N n bits k : ℕ} (h : IsSieve N bits)
    (hn : n ≤ N) (hk : wheelLength n - 1 ≤ 2 ^ k) :
    primorial n = sievePrimeProduct k n bits := by
  simpa only [sievePrimeProduct, Nat.bitProductBlock_eq_range _ _ _ _ _ hk] using
    primorial_eq_wheelProduct h hn

/-- One adjacent wheel block, its evaluation depth and externally proposed exact product. -/
structure SieveProductRow where
  width : ℕ
  depth : ℕ
  value : ℕ

namespace SieveProductRow

/-- Check the local product and reject depths that would truncate the block. -/
def check (row : SieveProductRow) (bits start : ℕ) : Bool :=
  decide (row.width ≤ 2 ^ row.depth ∧
    Nat.bitProductBlock num row.depth bits start row.width = row.value)

/-- Check consecutive products, advancing by the exact width of each row. -/
def checkTrace (bits : ℕ) (start : ℕ) : List SieveProductRow → Bool
  | [] => true
  | row :: rest => row.check bits start && checkTrace bits (start + row.width) rest

/-- Independently checked consecutive row lists compose without repeating their computations. -/
theorem checkTrace_append (bits start : ℕ) (left right : List SieveProductRow) :
    checkTrace bits start (left ++ right) =
      (checkTrace bits start left && checkTrace bits (start + (left.map width).sum) right) := by
  induction left generalizing start with
  | nil => simp [checkTrace]
  | cons row rest ih =>
    simp only [List.cons_append, checkTrace, ih, List.map_cons, List.sum_cons,
      Nat.add_assoc, Bool.and_assoc]

/-- Checked local products multiply to the exact selected product over their combined range. -/
theorem range_eq_of_checkTrace {bits start : ℕ} {rows : List SieveProductRow}
    (h : checkTrace bits start rows = true) :
    Nat.bitProductRange num bits start (rows.map width).sum = (rows.map value).prod := by
  induction rows generalizing start with
  | nil => simp [Nat.bitProductRange]
  | cons row rest ih =>
    simp only [checkTrace, Bool.and_eq_true, check, decide_eq_true_eq] at h
    simp only [List.map_cons, List.sum_cons, List.prod_cons, Nat.bitProductRange_add]
    rw [← Nat.bitProductBlock_eq_range _ row.depth _ _ _ h.1.1, h.1.2, ih h.2]

/-- Check complete wheel coverage, the exceptional factors and the product trace. -/
def checkPrimorial (n bits : ℕ) (rows : List SieveProductRow) (value : ℕ) : Bool :=
  decide ((rows.map width).sum = wheelLength n - 1 ∧
    (if 2 ≤ n then 2 else 1) * (if 3 ≤ n then 3 else 1) * (rows.map SieveProductRow.value).prod =
      value) && checkTrace bits 1 rows

/-- Complete checked rows give the actual primorial, not merely a proposed numerical product. -/
theorem primorial_eq_of_check {N n bits value : ℕ} {rows : List SieveProductRow}
    (h : IsSieve N bits) (hn : n ≤ N) (hc : checkPrimorial n bits rows value = true) :
    primorial n = value := by
  simp only [checkPrimorial, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [primorial_eq_wheelProduct h hn, ← hc.1.1, range_eq_of_checkTrace hc.2]
  exact hc.1.2

end SieveProductRow

end PrimeFactorUnimodality
