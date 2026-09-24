/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Bitwise

/-! # Balanced products selected by finite bit blocks

A bounded product reads one compact bitset, splitting it into balanced halves
and skipping empty subtrees. Its exact finite-product semantics apply to any
commutative monoid, arbitrary offsets and clipped widths. The range identity
assembles independently checked chunks without re-evaluating their products.
-/

namespace Nat

open Finset

variable {M : Type*} [CommMonoid M]

/-- The exact product of the values at set-bit positions in one finite block. -/
def bitProductRange (f : ℕ → M) (bits start width : ℕ) : M :=
  ∏ i ∈ range width, if bits.testBit (start + i) then f (start + i) else 1

/-- Adjacent finite block products multiply without overlap or omitted positions. -/
theorem bitProductRange_add (f : ℕ → M) (bits start a b : ℕ) :
    bitProductRange f bits start (a + b) =
      bitProductRange f bits start a * bitProductRange f bits (start + a) b := by
  simp only [bitProductRange, prod_range_add, Nat.add_assoc]

/-- Balanced product over the low `2 ^ k` bits, skipping zero subtrees. -/
def bitProductPow (f : ℕ → M) : ℕ → ℕ → ℕ → M
  | 0, start, bits => if bits.testBit 0 then f start else 1
  | k + 1, start, bits =>
    if bits = 0 then 1 else
      bitProductPow f k start (bits % 2 ^ (2 ^ k)) *
        bitProductPow f k (start + 2 ^ k) (bits / 2 ^ (2 ^ k))

/-- Balanced evaluation equals the product of the selected values, including offset zero. -/
theorem bitProductPow_eq_prod (f : ℕ → M) (k start bits : ℕ) :
    bitProductPow f k start bits =
      ∏ i ∈ range (2 ^ k), if bits.testBit i then f (start + i) else 1 := by
  induction k generalizing start bits with
  | zero => simp [bitProductPow]
  | succ k ih =>
    by_cases hz : bits = 0
    · simp [hz, bitProductPow]
    rw [bitProductPow, ite_eq_right hz, ih, ih, Nat.pow_succ, Nat.mul_two, prod_range_add]
    congr 1
    · apply prod_congr rfl
      intro i hi
      simp [Nat.testBit_mod_two_pow, mem_range.mp hi]
    · apply prod_congr rfl
      intro i hi
      simp [Nat.testBit_div_two_pow, Nat.add_comm, Nat.add_left_comm]

/-- Retain one offset bit block and evaluate its selected product with depth `k`. -/
def bitProductBlock (f : ℕ → M) (k bits start width : ℕ) : M :=
  bitProductPow f k start ((bits / 2 ^ start) % 2 ^ width)

/-- Sufficient depth gives the product over exactly the retained set-bit positions. -/
theorem bitProductBlock_eq_prod (f : ℕ → M) (k bits start width : ℕ)
    (hw : width ≤ 2 ^ k) :
    bitProductBlock f k bits start width =
      ∏ i ∈ (range width).filter (fun i => bits.testBit (start + i)), f (start + i) := by
  rw [bitProductBlock, bitProductPow_eq_prod, ← prod_filter]
  apply prod_congr
  · ext i
    simp only [mem_filter, mem_range, testBit_mod_two_pow, testBit_div_two_pow,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [Nat.add_comm i start]
    exact ⟨fun h => h.2, fun h => ⟨h.1.trans_le hw, h⟩⟩
  · intro i hi
    rfl

/-- The executable block product has the exact range-product semantics. -/
theorem bitProductBlock_eq_range (f : ℕ → M) (k bits start width : ℕ)
    (hw : width ≤ 2 ^ k) :
    bitProductBlock f k bits start width = bitProductRange f bits start width := by
  rw [bitProductBlock_eq_prod _ _ _ _ _ hw, prod_filter]
  rfl

end Nat
