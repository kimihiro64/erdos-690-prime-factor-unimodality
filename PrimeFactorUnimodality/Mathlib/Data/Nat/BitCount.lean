/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Bitwise

/-! # Balanced counts of bounded natural-number bit blocks

Split a retained bitset in halves recursively, avoiding a separate shift of
the original large integer for every bit. Exact finite-set semantics retain
the requested offset and width; the depth bound prevents truncated counts.
-/

namespace Nat

open Finset

/-- Count the low `2 ^ k` bits by balanced splitting into smaller integers. -/
def bitCountPow : ℕ → ℕ → ℕ
  | 0, bits => if bits.testBit 0 then 1 else 0
  | k + 1, bits =>
    bitCountPow k (bits % 2 ^ (2 ^ k)) + bitCountPow k (bits / 2 ^ (2 ^ k))

/-- Balanced splitting counts exactly the bit indicators in the full requested power-of-two block. -/
theorem bitCountPow_eq_sum (k bits : ℕ) :
    bitCountPow k bits = ∑ i ∈ range (2 ^ k), if bits.testBit i then 1 else 0 := by
  induction k generalizing bits with
  | zero => simp only [bitCountPow, Nat.pow_zero, sum_range_one]
  | succ k ih =>
    rw [bitCountPow, ih, ih, Nat.pow_succ, Nat.mul_two, sum_range_add]
    congr 1
    · apply sum_congr rfl
      intro i hi
      simp [Nat.testBit_mod_two_pow, mem_range.mp hi]
    · apply sum_congr rfl
      intro i hi
      simp [Nat.testBit_div_two_pow, Nat.add_comm]

/-- Masking retains precisely the requested width when the recursion depth is sufficient. -/
theorem bitCountPow_mod_eq_card (k bits width : ℕ) (hw : width ≤ 2 ^ k) :
    bitCountPow k (bits % 2 ^ width) =
      ((range width).filter (fun i => bits.testBit i)).card := by
  rw [bitCountPow_eq_sum, ← card_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range, testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1.trans_le hw, h⟩⟩

/-- Count one retained bit block without examining unrelated lower or upper bits. -/
def bitCountBlock (k bits start width : ℕ) : ℕ :=
  bitCountPow k ((bits / 2 ^ start) % 2 ^ width)

/-- Block counts have exact finite-set semantics, including arbitrary offsets and zero width. -/
theorem bitCountBlock_eq_card (k bits start width : ℕ) (hw : width ≤ 2 ^ k) :
    bitCountBlock k bits start width =
      ((range width).filter (fun i => bits.testBit (start + i))).card := by
  rw [bitCountBlock, bitCountPow_mod_eq_card k _ width hw]
  congr 1
  ext i
  simp [testBit_div_two_pow, Nat.add_comm]

/-- Adjacent bit blocks compose without overlap or omitted bits. -/
theorem bitCountBlock_append (k bits start a b : ℕ) (hab : a + b ≤ 2 ^ k) :
    bitCountBlock k bits start (a + b) =
      bitCountBlock k bits start a + bitCountBlock k bits (start + a) b := by
  rw [bitCountBlock_eq_card _ _ _ _ hab,
    bitCountBlock_eq_card _ _ _ _ (by omega), bitCountBlock_eq_card _ _ _ _ (by omega)]
  simp only [card_filter, sum_range_add, Nat.add_assoc]

end Nat
