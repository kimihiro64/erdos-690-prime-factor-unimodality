/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Data.Nat.BitCountPacked

/-! # Simultaneous strict comparisons of packed unsigned integers

Each `2 * s`-bit lane stores an `s`-bit integer in its low half. Adding the
low-half mask before subtracting one operand prevents borrowing across
lanes. The upper half of each resulting lane is one exactly when the
corresponding strict comparison holds. One whole-integer mask comparison
therefore certifies every lane, including leading zero lanes.
-/

namespace Nat

/-- Extract a `2 * s`-bit lane at its declared offset. -/
def bitLaneDigit (s x i : ℕ) : ℕ := x / 2 ^ (2 * s * i) % 2 ^ (2 * s)

/-- An integer with a one in each of the `n` low-half lanes. -/
def bitLaneOnes (s n : ℕ) : ℕ := bitLaneMask s n / (2 ^ s - 1)

/-- Recursive specification of the all-ones lane pattern, used only in proofs. -/
def bitLaneOnesRec (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 ^ (2 * s) * bitLaneOnesRec s n

/-- The closed integer pattern equals its recursive lane specification. -/
theorem bitLaneOnes_eq (s n : ℕ) (hs : 0 < s) :
    bitLaneOnes s n = bitLaneOnesRec s n := by
  have hm : bitLaneMaskRec s n = (2 ^ s - 1) * bitLaneOnesRec s n := by
    induction n with
    | zero => simp [bitLaneMaskRec, bitLaneOnesRec]
    | succ n ih => simp only [bitLaneMaskRec, bitLaneOnesRec, ih]; ring
  rw [bitLaneOnes, bitLaneMask_eq s n hs, hm, Nat.mul_div_right]
  have := Nat.one_lt_pow (by omega : s ≠ 0) (by decide : 1 < 2)
  omega

/-- A masked input has a bounded low lane and remains masked after deleting that lane. -/
theorem bitLaneMasked_head_tail (s n x : ℕ) (hs : 0 < s)
    (hx : x &&& bitLaneMask s (n + 1) = x) :
    x % 2 ^ (2 * s) < 2 ^ s ∧
      (x / 2 ^ (2 * s)) &&& bitLaneMask s n = x / 2 ^ (2 * s) := by
  constructor
  · have he := bitLane_low s n x hs
    rw [hx] at he
    rw [he]
    exact Nat.mod_lt _ (by positivity)
  · have he := congrArg (fun v => v / 2 ^ (2 * s)) hx
    rwa [Nat.and_div_two_pow, bitLaneMask_div s n hs] at he

/-- The guarded difference whose high halves encode strict comparisons. -/
def bitLaneDifference (s n x y : ℕ) : ℕ := y + bitLaneMask s n - x

/-- No subtraction borrows and no addition carries across the declared lanes. -/
theorem bitLaneDifference_split (s n x y : ℕ) (hs : 0 < s)
    (hx : x &&& bitLaneMask s (n + 1) = x)
    (hy : y &&& bitLaneMask s (n + 1) = y) :
    bitLaneDifference s (n + 1) x y =
      (y % 2 ^ (2 * s) + (2 ^ s - 1) - x % 2 ^ (2 * s)) +
        2 ^ (2 * s) * bitLaneDifference s n (x / 2 ^ (2 * s)) (y / 2 ^ (2 * s)) := by
  have hxt := bitLaneMasked_head_tail s n x hs hx
  have hyt := bitLaneMasked_head_tail s n y hs hy
  have hxle : x ≤ bitLaneMask s (n + 1) := by
    rw [← hx]
    exact Nat.and_le_right
  have hxtle : x / 2 ^ (2 * s) ≤ bitLaneMask s n := by
    rw [← hxt.2]
    exact Nat.and_le_right
  have hm : bitLaneMask s (n + 1) = (2 ^ s - 1) + 2 ^ (2 * s) * bitLaneMask s n := by
    rw [bitLaneMask_eq _ _ hs, bitLaneMaskRec, ← bitLaneMask_eq _ _ hs]
  have h₁ := Nat.sub_add_cancel (show x ≤ y + bitLaneMask s (n + 1) by omega)
  have h₂ := Nat.sub_add_cancel (show x % 2 ^ (2 * s) ≤
      y % 2 ^ (2 * s) + (2 ^ s - 1) by omega)
  have h₃ := Nat.sub_add_cancel (show x / 2 ^ (2 * s) ≤
      y / 2 ^ (2 * s) + bitLaneMask s n by omega)
  have h₄ := Nat.mod_add_div x (2 ^ (2 * s))
  have h₅ := Nat.mod_add_div y (2 ^ (2 * s))
  have h₆ := congrArg (fun v => 2 ^ (2 * s) * v) h₃
  simp only [Nat.mul_add] at h₆
  unfold bitLaneDifference
  omega

/-- A guarded low difference fits in its lane, including the smallest positive width. -/
theorem bitLaneDifference_low_lt (s n x y : ℕ) (hs : 0 < s)
    (hy : y &&& bitLaneMask s (n + 1) = y) :
    y % 2 ^ (2 * s) + (2 ^ s - 1) - x % 2 ^ (2 * s) < 2 ^ (2 * s) := by
  have hylo := (bitLaneMasked_head_tail s n y hs hy).1
  have hp : 1 < 2 ^ s := Nat.one_lt_pow (by omega) (by decide)
  have he : 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by rw [two_mul, pow_add]
  have hm : 2 ^ s - 1 < 2 ^ s := Nat.sub_lt (by positivity) (by decide)
  have hle := Nat.sub_le (y % 2 ^ (2 * s) + (2 ^ s - 1)) (x % 2 ^ (2 * s))
  nlinarith

/-- The high halves of all guarded differences, retained simultaneously. -/
def bitLaneCompareMask (s n x y : ℕ) : ℕ :=
  (bitLaneDifference s n x y / 2 ^ s) &&& bitLaneMask s n

/-- The lowest comparison digit is the high half of its guarded difference. -/
theorem bitLaneCompareMask_mod (s n x y : ℕ) (hs : 0 < s)
    (hx : x &&& bitLaneMask s (n + 1) = x)
    (hy : y &&& bitLaneMask s (n + 1) = y) :
    bitLaneCompareMask s (n + 1) x y % 2 ^ (2 * s) =
      (y % 2 ^ (2 * s) + (2 ^ s - 1) - x % 2 ^ (2 * s)) / 2 ^ s := by
  rw [bitLaneCompareMask, bitLane_low _ _ _ hs, ← Nat.mod_mul_right_div_self]
  rw [← pow_add, ← two_mul, bitLaneDifference_split s n x y hs hx hy,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (bitLaneDifference_low_lt s n x y hs hy)]

/-- Removing one comparison digit commutes with comparing the remaining input lanes. -/
theorem bitLaneCompareMask_div (s n x y : ℕ) (hs : 0 < s)
    (hx : x &&& bitLaneMask s (n + 1) = x)
    (hy : y &&& bitLaneMask s (n + 1) = y) :
    bitLaneCompareMask s (n + 1) x y / 2 ^ (2 * s) =
      bitLaneCompareMask s n (x / 2 ^ (2 * s)) (y / 2 ^ (2 * s)) := by
  have hd : bitLaneDifference s (n + 1) x y / 2 ^ (2 * s) =
      bitLaneDifference s n (x / 2 ^ (2 * s)) (y / 2 ^ (2 * s)) := by
    rw [bitLaneDifference_split s n x y hs hx hy, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (bitLaneDifference_low_lt s n x y hs hy), zero_add]
  simp only [bitLaneCompareMask, Nat.and_div_two_pow, bitLaneMask_div _ _ hs]
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ s), ← Nat.div_div_eq_div_mul, hd]

/-- Whole-integer validation of the widths, input masks and every strict comparison. -/
def checkBitLaneLt (s n x y : ℕ) : Bool :=
  decide (0 < s ∧ x &&& bitLaneMask s n = x ∧ y &&& bitLaneMask s n = y ∧
    bitLaneCompareMask s n x y = bitLaneOnes s n)

/-- A successful packed check proves every requested scalar comparison. -/
theorem bitLaneDigit_lt_of_check (s n x y : ℕ) (h : checkBitLaneLt s n x y = true) :
    ∀ i < n, bitLaneDigit s x i < bitLaneDigit s y i := by
  simp only [checkBitLaneLt, decide_eq_true_eq] at h
  obtain ⟨hs, hx, hy, hcmp⟩ := h
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    have hxt := bitLaneMasked_head_tail s n x hs hx
    have hyt := bitLaneMasked_head_tail s n y hs hy
    have hp : 1 < 2 ^ (2 * s) := Nat.one_lt_pow (by omega) (by decide)
    have hm : bitLaneOnes s (n + 1) % 2 ^ (2 * s) = 1 := by
      rw [bitLaneOnes_eq _ _ hs, bitLaneOnesRec, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hp]
    have hd : bitLaneOnes s (n + 1) / 2 ^ (2 * s) = bitLaneOnes s n := by
      rw [bitLaneOnes_eq _ _ hs, bitLaneOnesRec, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hp, zero_add, ← bitLaneOnes_eq _ _ hs]
    have hhead := congrArg (fun v => v % 2 ^ (2 * s)) hcmp
    rw [bitLaneCompareMask_mod s n x y hs hx hy, hm] at hhead
    have htail := congrArg (fun v => v / 2 ^ (2 * s)) hcmp
    rw [bitLaneCompareMask_div s n x y hs hx hy, hd] at htail
    intro i hi
    cases i with
    | zero =>
      simp only [bitLaneDigit, Nat.mul_zero, pow_zero, Nat.div_one]
      have hle := Nat.div_mul_le_self
        (y % 2 ^ (2 * s) + (2 ^ s - 1) - x % 2 ^ (2 * s)) (2 ^ s)
      rw [hhead, one_mul] at hle
      omega
    | succ i =>
      have ht := ih (x / 2 ^ (2 * s)) (y / 2 ^ (2 * s)) hxt.2 hyt.2 htail i (by omega)
      simpa only [bitLaneDigit, Nat.mul_succ, pow_add, Nat.div_div_eq_div_mul,
        Nat.mul_comm (2 ^ (2 * s))] using ht

end Nat
