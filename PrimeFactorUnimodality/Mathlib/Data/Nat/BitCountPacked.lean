/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorUnimodality.Mathlib.Data.Nat.BitCount

/-! # Packed population counts by carry-free lane merging

A geometric mask selects the low half of every lane. Two masked integers
merge all adjacent lanes at once; their sums fit in the doubled lane width.
Repeating this for `k` stages counts the low `2 ^ k` bits without recursive
per-bit traversal. These are arbitrary-precision integer operations, not
constant-time machine-word operations. The recursive lane sum is used only
in the correctness proof, never by the executable counter.

Exact equality with `bitCountPow` preserves clipping and insufficient-depth
behavior. Cardinality and adjacent-block composition require the same width
bound as the original interface.
-/

namespace Nat

/-- The low `s` bits of each of `n` adjacent `2 * s`-bit lanes, in closed form. -/
def bitLaneMask (s n : ℕ) : ℕ := (2 ^ s - 1) * (2 ^ (2 * s * n) - 1) / (2 ^ (2 * s) - 1)

/-- Sum adjacent `s`-bit lanes simultaneously, retaining exactly `n` pairs. -/
def bitLaneMerge (s n bits : ℕ) : ℕ :=
  let mask := bitLaneMask s n
  (bits &&& mask) + ((bits / 2 ^ s) &&& mask)

/-- Merge `2 ^ k` lanes of width `s` into one digit sum using `k` whole-integer stages. -/
def packedBitCountAux (s : ℕ) : ℕ → ℕ → ℕ
  | 0, bits => bits % 2 ^ s
  | k + 1, bits => packedBitCountAux (2 * s) k (bitLaneMerge s (2 ^ k) bits)

/-- Count the low `2 ^ k` bits by packed, carry-free lane merging. -/
def bitCountPacked (k bits : ℕ) : ℕ := packedBitCountAux 1 k bits

/-- Packed count of an offset, width-clipped block, with the original depth convention. -/
def bitCountBlockPacked (k bits start width : ℕ) : ℕ :=
  bitCountPacked k ((bits / 2 ^ start) % 2 ^ width)

/-- Recursive specification of the geometric lane mask, used only in proofs. -/
def bitLaneMaskRec (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (2 ^ s - 1) + 2 ^ (2 * s) * bitLaneMaskRec s n

/-- The closed-form mask equals its digit-by-digit specification. -/
theorem bitLaneMask_eq (s n : ℕ) (hs : 0 < s) :
    bitLaneMask s n = bitLaneMaskRec s n := by
  have hb : 1 < 2 ^ (2 * s) := Nat.one_lt_pow (by omega) (by decide)
  have hid : bitLaneMaskRec s n * (2 ^ (2 * s) - 1) + (2 ^ s - 1) =
      (2 ^ s - 1) * (2 ^ (2 * s)) ^ n := by
    induction n with
    | zero => simp [bitLaneMaskRec]
    | succ n ih =>
        rw [bitLaneMaskRec, pow_succ]
        calc
          _ = 2 ^ (2 * s) * (bitLaneMaskRec s n * (2 ^ (2 * s) - 1) +
              (2 ^ s - 1)) := by
            have he := Nat.sub_add_cancel (show 1 ≤ 2 ^ (2 * s) by omega)
            nlinarith
          _ = _ := by rw [ih]; ring
  have he : bitLaneMaskRec s n * (2 ^ (2 * s) - 1) =
      (2 ^ s - 1) * ((2 ^ (2 * s)) ^ n - 1) := by
    rw [Nat.mul_sub_left_distrib (2 ^ s - 1) ((2 ^ (2 * s)) ^ n) 1, Nat.mul_one]
    omega
  rw [bitLaneMask, pow_mul, ← he, Nat.mul_div_cancel]
  omega

/-- The first mask lane contains exactly the low-half mask. -/
theorem bitLaneMask_mod (s n : ℕ) (hs : 0 < s) :
    bitLaneMask s (n + 1) % 2 ^ (2 * s) = 2 ^ s - 1 := by
  have hb : 2 ^ s - 1 < 2 ^ (2 * s) :=
    (Nat.sub_lt (by positivity : 0 < 2 ^ s) (by decide : 0 < 1)).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  rw [bitLaneMask_eq _ _ hs, bitLaneMaskRec]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hb]

/-- Removing one mask lane gives the mask for the remaining lanes. -/
theorem bitLaneMask_div (s n : ℕ) (hs : 0 < s) :
    bitLaneMask s (n + 1) / 2 ^ (2 * s) = bitLaneMask s n := by
  have hb : 2 ^ s - 1 < 2 ^ (2 * s) :=
    (Nat.sub_lt (by positivity : 0 < 2 ^ s) (by decide : 0 < 1)).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  rw [bitLaneMask_eq _ _ hs, bitLaneMaskRec,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hb, zero_add,
    bitLaneMask_eq _ _ hs]

/-- Masking and retaining the first doubled lane extracts the original low digit. -/
theorem bitLane_low (s n bits : ℕ) (hs : 0 < s) :
    (bits &&& bitLaneMask s (n + 1)) % 2 ^ (2 * s) = bits % 2 ^ s := by
  rw [Nat.and_mod_two_pow, bitLaneMask_mod _ _ hs, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

/-- Adding two width-`s` digits never carries out of a width-`2 * s` lane. -/
theorem bitLane_no_carry (s bits : ℕ) (hs : 0 < s) :
    bits % 2 ^ s + (bits / 2 ^ s) % 2 ^ s < 2 ^ (2 * s) := by
  have hb : 1 < 2 ^ s := Nat.one_lt_pow (by omega) (by decide)
  have h₁ := Nat.mod_lt bits (show 0 < 2 ^ s by positivity)
  have h₂ := Nat.mod_lt (bits / 2 ^ s) (show 0 < 2 ^ s by positivity)
  rw [show 2 * s = s + s by omega, pow_add]
  nlinarith

/-- The first merged lane is exactly the sum of the first two original digits. -/
theorem bitLaneMerge_mod (s n bits : ℕ) (hs : 0 < s) :
    bitLaneMerge s (n + 1) bits % 2 ^ (2 * s) =
      bits % 2 ^ s + (bits / 2 ^ s) % 2 ^ s := by
  rw [bitLaneMerge, Nat.add_mod, bitLane_low _ _ _ hs, bitLane_low _ _ _ hs,
    Nat.mod_eq_of_lt (bitLane_no_carry s bits hs)]

/-- Removing a merged lane commutes with merging the remaining original lanes. -/
theorem bitLaneMerge_div (s n bits : ℕ) (hs : 0 < s) :
    bitLaneMerge s (n + 1) bits / 2 ^ (2 * s) =
      bitLaneMerge s n (bits / 2 ^ (2 * s)) := by
  have hcarry := bitLane_no_carry s bits hs
  simp only [bitLaneMerge]
  rw [Nat.add_div (by positivity), bitLane_low _ _ _ hs, bitLane_low _ _ _ hs]
  rw [ite_eq_right (by omega : ¬ 2 ^ (2 * s) ≤ bits % 2 ^ s + bits / 2 ^ s % 2 ^ s)]
  rw [Nat.add_zero, Nat.and_div_two_pow, Nat.and_div_two_pow,
    bitLaneMask_div _ _ hs]
  congr 2
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- Sum exactly `n` base-`2 ^ s` digits, including leading zero digits. -/
def bitLaneSum (s : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, bits => bits % 2 ^ s + bitLaneSum s n (bits / 2 ^ s)

/-- One packed merge preserves the complete sum of all retained digits. -/
theorem bitLaneMerge_sum (s n bits : ℕ) (hs : 0 < s) :
    bitLaneSum (2 * s) n (bitLaneMerge s n bits) = bitLaneSum s (2 * n) bits := by
  induction n generalizing bits with
  | zero => simp [bitLaneSum]
  | succ n ih =>
    rw [bitLaneSum, bitLaneMerge_mod _ _ _ hs, bitLaneMerge_div _ _ _ hs, ih]
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, bitLaneSum, bitLaneSum]
    rw [Nat.div_div_eq_div_mul, ← pow_add, ← Nat.two_mul, Nat.add_assoc]

/-- The executable packed recurrence equals the exact retained digit sum. -/
theorem packedBitCountAux_eq (s k bits : ℕ) (hs : 0 < s) :
    packedBitCountAux s k bits = bitLaneSum s (2 ^ k) bits := by
  induction k generalizing s bits with
  | zero => simp [packedBitCountAux, bitLaneSum]
  | succ k ih =>
    rw [packedBitCountAux, ih _ _ (by omega), bitLaneMerge_sum _ _ _ hs,
      pow_succ, Nat.mul_comm (2 ^ k) 2]

/-- Width-one digit sums count precisely the set bits. -/
theorem bitLaneSum_one_eq_sum (n bits : ℕ) :
    bitLaneSum 1 n bits = ∑ i ∈ Finset.range n, if bits.testBit i then 1 else 0 := by
  induction n generalizing bits with
  | zero => simp [bitLaneSum]
  | succ n ih =>
    have hbit : bits % 2 = if bits.testBit 0 then 1 else 0 := by
      have := Nat.mod_lt bits (show 0 < 2 by decide)
      rw [Nat.testBit_zero]
      simp only [decide_eq_true_eq]
      split_ifs <;> omega
    simp only [bitLaneSum, Nat.pow_one, ih, Finset.sum_range_succ', Nat.testBit_div_two]
    rw [hbit, Nat.add_comm]

/-- Packed and recursively split counters agree for every depth and input. -/
theorem bitCountPacked_eq (k bits : ℕ) : bitCountPacked k bits = bitCountPow k bits := by
  rw [bitCountPacked, packedBitCountAux_eq _ _ _ (by decide),
    bitLaneSum_one_eq_sum, bitCountPow_eq_sum]

/-- Packed blocks retain the original clipping, offset and depth semantics. -/
theorem bitCountBlockPacked_eq (k bits start width : ℕ) :
    bitCountBlockPacked k bits start width = bitCountBlock k bits start width :=
  bitCountPacked_eq k _

/-- With sufficient depth, a packed block counts exactly its finite set of set-bit positions. -/
theorem bitCountBlockPacked_eq_card (k bits start width : ℕ) (hw : width ≤ 2 ^ k) :
    bitCountBlockPacked k bits start width =
      ((Finset.range width).filter (fun i => bits.testBit (start + i))).card := by
  rw [bitCountBlockPacked_eq, bitCountBlock_eq_card _ _ _ _ hw]

/-- Adjacent packed block counts compose without overlap or loss. -/
theorem bitCountBlockPacked_append (k bits start a b : ℕ) (hab : a + b ≤ 2 ^ k) :
    bitCountBlockPacked k bits start (a + b) =
      bitCountBlockPacked k bits start a + bitCountBlockPacked k bits (start + a) b := by
  simpa only [bitCountBlockPacked_eq] using bitCountBlock_append k bits start a b hab

end Nat
