import PrimeFactorUnimodality.Mathlib.Data.Nat.BitCountPacked

/-! # Packed counts preserve offsets, clipping, depth and exact cardinalities -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Nat Finset

example (k bits : ℕ) : bitCountPacked k bits = bitCountPow k bits :=
  bitCountPacked_eq k bits

example (k bits start width : ℕ) :
    bitCountBlockPacked k bits start width = bitCountBlock k bits start width :=
  bitCountBlockPacked_eq k bits start width

example (k bits start width : ℕ) (hw : width ≤ 2 ^ k) :
    bitCountBlockPacked k bits start width =
      ((range width).filter (fun i => bits.testBit (start + i))).card :=
  bitCountBlockPacked_eq_card k bits start width hw

example (s n bits : ℕ) (hs : 0 < s) :
    bitLaneSum (2 * s) n (bitLaneMerge s n bits) = bitLaneSum s (2 * n) bits :=
  bitLaneMerge_sum s n bits hs

set_option maxRecDepth 10000 in
example : ∀ k : Fin 8, ∀ bits : Fin 256, bitCountPacked k bits = bitCountPow k bits := by
  decide +kernel

example : bitCountBlockPacked 1 13 2 2 = 2 := by decide +kernel
example : bitCountBlockPacked 3 65535 3 0 = 0 := by decide +kernel
example : bitCountBlockPacked 3 65535 3 5 = 5 := by decide +kernel
example : bitCountBlockPacked 0 3 0 2 = 1 := by decide +kernel
example : bitCountBlockPacked 5 65535 50 16 = 0 := by decide +kernel
example : bitCountPacked 4 (2 ^ 16 + 43981) = 10 := by decide +kernel
example : bitCountPacked 0 0 = 0 ∧ bitCountPacked 0 1 = 1 := by decide +kernel
example : bitCountBlockPacked 4 43981 0 16 =
    bitCountBlockPacked 4 43981 0 7 + bitCountBlockPacked 4 43981 7 9 :=
  bitCountBlockPacked_append 4 43981 0 7 9 (by decide)

example : bitCountPacked 20 (2 ^ 1048576 - 1) = 1048576 := by decide +kernel

end PrimeFactorUnimodality.Tests
