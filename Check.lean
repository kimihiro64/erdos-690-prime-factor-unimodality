import Mathlib.Data.ZMod.Basic
import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod

/-! # Fast modular-power smoke checks -/

namespace PrimeFactorUnimodality

example : fastPowMod 3 10 9 = 3 := by decide

example : (3 : ZMod 10) ^ 9 = (3 : ZMod 10) := by
  have computed : fastPowMod 3 10 9 = 3 := by decide
  change (((3 ^ 9 : Nat) : Nat) : ZMod 10) = ((3 : Nat) : ZMod 10)
  rw [← ZMod.natCast_mod (3 ^ 9) 10]
  rw [← fastPowMod_eq_pow_mod, computed]

end PrimeFactorUnimodality
