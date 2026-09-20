import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-! # Kernel-reducible binary modular exponentiation

`fastPowMod` separates a small, reusable correctness proof from closed modular
computations. This lets `decide` check a Fermat certificate without expanding
one enormous proof term containing every intermediate residue.
-/

namespace PrimeFactorUnimodality

def fastPowMod (a m : Nat) : Nat → Nat :=
  Nat.binaryRec' (1 % m) fun odd _ _ half =>
    let square := half * half % m
    if odd then square * (a % m) % m else square

theorem fastPowMod_eq_pow_mod (a m e : Nat) :
    fastPowMod a m e = a ^ e % m := by
  induction e using Nat.binaryRec' with
  | zero => rfl
  | bit odd n h ih =>
      simp only [fastPowMod] at ih
      rw [fastPowMod, Nat.binaryRec'_eq _ _ h]
      cases odd <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.bit_false, Nat.bit_true]
      · rw [ih, Nat.two_mul, Nat.pow_add]
        exact (Nat.mul_mod (a ^ n) (a ^ n) m).symm
      · rw [ih, Nat.two_mul, Nat.pow_succ, Nat.pow_add]
        rw [Nat.mul_mod (a ^ n * a ^ n) a m, Nat.mul_mod (a ^ n) (a ^ n) m]

theorem natCast_fastPowMod_eq_pow (a m e : Nat) :
    ((fastPowMod a m e : Nat) : ZMod m) = (a : ZMod m) ^ e := by
  rw [fastPowMod_eq_pow_mod, ZMod.natCast_mod]
  simp only [Nat.cast_pow]

end PrimeFactorUnimodality
