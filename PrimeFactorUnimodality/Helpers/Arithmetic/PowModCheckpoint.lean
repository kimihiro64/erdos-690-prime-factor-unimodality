module
public import Mathlib.Data.Nat.ModEq

set_option autoImplicit false

/-! # Modular power checkpoints

Each row consumes a bounded binary window. Intermediate residues are
checked independently and composed through the invariant below.
-/

public section
namespace PrimeFactorUnimodality

/-- Keep the power opaque while the kernel compares checkpoint types. -/
structure PowModState (a m e r : Nat) : Prop where
  eq : a ^ e % m = r

theorem powModState_zero (a m : Nat) (hm : decide (1 < m) = true) :
    PowModState a m 0 1 := by
  constructor
  simpa using Nat.mod_eq_of_lt (of_decide_eq_true hm)

@[expose] def powBitExponent (bits : Nat) : Nat → Nat → Nat
  | 0, e => e
  | fuel + 1, e => powBitExponent bits fuel (2 * e + if bits.testBit fuel then 1 else 0)

@[expose] def powBitRun (a m bits : Nat) : Nat → Nat → Nat
  | 0, r => r
  | fuel + 1, r =>
    let square := r * r % m
    powBitRun a m bits fuel (if bits.testBit fuel then square * a % m else square)

theorem powBitRun_eq (a m bits fuel e r : Nat)
    (h : a ^ e % m = r) :
    a ^ powBitExponent bits fuel e % m = powBitRun a m bits fuel r := by
  induction fuel generalizing e r with
  | zero => exact h
  | succ fuel ih =>
    simp only [powBitExponent, powBitRun]
    apply ih
    cases bits.testBit fuel <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    · rw [Nat.two_mul, pow_add, Nat.mul_mod, h]
    · rw [pow_succ, Nat.two_mul, pow_add, Nat.mul_mod (a ^ e * a ^ e) a,
        Nat.mul_mod (a ^ e) (a ^ e), h]
      simp only [Nat.mul_mod, Nat.mod_mod]

theorem powBitCheckpoint (a m e r e' r' bits fuel : Nat)
    (previous : PowModState a m e r)
    (check : (powBitExponent bits fuel e == e') && (powBitRun a m bits fuel r == r') = true) :
    PowModState a m e' r' := by
  have h : powBitExponent bits fuel e = e' ∧ powBitRun a m bits fuel r = r' := by
    simpa using check
  constructor
  rw [← h.1, powBitRun_eq a m bits fuel e r previous.eq, h.2]

end PrimeFactorUnimodality
