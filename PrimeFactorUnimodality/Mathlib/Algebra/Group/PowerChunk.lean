/-
Copyright (c) 2026 kimihiro64. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kimihiro64
-/
import Mathlib.Algebra.Group.Monoid
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Bounded replay chunks for large powers

`powChunkMSB` evaluates a fixed-width natural-number chunk from most
significant bit to least significant bit. Its specification lets generated
certificates split a large modular power into independently cached, bounded
kernel computations without constructing enormous bit-list syntax trees.
-/

/-- A type-valued wrapper keeps very large checked equalities available to
downstream modules without registering them as premise-selection theorems. -/
structure PowerCertificate {M : Type*} [Monoid M]
    (value base : M) (exponent : ℕ) : Type where
  certifies : value = base ^ exponent

/-- Continue binary exponentiation through `width` low bits of `bits`, reading
them from most significant to least significant. -/
def powChunkMSB {M : Type*} [Monoid M] : ℕ → ℕ → M → M → M
  | 0, _, acc, _ => acc
  | width + 1, bits, acc, base =>
      let prior := powChunkMSB width (bits / 2) acc base
      prior * prior * if bits % 2 = 1 then base else 1

/-- A bounded binary chunk appends its fixed-width bits to the exponent already
represented by the accumulator. -/
theorem powChunkMSB_spec {M : Type*} [Monoid M] (width bits : ℕ)
    (hbits : bits < 2 ^ width) (base : M) (e : ℕ) :
    powChunkMSB width bits (base ^ e) base =
      base ^ (e * 2 ^ width + bits) := by
  induction width generalizing bits e with
  | zero =>
      have : bits = 0 := by simpa using hbits
      subst bits
      simp [powChunkMSB]
  | succ width ih =>
      rw [powChunkMSB]
      have hdiv : bits / 2 < 2 ^ width := by
        rw [pow_succ] at hbits
        omega
      rw [ih (bits / 2) hdiv e]
      have hmod : bits % 2 = 0 ∨ bits % 2 = 1 := Nat.mod_two_eq_zero_or_one bits
      rcases hmod with hmod | hmod
      · have hne : bits % 2 ≠ 1 := by omega
        simp only [hne, ite_false, mul_one]
        rw [← pow_add]
        congr 1
        rw [pow_succ]
        have hdecomp := bits.mod_add_div 2
        ring_nf
        omega
      · simp only [hmod, ite_true]
        rw [← pow_add, ← pow_succ]
        congr 1
        rw [pow_succ]
        have hdecomp := bits.mod_add_div 2
        ring_nf
        omega

theorem nat_mod_two_mul (n p : ℕ) :
    n % (2 * p) = 2 * ((n / 2) % p) + n % 2 := by
  have hdecomp := (n % (2 * p)).mod_add_div 2
  have hdiv := Nat.mod_mul_right_div_self n 2 p
  have hrem : n % (2 * p) % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (dvd_mul_right 2 p)
  omega

/-- The unconditional specification: high bits outside the declared width are
discarded. Generated chunks use this form to avoid large bound-proof terms. -/
theorem powChunkMSB_spec_mod {M : Type*} [Monoid M] (width bits : ℕ)
    (base : M) (e : ℕ) :
    powChunkMSB width bits (base ^ e) base =
      base ^ (e * 2 ^ width + bits % (2 ^ width)) := by
  induction width generalizing bits e with
  | zero => simp [powChunkMSB, Nat.mod_one]
  | succ width ih =>
      rw [powChunkMSB, ih]
      have hmod : bits % 2 = 0 ∨ bits % 2 = 1 := Nat.mod_two_eq_zero_or_one bits
      rcases hmod with hmod | hmod
      · have hne : bits % 2 ≠ 1 := by omega
        simp only [hne, ite_false, mul_one]
        rw [← pow_add]
        congr 1
        rw [pow_succ]
        have hcombine := nat_mod_two_mul bits (2 ^ width)
        have hcombine' : bits % (2 ^ width * 2) =
            2 * ((bits / 2) % (2 ^ width)) + bits % 2 := by
          simpa [mul_comm] using hcombine
        ring_nf
        omega
      · simp only [hmod, ite_true]
        rw [← pow_add, ← pow_succ]
        congr 1
        rw [pow_succ]
        have hcombine := nat_mod_two_mul bits (2 ^ width)
        have hcombine' : bits % (2 ^ width * 2) =
            2 * ((bits / 2) % (2 ^ width)) + bits % 2 := by
          simpa [mul_comm] using hcombine
        ring_nf
        omega

universe u

/-- A chain of independently checked power chunks.  Unlike materializing a
new equality after every chunk, this indexed trace keeps each generated file
small and delays the semantic composition to one generic induction. -/
inductive PowerTrace {M : Type u} [Monoid M] (base : M) : M → ℕ → Type (u + 1)
  | nil : PowerTrace base 1 0
  | step {before : M} {exponent : ℕ}
      (prior : PowerTrace base before exponent)
      (width bits : ℕ) (after : M)
      (bits_lt : bits < 2 ^ width)
      (checked : powChunkMSB width bits before base = after) :
      PowerTrace base after (exponent * 2 ^ width + bits)

/-- Every checked trace has the binary-power meaning recorded in its indices. -/
theorem PowerTrace.certifies {M : Type*} [Monoid M] {base value : M}
    {exponent : ℕ} (trace : PowerTrace base value exponent) :
    value = base ^ exponent := by
  induction trace with
  | nil => simp
  | step prior width bits after bits_lt checked ih =>
      rw [← checked, ih, powChunkMSB_spec width bits bits_lt]

/-- A faster chunk evaluator built from Mathlib's binary-power implementation.
It performs two bounded powers, but avoids the large recursive reduction term
created by `powChunkMSB`. -/
def powChunkHorner {M : Type*} [Monoid M] (width bits : ℕ) (acc base : M) : M :=
  npowBinRecAuto (2 ^ width) acc * npowBinRecAuto bits base

theorem npowBinRecAuto_eq_pow {M : Type*} [Monoid M] (n : ℕ) (x : M) :
    npowBinRecAuto n x = x ^ n := by
  induction n with
  | zero => simp only [npowBinRec_zero, pow_zero]
  | succ n ih =>
      rw [show npowBinRecAuto (n + 1) x = npowBinRecAuto n x * x by
        exact npowBinRec_succ n x, ih, pow_succ]

/-- Horner chunks have the same exponent-appending semantics as the direct bit
evaluator. -/
theorem powChunkHorner_spec {M : Type*} [Monoid M] (width bits : ℕ)
    (base : M) (e : ℕ) :
    powChunkHorner width bits (base ^ e) base =
      base ^ (e * 2 ^ width + bits) := by
  unfold powChunkHorner
  rw [npowBinRecAuto_eq_pow, npowBinRecAuto_eq_pow, ← pow_mul, ← pow_add]

/-- A semantic chunk chain using the compact binary-power evaluator.  This
avoids the very large recursive reduction terms produced by `powChunkMSB` on
large modular residues while retaining the same kernel-checked meaning. -/
inductive PowerHornerTrace {M : Type u} [Monoid M] (base : M) : M → ℕ → Type (u + 1)
  | nil : PowerHornerTrace base 1 0
  | step {before : M} {exponent : ℕ}
      (prior : PowerHornerTrace base before exponent)
      (width bits : ℕ) (after : M)
      (checked : powChunkHorner width bits before base = after) :
      PowerHornerTrace base after (exponent * 2 ^ width + bits)

/-- Every Horner trace certifies its accumulated power. -/
theorem PowerHornerTrace.certifies {M : Type*} [Monoid M] {base value : M}
    {exponent : ℕ} (trace : PowerHornerTrace base value exponent) :
    value = base ^ exponent := by
  induction trace with
  | nil => simp
  | step prior width bits after checked ih =>
      rw [← checked, ih, powChunkHorner_spec]
