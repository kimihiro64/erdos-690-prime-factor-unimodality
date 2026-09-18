/-
Copyright (c) 2026 kimihiro64. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kimihiro64
-/
import PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerChunk

/-!
# Independently checkable power chunks

This module separates a single checked binary-power step from the recursively
nested trace used by `PowerTrace`, allowing large generated computations to be
compiled independently and assembled afterward.
-/

universe u

/-- One independently checkable binary-power chunk. -/
structure PowerStep {M : Type u} [Monoid M] (base before after : M)
    (beforeExponent width bits : ℕ) : Type (u + 1) where
  bits_lt : bits < 2 ^ width
  checked : powChunkMSB width bits before base = after

/-- An independently checked step extends a semantic certificate for its
input state. -/
theorem PowerStep.certifies {M : Type*} [Monoid M]
    {base before after : M} {beforeExponent width bits : ℕ}
    (step : PowerStep base before after beforeExponent width bits)
    (prior : before = base ^ beforeExponent) :
    after = base ^ (beforeExponent * 2 ^ width + bits) := by
  rw [← step.checked, prior, powChunkMSB_spec width bits step.bits_lt]
