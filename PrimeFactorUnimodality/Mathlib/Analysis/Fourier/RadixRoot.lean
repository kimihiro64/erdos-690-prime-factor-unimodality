/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.IntegerGrid

/-! # Canonical roots shared across a radix tree

Every node at the same depth uses the same root and twiddle table.
Squaring moves to the next smaller grid, including the one-point grid.
-/

namespace Fourier

noncomputable section

open Complex ZMod

/-- The exact positive-phase root for a power-of-two grid. -/
def radixRoot (n : ℕ) : ℂ := stdAddChar (1 : ZMod (2 ^ n))

/-- Canonical roots have unit norm. -/
theorem norm_radixRoot (n : ℕ) : ‖radixRoot n‖ = 1 := by
  simp [radixRoot, stdAddChar_apply]

/-- Every twiddle is one bounded real-angle exponential. -/
theorem radixRoot_pow (n k : ℕ) :
    radixRoot n ^ k = exp (I * ((2 * Real.pi * k / (2 ^ n) : ℝ) : ℂ)) := by
  rw [radixRoot, stdAddChar_one_pow]
  have h := stdAddChar_coe (N := 2 ^ n) (k : ℤ)
  push_cast at h
  rw [h]
  congr 1
  push_cast
  ring

/-- The two children can reuse the already-checked table of the smaller grid. -/
theorem radixRoot_succ_sq (n : ℕ) : radixRoot (n + 1) ^ 2 = radixRoot n := by
  rw [radixRoot_pow]
  have h := radixRoot_pow n 1
  simp only [pow_one, Nat.cast_one, mul_one] at h
  rw [h]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

end

end Fourier
