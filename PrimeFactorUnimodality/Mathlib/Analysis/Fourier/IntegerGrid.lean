/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Fourier.ZMod
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixTwo

/-! # Radix transforms and integer-frequency sampling grids

Integer frequencies are combined modulo the grid size, retaining all
colliding coefficients. Mathlib's additive character fixes the sign and
normalization of the transform, including negative frequencies.
-/

namespace ZMod

noncomputable section

open Finset Complex

variable {N : ℕ} [NeZero N]

/-- Powers of the unit character are the character of the natural index. -/
theorem stdAddChar_one_pow (j : ℕ) :
    stdAddChar (1 : ZMod N) ^ j = stdAddChar (j : ZMod N) := by
  simpa only [nsmul_eq_mul, mul_one] using
    (AddChar.map_nsmul_eq_pow (stdAddChar (N := N)) j 1).symm

/-- The canonical character supplies the exact root period needed by the algorithm. -/
theorem stdAddChar_one_pow_card : stdAddChar (1 : ZMod N) ^ N = 1 := by
  simp [stdAddChar_one_pow]

/-- The standard finite equivalence retains the natural index. -/
theorem val_finEquiv (i : Fin N) : (finEquiv N i).val = i.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The finite equivalence is the natural cast into the residue ring. -/
theorem finEquiv_eq_natCast (i : Fin N) : finEquiv N i = (i.val : ZMod N) := by
  rw [← val_finEquiv i, natCast_zmod_val]

/-- The positive-phase radix transform is Mathlib's DFT at the negative output index. -/
theorem radixTwo_eq_dft (n : ℕ) (a : Vector ℂ (2 ^ n)) (k : Fin (2 ^ n)) :
    (Fourier.radixTwo n (stdAddChar (1 : ZMod (2 ^ n))) a)[k.val] =
      dft (fun j : ZMod (2 ^ n) => a[j.val]'(val_lt j)) (-(k.val : ZMod (2 ^ n))) := by
  rw [Fourier.radixTwo_get n _ stdAddChar_one_pow_card, dft_apply,
    ← Equiv.sum_comp (finEquiv (2 ^ n)).toEquiv]
  apply sum_congr rfl
  intro j hj
  simp only [stdAddChar_one_pow, Nat.cast_mul, RingEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, finEquiv_eq_natCast, mul_neg, neg_neg, smul_eq_mul,
    val_natCast, Nat.mod_eq_of_lt j.isLt]
  rw [mul_comm (j.val : ZMod (2 ^ n)), mul_comm]

/-- Modulo-grid aliasing adds colliding coefficients, never discards them. -/
def aliasCoefficients (B : Finset ℤ) (a : ℤ → ℂ) (j : ZMod N) : ℂ :=
  ∑ b ∈ B.filter (fun b : ℤ => (b : ZMod N) = j), a b

/-- Aliasing preserves the exact Fourier sum at every grid index. -/
theorem dft_alias_neg (B : Finset ℤ) (a : ℤ → ℂ) (k : ZMod N) :
    dft (aliasCoefficients B a) (-k) = ∑ b ∈ B, stdAddChar ((b : ZMod N) * k) * a b := by
  rw [dft_apply]
  simp only [mul_neg, neg_neg, smul_eq_mul, aliasCoefficients, mul_sum]
  have h := sum_fiberwise_of_maps_to (g := fun b : ℤ => (b : ZMod N))
    (s := B) (t := univ) (fun b _ => mem_univ (b : ZMod N))
    (fun b => stdAddChar ((b : ZMod N) * k) * a b)
  rw [← h]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro b hb
  rw [(mem_filter.mp hb).2]

/-- The character on a signed grid index is the exact real exponential phase. -/
theorem stdAddChar_grid (b k : ℤ) :
    stdAddChar ((b : ZMod N) * (k : ZMod N)) =
      exp (I * (((2 * Real.pi * k / N) * b : ℝ) : ℂ)) := by
  rw [← Int.cast_mul, stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- An integer-frequency polynomial sampled on a uniform grid is one aliased DFT. -/
theorem sum_exp_grid_eq_dft (B : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) :
    (∑ b ∈ B, exp (I * (((2 * Real.pi * k / N) * b : ℝ) : ℂ)) * a b) =
      dft (aliasCoefficients B a) (-(k : ZMod N)) := by
  rw [dft_alias_neg]
  apply sum_congr rfl
  intro b hb
  rw [stdAddChar_grid]

/-- Reusing one transformed coefficient vector per order evaluates an entire moment polynomial. -/
theorem sum_exp_polynomial_grid_eq (B : Finset ℤ) (a : ℤ → ℕ → ℂ) (m : ℕ) (k : ℤ) :
    (∑ b ∈ B, exp (I * (((2 * Real.pi * k / N) * b : ℝ) : ℂ)) *
      ∑ j ∈ range m, a b j * ((2 * Real.pi * k / N : ℝ) : ℂ) ^ j) =
      ∑ j ∈ range m, dft (aliasCoefficients B (fun b => a b j)) (-(k : ZMod N)) *
        ((2 * Real.pi * k / N : ℝ) : ℂ) ^ j := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  simp only [← mul_assoc, ← sum_mul, sum_exp_grid_eq_dft]

end

end ZMod
