/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixError
import PrimeFactorUnimodality.Mathlib.Data.Vector.ScatterAdd

/-! # Shared transforms of grouped moments

Sparse coefficients are accumulated once into a shared array. One checked
radix trace per Taylor order supplies every signed grid sample. The final
polynomial bound retains the error of every transformed coefficient.
-/

namespace Fourier

noncomputable section

open Complex Finset ZMod

/-- Linear sparse accumulation of all integer frequencies into their grid residues. -/
def aliasVector (n : ℕ) (B : Finset ℤ) (a : ℤ → ℂ) : Vector ℂ (2 ^ n) :=
  (Vector.replicate (2 ^ n) 0).scatterAdd (B.toList.map fun b : ℤ =>
    (⟨(b : ZMod (2 ^ n)).val, ZMod.val_lt _⟩, a b))

/-- Array accumulation implements the complete alias sum, including collisions. -/
theorem aliasVector_get (n : ℕ) (B : Finset ℤ) (a : ℤ → ℂ) (k : ZMod (2 ^ n)) :
    (aliasVector n B a)[k.val]'(ZMod.val_lt k) = aliasCoefficients B a k := by
  rw [aliasVector, Vector.scatterAdd_get _ _ ⟨k.val, ZMod.val_lt k⟩]
  simp only [Vector.getElem_replicate, zero_add, List.map_map, Function.comp_def,
    Fin.mk.injEq, (ZMod.val_injective (2 ^ n)).eq_iff]
  simp [aliasCoefficients, Finset.sum_filter]

/-- A checked trace bounds every DFT output of the stored moments. -/
theorem RadixTrace.Valid.norm_dft_alias_sub_le {n : ℕ} {t : RadixTrace n}
    {B : Finset ℤ} {a : ℤ → ℂ}
    (ht : t.Valid (stdAddChar (1 : ZMod (2 ^ n))) (aliasVector n B a))
    (k : ZMod (2 ^ n)) :
    ‖dft (aliasCoefficients B a) (-k) - t.values[k.val]'(val_lt k)‖ ≤ t.error := by
  have h := ht.norm_radixTwo_sub_le (by simp [stdAddChar_apply]) ⟨k.val, val_lt k⟩
  rw [radixTwo_eq_dft] at h
  simpa only [aliasVector_get, natCast_zmod_val] using h

/-- A shared transform family bounds the full grouped polynomial at each signed grid point. -/
theorem norm_exp_polynomial_grid_sub_traces_le (n m : ℕ) (B : Finset ℤ)
    (a : ℤ → ℕ → ℂ) (t : ℕ → RadixTrace n)
    (ht : ∀ j ∈ range m,
      (t j).Valid (stdAddChar (1 : ZMod (2 ^ n))) (aliasVector n B (fun b => a b j)))
    (k : ℤ) :
    ‖(∑ b ∈ B, exp (I * (((2 * Real.pi * k / (2 ^ n)) * b : ℝ) : ℂ)) *
        ∑ j ∈ range m, a b j * ((2 * Real.pi * k / (2 ^ n) : ℝ) : ℂ) ^ j) -
      ∑ j ∈ range m, (t j).values[(k : ZMod (2 ^ n)).val]'(val_lt _) *
        ((2 * Real.pi * k / (2 ^ n) : ℝ) : ℂ) ^ j‖ ≤
      ∑ j ∈ range m, (t j).error * |2 * Real.pi * k / (2 ^ n)| ^ j := by
  have he := sum_exp_polynomial_grid_eq (N := 2 ^ n) B a m k
  simp only [Nat.cast_pow, Nat.cast_ofNat] at he
  rw [he, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [← sub_mul, norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((ht j hj).norm_dft_alias_sub_le (k : ZMod (2 ^ n)))
    (pow_nonneg (abs_nonneg _) _)

end

end Fourier
