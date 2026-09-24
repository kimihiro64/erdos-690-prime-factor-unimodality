/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.IntegerGrid

/-! # Regrouping summable Fourier series into a finite transform

All integer frequencies in each residue class are retained. At a rational
grid point their characters agree, so the full series is exactly a finite
DFT of the residue sums. Representatives may be signed or centered.
-/

open Finset

namespace ZMod

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The complete sum of coefficients in one residue class. -/
def residueTsum (a : ℤ → ℂ) (j : ZMod N) : ℂ :=
  ∑' l : ℤ, a ((j.val : ℤ) + (N : ℤ) * l)

/-- A summable integer series is the finite sum of its full residue-class sums. -/
theorem tsum_eq_sum_residueTsum {a : ℤ → ℂ} (ha : Summable a) :
    (∑' n : ℤ, a n) = ∑ j : ZMod N, residueTsum a j := by
  let e : Fin N × ℤ ≃ ℤ :=
    (Equiv.prodComm (Fin N) ℤ).trans (Int.divModEquiv N).symm
  have hs : Summable (fun p : Fin N × ℤ => a (e p)) := e.summable_iff.mpr ha
  calc
    _ = ∑' p : Fin N × ℤ, a (e p) := (e.tsum_eq a).symm
    _ = ∑' j : Fin N, ∑' l : ℤ, a (e (j, l)) := hs.tsum_prod
    _ = ∑ j : Fin N, ∑' l : ℤ, a ((j.val : ℤ) + (N : ℤ) * l) := by
      rw [tsum_fintype]
      simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Int.divModEquiv_symm_apply,
        Prod.swap_prod_mk, mul_comm, add_comm]
    _ = _ := by
      rw [← Equiv.sum_comp (finEquiv N).toEquiv]
      simp only [residueTsum, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, val_finEquiv]

/-- Any integer representative gives the identical residue sum. -/
theorem residueTsum_eq_of_intCast (a : ℤ → ℂ) (q : ℤ) (j : ZMod N)
    (hq : (q : ZMod N) = j) :
    residueTsum a j = ∑' l : ℤ, a (q + (N : ℤ) * l) := by
  obtain ⟨r, rfl⟩ := (intCast_eq_iff N q j).mp hq
  have he := (Equiv.addLeft r).tsum_eq (fun l : ℤ => a ((j.val : ℤ) + (N : ℤ) * l))
  simpa only [residueTsum, Equiv.coe_addLeft, mul_add, add_assoc] using he.symm

/-- Multiplication by the Fourier character preserves summability. -/
theorem summable_mul_stdAddChar {a : ℤ → ℂ} (ha : Summable a) (k : ZMod N) :
    Summable (fun n : ℤ => a n * stdAddChar ((n : ZMod N) * k)) := by
  apply ha.norm.of_norm_bounded
  intro n
  simp only [norm_mul, stdAddChar_apply, Circle.norm_coe, mul_one, le_refl]

/-- The exact positive-phase series is the DFT of all residue sums at the negative index. -/
theorem tsum_mul_stdAddChar_eq_dft_neg {a : ℤ → ℂ} (ha : Summable a) (k : ZMod N) :
    (∑' n : ℤ, a n * stdAddChar ((n : ZMod N) * k)) = dft (residueTsum a) (-k) := by
  rw [tsum_eq_sum_residueTsum (N := N) (summable_mul_stdAddChar ha k), dft_apply]
  apply sum_congr rfl
  intro j hj
  simp only [residueTsum, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    natCast_self, zero_mul, add_zero, natCast_zmod_val, mul_neg, neg_neg,
    smul_eq_mul, tsum_mul_right]
  rw [mul_comm]

/-- The continuous Fourier monomial at an integer grid point is the discrete character. -/
theorem fourier_grid_eq_stdAddChar (n k : ℤ) :
    fourier n (((k : ℝ) / N : ℝ) : UnitAddCircle) =
      stdAddChar ((n : ZMod N) * (k : ZMod N)) := by
  rw [fourier_coe_apply, ← Int.cast_mul, stdAddChar_coe]
  push_cast
  congr 1
  ring

/-- Discrete Poisson regrouping of a genuinely convergent continuous Fourier series. -/
theorem tsum_fourier_grid_eq_dft_neg {a : ℤ → ℂ} (ha : Summable a) (k : ℤ) :
    (∑' n : ℤ, a n * fourier n (((k : ℝ) / N : ℝ) : UnitAddCircle)) =
      dft (residueTsum a) (-(k : ZMod N)) := by
  simp only [fourier_grid_eq_stdAddChar (N := N)]
  exact tsum_mul_stdAddChar_eq_dft_neg (N := N) ha (k : ZMod N)

/-- The centered integer representative lies in the closed half-period cell over the reals. -/
theorem abs_valMinAbs_real_le_half (j : ZMod N) :
    |(j.valMinAbs : ℝ)| ≤ (N : ℝ) / 2 := by
  have hl : -(N : ℝ) < (j.valMinAbs : ℝ) * 2 := by
    exact_mod_cast j.valMinAbs_mem_Ioc.1
  have hu : (j.valMinAbs : ℝ) * 2 ≤ (N : ℝ) := by
    exact_mod_cast j.valMinAbs_mem_Ioc.2
  rw [abs_le]
  constructor <;> linarith

/-- Each output retains the sum of all input errors, since the character has unit norm. -/
theorem norm_dft_sub_le_sum {a b : ZMod N → ℂ} {ε : ZMod N → ℝ}
    (h : ∀ j, ‖a j - b j‖ ≤ ε j) (k : ZMod N) :
    ‖dft a k - dft b k‖ ≤ ∑ j : ZMod N, ε j := by
  rw [dft_apply, dft_apply, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  simpa only [smul_eq_mul, ← mul_sub, norm_mul, stdAddChar_apply,
    Circle.norm_coe, one_mul] using h j

/-- Uniform input errors grow by at most the transform length before normalization. -/
theorem norm_dft_sub_le {a b : ZMod N → ℂ} {ε : ℝ}
    (h : ∀ j, ‖a j - b j‖ ≤ ε) (k : ZMod N) :
    ‖dft a k - dft b k‖ ≤ (N : ℝ) * ε := by
  simpa only [sum_const, card_univ, ZMod.card, nsmul_eq_mul] using
    norm_dft_sub_le_sum h k

end

end ZMod
