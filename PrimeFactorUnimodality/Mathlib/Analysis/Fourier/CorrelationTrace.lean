/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixDFTError

/-! # Shared rounded evaluation of a finite sum of cyclic correlations

Each pair of columns has two forward traces. Their reversed-index products
are accumulated before one inverse trace. Validity covers every input and
trace, approximate-factor cap and accumulation error, without asserting the
desired correlation enclosure as a premise.
-/

open Finset

namespace Fourier

noncomputable section

/-- Shared input columns, forward transforms, accumulated products and one inverse transform. -/
structure CorrelationTrace (ι : Type*) (n : ℕ) where
  leftInput : ι → Vector ℂ (2 ^ n)
  rightInput : ι → Vector ℂ (2 ^ n)
  left : ι → RadixTrace n
  right : ι → RadixTrace n
  products : Vector ℂ (2 ^ n)
  inverse : RadixTrace n
  leftCap : ι → ℝ
  rightCap : ι → ℝ
  rounding : ℝ

namespace CorrelationTrace

variable {ι : Type*} {n : ℕ}

/-- Interpret a positive-phase forward trace with the mathematical DFT indexing. -/
def leftDFT (t : CorrelationTrace ι n) (i : ι) (l : ZMod (2 ^ n)) : ℂ :=
  (t.left i).values[(-l).val]'(ZMod.val_lt (-l))

/-- Interpret the second forward trace with the same DFT convention. -/
def rightDFT (t : CorrelationTrace ι n) (i : ι) (l : ZMod (2 ^ n)) : ℂ :=
  (t.right i).values[(-l).val]'(ZMod.val_lt (-l))

/-- Left forward error includes every coefficient-input enclosure. -/
def leftError (t : CorrelationTrace ι n) (α : ι → ZMod (2 ^ n) → ℝ) (i : ι) : ℝ :=
  (∑ l : ZMod (2 ^ n), α i l) + (t.left i).error

/-- Right forward error includes every column-input enclosure. -/
def rightError (t : CorrelationTrace ι n) (β : ι → ZMod (2 ^ n) → ℝ) (i : ι) : ℝ :=
  (∑ l : ZMod (2 ^ n), β i l) + (t.right i).error

/-- Error after summing all rounded forward-transform products. -/
def productError (t : CorrelationTrace ι n) (s : Finset ι)
    (α β : ι → ZMod (2 ^ n) → ℝ) : ℝ :=
  (∑ i ∈ s, (t.leftError α i * (t.rightCap i + t.rightError β i) +
    t.leftCap i * t.rightError β i)) + t.rounding

/-- Uniform output error after the one normalized inverse transform. -/
def error (t : CorrelationTrace ι n) (s : Finset ι)
    (α β : ι → ZMod (2 ^ n) → ℝ) : ℝ :=
  t.productError s α β + t.inverse.error / (2 ^ n : ℕ)

/-- Exact normalization of the stored inverse output; any later rounding is separate. -/
def value (t : CorrelationTrace ι n) (j : ZMod (2 ^ n)) : ℂ :=
  ((2 ^ n : ℕ) : ℂ)⁻¹ * t.inverse.values[j.val]'(ZMod.val_lt j)

/-- Complete coverage of forward inputs, arithmetic and inverse computation. -/
structure Valid (t : CorrelationTrace ι n) (s : Finset ι)
    (a b : ι → ZMod (2 ^ n) → ℂ) (α β : ι → ZMod (2 ^ n) → ℝ) : Prop where
  left_valid : ∀ i ∈ s,
    (t.left i).Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) (t.leftInput i)
  right_valid : ∀ i ∈ s,
    (t.right i).Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) (t.rightInput i)
  left_input : ∀ i ∈ s, ∀ l : ZMod (2 ^ n),
    ‖a i l - (t.leftInput i)[l.val]'(ZMod.val_lt l)‖ ≤ α i l
  right_input : ∀ i ∈ s, ∀ l : ZMod (2 ^ n),
    ‖b i l - (t.rightInput i)[l.val]'(ZMod.val_lt l)‖ ≤ β i l
  left_cap : ∀ i ∈ s, ∀ l, ‖t.leftDFT i l‖ ≤ t.leftCap i
  right_cap : ∀ i ∈ s, ∀ l, ‖t.rightDFT i l‖ ≤ t.rightCap i
  products_valid : ∀ l : ZMod (2 ^ n),
    ‖(∑ i ∈ s, t.leftDFT i (-l) * t.rightDFT i l) -
      t.products[l.val]'(ZMod.val_lt l)‖ ≤ t.rounding
  inverse_valid : t.inverse.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) t.products

/-- All exact forward products are enclosed by the shared rounded spectrum. -/
theorem Valid.norm_spectrum_sub_le {t : CorrelationTrace ι n} {s : Finset ι}
    {a b : ι → ZMod (2 ^ n) → ℂ} {α β : ι → ZMod (2 ^ n) → ℝ}
    (ht : t.Valid s a b α β) (l : ZMod (2 ^ n)) :
    ‖(∑ i ∈ s, ZMod.dft (a i) (-l) * ZMod.dft (b i) l) -
      t.products[l.val]'(ZMod.val_lt l)‖ ≤ t.productError s α β := by
  exact Complex.norm_sum_mul_sub_rounded_le s
    (fun i hi => (ht.left_valid i hi).norm_dft_sub_le (ht.left_input i hi) (-l))
    (fun i hi => (ht.right_valid i hi).norm_dft_sub_le (ht.right_input i hi) l)
    (fun i hi => ht.left_cap i hi (-l)) (fun i hi => ht.right_cap i hi l)
    (ht.products_valid l)

/-- Two forward transforms per column and one inverse enclose the exact correlation sum. -/
theorem Valid.norm_sum_correlation_sub_le {t : CorrelationTrace ι n} {s : Finset ι}
    {a b : ι → ZMod (2 ^ n) → ℂ} {α β : ι → ZMod (2 ^ n) → ℝ}
    (ht : t.Valid s a b α β) (j : ZMod (2 ^ n)) :
    ‖(∑ i ∈ s, ZMod.cyclicCorrelation (a i) (b i) j) - t.value j‖ ≤ t.error s α β := by
  have he : (∑ i ∈ s, ZMod.cyclicCorrelation (a i) (b i) j) =
      ((2 ^ n : ℕ) : ℂ)⁻¹ * ZMod.dft
        (fun l => ∑ i ∈ s, ZMod.dft (a i) (-l) * ZMod.dft (b i) l) (-j) := by
    simp_rw [ZMod.cyclicCorrelation_eq_inv_dft]
    simp only [ZMod.dft_apply, smul_eq_mul, mul_sum]
    rw [sum_comm]
  rw [he]
  exact ht.inverse_valid.norm_inv_dft_sub_le ht.norm_spectrum_sub_le j

end CorrelationTrace

end

end Fourier
