/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Fourier.ZMod

/-! # Finite cyclic convolution and its Fourier evaluation

Convolution is exactly an inverse DFT of pointwise products. Correlation
uses a reversed first input, so its positive shift is not confused with
the subtraction in the convolution convention.
-/

open Finset

namespace ZMod

noncomputable section

variable {N : ℕ} [NeZero N]

/-- Cyclic convolution with the counting-measure normalization. -/
def cyclicConvolution (a b : ZMod N → ℂ) (j : ZMod N) : ℂ :=
  ∑ l : ZMod N, a l * b (j - l)

/-- Circular positive-shift correlation, without conjugating its first input. -/
def cyclicCorrelation (a b : ZMod N → ℂ) (j : ZMod N) : ℂ :=
  ∑ l : ZMod N, a l * b (j + l)

/-- The DFT of cyclic convolution is the pointwise product of the two DFTs. -/
theorem dft_cyclicConvolution (a b : ZMod N → ℂ) (k : ZMod N) :
    dft (cyclicConvolution a b) k = dft a k * dft b k := by
  simp only [dft_apply, cyclicConvolution, smul_eq_mul]
  rw [sum_mul]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← Equiv.sum_comp (Equiv.addRight j)
    (fun l : ZMod N => stdAddChar (-(l * k)) * (a j * b (l - j)))]
  simp only [Equiv.coe_addRight, add_sub_cancel_right, add_mul, neg_add,
    AddChar.map_add_eq_mul]
  apply sum_congr rfl
  intro l hl
  ring

/-- A shared pair of forward transforms and one inverse transform give all convolution outputs. -/
theorem cyclicConvolution_eq_inv_dft (a b : ZMod N → ℂ) (j : ZMod N) :
    cyclicConvolution a b j = (N : ℂ)⁻¹ *
      dft (fun k => dft a k * dft b k) (-j) := by
  have he : (fun k => dft a k * dft b k) = dft (cyclicConvolution a b) :=
    funext fun k => (dft_cyclicConvolution a b k).symm
  rw [he, dft_dft]
  simp only [neg_neg, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_mul]

/-- Positive-shift correlation is convolution with its first input reversed. -/
theorem cyclicCorrelation_eq_convolution (a b : ZMod N → ℂ) (j : ZMod N) :
    cyclicCorrelation a b j = cyclicConvolution (fun l => a (-l)) b j := by
  unfold cyclicCorrelation cyclicConvolution
  rw [← Equiv.sum_comp (Equiv.neg (ZMod N)) (fun l => a (-l) * b (j - l))]
  simp

/-- Correlation retains the reversed frequency index on its first transform. -/
theorem cyclicCorrelation_eq_inv_dft (a b : ZMod N → ℂ) (j : ZMod N) :
    cyclicCorrelation a b j = (N : ℂ)⁻¹ *
      dft (fun k => dft a (-k) * dft b k) (-j) := by
  rw [cyclicCorrelation_eq_convolution, cyclicConvolution_eq_inv_dft, dft_comp_neg]

/-- All finite coefficients colliding in a grid bucket are added, not discarded. -/
def bucketCoefficients {ι : Type*} (s : Finset ι) (bin : ι → ZMod N) (a : ι → ℂ)
    (l : ZMod N) : ℂ := ∑ i ∈ s.filter (fun i => bin i = l), a i

/-- A weighted sum over many shifted inputs is one correlation of their shared buckets. -/
theorem sum_mul_shift_eq_cyclicCorrelation {ι : Type*} (s : Finset ι)
    (bin : ι → ZMod N) (a : ι → ℂ) (b : ZMod N → ℂ) (j : ZMod N) :
    (∑ i ∈ s, a i * b (j + bin i)) = cyclicCorrelation (bucketCoefficients s bin a) b j := by
  have he := sum_fiberwise_of_maps_to (g := bin) (s := s) (t := univ)
    (fun i _ => mem_univ (bin i)) (fun i => a i * b (j + bin i))
  rw [← he, cyclicCorrelation]
  apply sum_congr rfl
  intro l hl
  rw [bucketCoefficients, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

end

end ZMod
