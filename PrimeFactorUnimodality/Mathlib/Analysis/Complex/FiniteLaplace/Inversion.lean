/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Fourier.Inversion
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Bounds
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Continuity
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.RemainderSource
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Cauchy

/-! # Absolute inversion of the pole-subtracted finite Laplace transform

The endpoint conditions give quadratic decay on every positive vertical
line. Both the damped time-domain source and its Fourier transform are
integrable, so Mathlib's Fourier inversion applies at every real point.
The Fourier/Laplace kernel calculation also occurs in
`laplaceTransformBilateral_eq_fourier` in the Apache-2.0 repository
`kimihiro64/PrimeNumberTheoremAnd`, revision
`f6147e7572ab3abe5428101bc0b13627bcb005df`. We use Mathlib directly and do
not import the sibling's truncated-inversion or explicit-formula modules.
-/

namespace Complex

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

/-- Fourier transform of the damped, continuous remainder source, with exact normalization. -/
theorem fourier_exp_mul_finiteLaplaceRemainderSource {f : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (hfd : f d = 0)
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    𝓕 (fun u : ℝ => exp (-s * (u : ℂ)) * finiteLaplaceRemainderSource f d u) t =
      finiteLaplace f d (s + ((2 * Real.pi * t : ℝ) : ℂ) * I) -
        f 0 / (s + ((2 * Real.pi * t : ℝ) : ℂ) * I) := by
  rw [Real.fourier_eq']
  have heq : (fun u : ℝ => exp (((-2 * Real.pi * (u * t) : ℝ) : ℂ) * I) •
      (exp (-s * (u : ℂ)) * finiteLaplaceRemainderSource f d u)) =
      fun u : ℝ => exp (-(s + ((2 * Real.pi * t : ℝ) : ℂ) * I) * (u : ℂ)) *
        finiteLaplaceRemainderSource f d u := by
    funext u
    rw [smul_eq_mul, ← mul_assoc, ← exp_add]
    congr 2
    push_cast
    ring
  simp only [Real.inner_apply]
  rw [heq]
  exact integral_exp_mul_finiteLaplaceRemainderSource hd hf hfd (by simpa using hs)

/-- Quadratic decay makes the pole-subtracted transform absolutely integrable in height. -/
theorem integrable_finiteLaplace_sub_pole_vertical {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ => finiteLaplace f d (s + (t : ℂ) * I) -
      f 0 / (s + (t : ℂ) * I)) := by
  have hne (t : ℝ) : s + (t : ℂ) * I ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero,
      zero_mul, sub_zero, add_zero, zero_re] at hre
    exact hs.ne' hre
  have hF : Continuous (fun t : ℝ => finiteLaplace f d (s + (t : ℂ) * I)) := by
    simpa [Function.comp_def] using (continuous_finiteLaplace_vertical hd hf s).comp
      (continuous_neg : Continuous (fun t : ℝ => -t))
  have hcont : Continuous (fun t : ℝ => finiteLaplace f d (s + (t : ℂ) * I) -
      f 0 / (s + (t : ℂ) * I)) := hF.sub (continuous_const.div (by fun_prop) hne)
  apply ((integrable_inv_sq_norm_vertical hs.ne').const_mul (M / s.re)).mono'
    hcont.aestronglyMeasurable
  filter_upwards with t
  have h := norm_finiteLaplace_sub_pole_le_div_re hd hM hf hg hh hfg hgh hfd hg₀ hgd
    hbound (s := s + (t : ℂ) * I) (by simpa using hs)
  simpa [div_mul_eq_div_div, div_eq_mul_inv, mul_assoc, mul_comm] using h

/-- Absolute Fourier inversion of the remainder, with no regularity of a zero extension assumed. -/
theorem fourierInv_finiteLaplace_sub_pole {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M) {s : ℂ} (hs : 0 < s.re) (x : ℝ) :
    𝓕⁻ (fun t : ℝ => finiteLaplace f d (s + ((2 * Real.pi * t : ℝ) : ℂ) * I) -
      f 0 / (s + ((2 * Real.pi * t : ℝ) : ℂ) * I)) x =
      exp (-s * (x : ℂ)) * finiteLaplaceRemainderSource f d x := by
  have htransform := funext (fourier_exp_mul_finiteLaplaceRemainderSource hd hf hfd hs)
  have hsource := integrable_exp_mul_finiteLaplaceRemainderSource hd hf hfd hs
  have hvertical := integrable_finiteLaplace_sub_pole_vertical hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hs
  have hfourier : Integrable (𝓕 (fun u : ℝ =>
      exp (-s * (u : ℂ)) * finiteLaplaceRemainderSource f d u)) := by
    rw [htransform]
    exact hvertical.comp_mul_left' (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  rw [← htransform]
  exact hsource.fourierInv_fourier_eq hfourier
    (((by fun_prop : Continuous (fun u : ℝ => exp (-s * (u : ℂ))))).mul
      (continuous_finiteLaplaceRemainderSource hd hf)).continuousAt

/-- The absolutely convergent inverse Laplace integral, with angular-frequency normalization. -/
theorem integral_finiteLaplace_sub_pole_vertical {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M) {s : ℂ} (hs : 0 < s.re) (x : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ t : ℝ, exp ((t : ℂ) * I * (x : ℂ)) *
        (finiteLaplace f d (s + (t : ℂ) * I) - f 0 / (s + (t : ℂ) * I))) =
      exp (-s * (x : ℂ)) * finiteLaplaceRemainderSource f d x := by
  have hinv := fourierInv_finiteLaplace_sub_pole hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hs x
  rw [Real.fourierInv_eq'] at hinv
  simp only [Real.inner_apply, smul_eq_mul] at hinv
  let F : ℝ → ℂ := fun t => exp ((t : ℂ) * I * (x : ℂ)) *
    (finiteLaplace f d (s + (t : ℂ) * I) - f 0 / (s + (t : ℂ) * I))
  have heq : (∫ t : ℝ, exp (((2 * Real.pi * (t * x) : ℝ) : ℂ) * I) *
      (finiteLaplace f d (s + ((2 * Real.pi * t : ℝ) : ℂ) * I) -
        f 0 / (s + ((2 * Real.pi * t : ℝ) : ℂ) * I))) =
      ∫ t : ℝ, F (2 * Real.pi * t) := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp [F]
    push_cast
    ring_nf
  rw [heq, Measure.integral_comp_mul_left] at hinv
  have hπ : 0 < (2 * Real.pi)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  rw [abs_of_pos hπ, Complex.real_smul, ofReal_inv, ofReal_mul, ofReal_ofNat] at hinv
  simpa only [one_div] using hinv

end

end Complex
