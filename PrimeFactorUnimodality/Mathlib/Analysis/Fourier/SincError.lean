/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.SincSampling

/-! # Sampling error without a band-limit assumption

The central Fourier cell gives the sinc series after aliasing. The error
against the original function consists of the omitted Fourier tail and the
integrated aliases. A uniform alias bound suffices on this unit-length cell.
-/

open MeasureTheory Filter Asymptotics
open scoped FourierTransform

namespace Fourier

noncomputable section

/-- Power decay with exponent greater than one gives absolute convergence of time samples. -/
theorem summable_norm_int_of_rpow_decay {f : ℝ → ℂ} {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (fun t => |t| ^ (-b))) :
    Summable (fun n : ℤ => ‖f n‖) :=
  summable_of_isBigO (Real.summable_abs_int_rpow hb)
    (hf.norm_left.comp_tendsto Int.tendsto_coe_cofinite)

/-- An absolutely summable sample sequence has a continuous Fourier series. -/
theorem continuous_samplingSeries {f : ℤ → ℂ} (hf : Summable (fun n => ‖f n‖)) :
    Continuous (fun x => ∑' n : ℤ, samplingPhase (-(n : ℝ)) x * f n) := by
  apply continuous_tsum (fun n => (continuous_samplingPhase _).mul continuous_const) hf
  intro n x
  simp

/-- Multiplication by an inverse Fourier phase preserves integrability and the absolute integral. -/
theorem integrable_samplingPhase_mul {f : ℝ → ℂ} (hf : Integrable f) (t : ℝ) :
    Integrable (fun x => samplingPhase t x * f x) := by
  apply hf.norm.mono'
    ((continuous_samplingPhase t).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with x
  simp

/-- The inverse integral outside the central unit cell is bounded by the actual Fourier tail. -/
theorem norm_sub_inverse_cell_le {f : ℝ → ℂ} (hc : Continuous f)
    (hf : Integrable f) (hF : Integrable (𝓕 f)) (t : ℝ) :
    ‖f t - ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), samplingPhase t x * 𝓕 f x‖ ≤
      ∫ x in (Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ))ᶜ, ‖𝓕 f x‖ := by
  have hi := integrable_samplingPhase_mul hF t
  have hinv : f t = ∫ x : ℝ, samplingPhase t x * 𝓕 f x := by
    rw [← hf.fourierInv_fourier_eq hF hc.continuousAt, Real.fourierInv_eq']
    simp only [samplingPhase, RCLike.inner_apply, conj_trivial, smul_eq_mul, mul_assoc]
  rw [hinv, intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2),
    ← setIntegral_compl measurableSet_Ioc hi]
  simpa only [norm_mul, norm_samplingPhase, one_mul] using
    norm_integral_le_integral_norm (fun x => samplingPhase t x * 𝓕 f x)

/-- The full sinc series has an explicit alias-plus-tail error against the genuine function. -/
theorem norm_sub_sincSeries_le {f : ℝ → ℂ} (hc : Continuous f)
    (hi : Integrable f) (hFi : Integrable (𝓕 f)) {b : ℝ} (hb : 1 < b)
    (hd : f =O[cocompact ℝ] (fun t => |t| ^ (-b)))
    (hFs : ∀ x : ℝ, Summable (fun n : ℤ => 𝓕 f (x + n))) {η : ℝ}
    (hAlias : ∀ x ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      ‖(∑' n : ℤ, 𝓕 f (x + n)) - 𝓕 f x‖ ≤ η) (t : ℝ) :
    ‖f t - ∑' n : ℤ, f n * (Real.sinc (Real.pi * (t - n)) : ℂ)‖ ≤
      (∫ x in (Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ))ᶜ, ‖𝓕 f x‖) + η := by
  have hs := summable_norm_int_of_rpow_decay hb hd
  have hFc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hc₁ : Continuous (fun x => samplingPhase t x * 𝓕 f x) :=
    (continuous_samplingPhase t).mul hFc
  have hc₂ : Continuous (fun x => samplingPhase t x *
      ∑' n : ℤ, samplingPhase (-(n : ℝ)) x * f n) :=
    (continuous_samplingPhase t).mul (continuous_samplingSeries hs)
  have he : ‖(∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), samplingPhase t x * 𝓕 f x) -
      (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        samplingPhase t x * ∑' n : ℤ, samplingPhase (-(n : ℝ)) x * f n)‖ ≤ η := by
    rw [← intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₂.intervalIntegrable _ _)]
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (C := η) (f := fun x =>
        samplingPhase t x * 𝓕 f x -
          samplingPhase t x * ∑' n : ℤ, samplingPhase (-(n : ℝ)) x * f n) (by
        intro x hx
        rw [← mul_sub, norm_mul, norm_samplingPhase, one_mul,
          ← tsum_fourier_shift_eq_samples hc hb hd x (hFs x), norm_sub_rev]
        apply hAlias x
        rw [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hx
        exact ⟨hx.1.le, hx.2⟩)
    norm_num at he ⊢
    exact he
  rw [tsum_sinc_eq_integral_series hs]
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), samplingPhase t x * 𝓕 f x) _).trans
      (add_le_add (norm_sub_inverse_cell_le hc hi hFi t) he)

end

end Fourier
