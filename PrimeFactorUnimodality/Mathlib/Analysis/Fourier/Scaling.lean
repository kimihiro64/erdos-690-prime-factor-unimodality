/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Real dilation of the complex Fourier transform

The Lebesgue change of variables supplies the absolute inverse scale. No
integrability premise is needed for this identity of total Bochner integrals.
-/

open MeasureTheory
open scoped FourierTransform

namespace Real

/-- Real dilation rescales frequency and multiplies the transform by the inverse absolute scale. -/
theorem fourier_comp_mul_left (f : ℝ → ℂ) {B : ℝ} (hB : B ≠ 0) (u : ℝ) :
    𝓕 (fun x : ℝ => f (B * x)) u = (|B|⁻¹ : ℝ) • 𝓕 f (u / B) := by
  rw [fourier_real_eq_integral_exp_smul, fourier_real_eq_integral_exp_smul]
  have he (x : ℝ) : -2 * Real.pi * (B * x) * (u / B) = -2 * Real.pi * x * u := by
    field_simp
  simpa only [he, abs_inv] using Measure.integral_comp_mul_left
    (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * (u / B) : ℝ) * Complex.I) • f x) B

end Real
