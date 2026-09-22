/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic

/-! # Real-axis monotonicity of finite Laplace transforms

A nonnegative source on a nonnegative compact interval gives a decreasing
real-axis transform. No sign condition on the real transform argument is
needed: compact support makes the comparison valid on the entire real axis.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- The real part on the real axis is the ordinary real exponential integral. -/
theorem re_finiteLaplace_ofReal {f : ℝ → ℝ} {d : ℝ}
    (hf : ContinuousOn f (uIcc 0 d)) (x : ℝ) :
    (finiteLaplace (fun u => (f u : ℂ)) d (x : ℂ)).re =
      ∫ u in (0 : ℝ)..d, Real.exp (-x * u) * f u := by
  have hi := intervalIntegrable_finiteLaplace (f := fun u => (f u : ℂ))
    (continuous_ofReal.comp_continuousOn hf) (x : ℂ)
  calc
    _ = ∫ u in (0 : ℝ)..d, (exp (-(x : ℂ) * (u : ℂ)) * (f u : ℂ)).re :=
      (intervalIntegral.intervalIntegral_re hi).symm
    _ = _ := ?_
  apply intervalIntegral.integral_congr
  intro u _
  simp [mul_re, exp_re]

/-- Nonnegative compact real sources have an antitone real-axis Laplace transform. -/
theorem antitone_re_finiteLaplace {f : ℝ → ℝ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (hf₀ : ∀ u ∈ Icc 0 d, 0 ≤ f u) :
    Antitone (fun x : ℝ => (finiteLaplace (fun u => (f u : ℂ)) d (x : ℂ)).re) := by
  intro x y hxy
  dsimp only
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  rw [re_finiteLaplace_ofReal hf', re_finiteLaplace_ofReal hf']
  have hi (v : ℝ) : IntervalIntegrable (fun u => Real.exp (-v * u) * f u) volume 0 d :=
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-v * u))).continuousOn.mul
      hf').intervalIntegrable
  exact intervalIntegral.integral_mono_on hd (hi y) (hi x) (fun u hu =>
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg hxy) hu.1)) (hf₀ u hu))

end

end Complex
