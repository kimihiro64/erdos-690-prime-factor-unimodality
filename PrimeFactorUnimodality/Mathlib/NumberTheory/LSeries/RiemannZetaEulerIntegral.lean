/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerDecay
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogDerivDecay

/-! # The complete horizontal integral of the zeta logarithmic derivative

The Euler logarithm is the primitive fixed by its vanishing value at
horizontal infinity. The absolute majorant and Mathlib's improper FTC
therefore identify the complete integral, with no discarded endpoint.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

/-- The actual Euler logarithm vanishes at horizontal infinity, at every real height. -/
theorem tendsto_riemannZetaEulerLog_horizontal_atTop (T : ℝ) :
    Tendsto (fun x : ℝ => riemannZetaEulerLog ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  have hdec : Tendsto (fun x : ℝ => (2 : ℝ) ^ (2 - x) * Real.log ‖riemannZeta (2 : ℂ)‖)
      atTop (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => 2 - x) atTop atBot := by
      apply tendsto_atBot.mpr
      intro b
      filter_upwards [eventually_ge_atTop (2 - b)] with x hx
      linarith
    have h := (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp
      hsub
    simpa only [Function.comp_def, zero_mul] using h.mul_const (Real.log ‖riemannZeta (2 : ℂ)‖)
  apply squeeze_zero_norm' _ hdec
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa using norm_riemannZetaEulerLog_le_two_rpow
    (s := (x : ℂ) + T * I) (by norm_num : (1 : ℝ) < 2) (by simpa using hx)

/-- The Euler logarithm differentiates along the horizontal coordinate without a branch choice. -/
theorem hasDerivAt_riemannZetaEulerLog_horizontal {x : ℝ} (hx : 1 < x) (T : ℝ) :
    HasDerivAt (fun y : ℝ => riemannZetaEulerLog ((y : ℂ) + T * I))
      (logDeriv riemannZeta ((x : ℂ) + T * I)) x := by
  have hs : 1 < ((x : ℂ) + T * I).re := by simpa using hx
  have hd := (differentiableAt_riemannZetaEulerLog hs).hasDerivAt
  rw [deriv_riemannZetaEulerLog hs] at hd
  simpa using! (hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (T * I))).comp_ofReal

/-- The entire logarithmic-derivative ray integral is the negative Euler logarithm at its start. -/
theorem integral_logDeriv_riemannZeta_horizontal_Ioi {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    (∫ x in Ioi σ, logDeriv riemannZeta ((x : ℂ) + T * I)) =
      -riemannZetaEulerLog ((σ : ℂ) + T * I) := by
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x hx => hasDerivAt_riemannZetaEulerLog_horizontal (hσ.trans_le hx) T)
    (integrableOn_logDeriv_riemannZeta_horizontal_Ioi hσ T)
    (tendsto_riemannZetaEulerLog_horizontal_atTop T)

end
