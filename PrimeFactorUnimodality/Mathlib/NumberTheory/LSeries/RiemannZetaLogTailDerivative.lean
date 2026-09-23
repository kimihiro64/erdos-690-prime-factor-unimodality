/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogNormDeriv
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerIntegral
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogIntegral

/-! # The height derivative of the entire horizontal zeta logarithmic tail

The von Mangoldt exponential majorant is independent of height and
integrable on the full ray. Dominated differentiation is therefore valid
without a truncation or an assumed interchange. The exact improper
logarithmic-derivative integral identifies the derivative as the Euler
argument at the ray's left endpoint, at every real height.
-/

noncomputable section

open ArithmeticFunction Complex Filter MeasureTheory Set
open scoped Topology

/-- The height derivative under the complete right-half-plane integral has an integrable majorant. -/
theorem hasDerivAt_integral_log_norm_riemannZeta_horizontal_Ioi {σ : ℝ}
    (hσ : 1 < σ) (T : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (riemannZetaEulerLog ((σ : ℂ) + T * I)).im T := by
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun x : ℝ => -(logDeriv riemannZeta ((x : ℂ) + t * I)).im) (volume.restrict (Ioi σ)) := by
    have hc : ContinuousOn (fun x : ℝ => -(logDeriv riemannZeta ((x : ℂ) + t * I)).im)
        (Ioi σ) := by
      intro x hx
      have hh := (continuousAt_logDeriv_riemannZeta
        (show 1 < ((x : ℂ) + t * I).re by simpa using hσ.trans hx)).comp
          (f := fun y : ℝ => (y : ℂ) + t * I) (by fun_prop)
      exact ((continuous_im.continuousAt.comp hh).neg).continuousWithinAt
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi σ)) (s := univ)
    (F := fun t x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
    (F' := fun t x : ℝ => -(logDeriv riemannZeta ((x : ℂ) + t * I)).im)
    (bound := fun x : ℝ => (2 : ℝ) ^ (σ - x) *
      ∑' n, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n‖)
    (x₀ := T) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun t =>
      (integrableOn_log_norm_riemannZeta_horizontal_Ioi hσ t).aestronglyMeasurable))
    (integrableOn_log_norm_riemannZeta_horizontal_Ioi hσ T) (hmeas T)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      intro t _
      simp only [norm_neg, Real.norm_eq_abs]
      exact (abs_im_le_norm _).trans (by
        simpa using norm_logDeriv_riemannZeta_le_two_rpow
          (s := (x : ℂ) + t * I) hσ (by simpa using hx.le)))
    (integrableOn_riemannZetaLogDerivMajorant σ)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      intro t _
      have hs : 1 < ((x : ℂ) + t * I).re := by simpa using hσ.trans hx
      have h1 : (x : ℂ) + t * I ≠ 1 := by intro he; simp [he] at hs
      exact (differentiableAt_riemannZeta h1).hasDerivAt.log_norm_vertical
        (riemannZeta_ne_zero_of_one_lt_re hs))
  have hi := integrableOn_logDeriv_riemannZeta_horizontal_Ioi hσ T
  have him : (∫ x in Ioi σ, (logDeriv riemannZeta ((x : ℂ) + T * I)).im) =
      (∫ x in Ioi σ, logDeriv riemannZeta ((x : ℂ) + T * I)).im := integral_im hi
  have he : (∫ x in Ioi σ, -(logDeriv riemannZeta ((x : ℂ) + T * I)).im) =
      (riemannZetaEulerLog ((σ : ℂ) + T * I)).im := by
    rw [integral_neg, him, integral_logDeriv_riemannZeta_horizontal_Ioi hσ T, neg_im, neg_neg]
  exact he ▸ hd.2

/-- The entire right-hand logarithmic tail is continuous at every real height. -/
theorem continuous_integral_log_norm_riemannZeta_horizontal_Ioi {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun T : ℝ => ∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) :=
  continuous_iff_continuousAt.mpr
    (fun T => (hasDerivAt_integral_log_norm_riemannZeta_horizontal_Ioi hσ T).continuousAt)

/-- The integrated Euler argument equals the increment of the complete logarithmic tail. -/
theorem integral_im_riemannZetaEulerLog_vertical {σ : ℝ} (hσ : 1 < σ) (a b : ℝ) :
    (∫ t in a..b, (riemannZetaEulerLog ((σ : ℂ) + t * I)).im) =
      (∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + b * I)‖) -
        ∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + a * I)‖ := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_integral_log_norm_riemannZeta_horizontal_Ioi hσ t)
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro t
  exact continuous_im.continuousAt.comp
    ((differentiableAt_riemannZetaEulerLog (by simpa using hσ)).continuousAt.comp
      (f := fun u : ℝ => (σ : ℂ) + u * I) (by fun_prop))

end
