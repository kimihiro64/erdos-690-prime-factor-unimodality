/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.Dirichlet
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.HorizontalDecay

/-! # An integrable horizontal majorant for the zeta logarithmic derivative

Mathlib identifies the negative logarithmic derivative with the absolutely
convergent von Mangoldt series. Its support starts at two, so the existing
Dirichlet-series comparison gives exponential horizontal decay uniformly
in height. No estimate for zeros or numerical coefficient mass is needed.
-/

noncomputable section

open ArithmeticFunction Complex Filter MeasureTheory Set
open scoped Topology

/-- The absolute mass on a convergent real line provides a uniform horizontal majorant. -/
theorem norm_logDeriv_riemannZeta_le_two_rpow {σ : ℝ} {s : ℂ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ (2 : ℝ) ^ (σ - s.re) *
      ∑' n, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n‖ := by
  have hsupport (n : ℕ) (hn : n ≠ 0) (hc : (vonMangoldt n : ℂ) ≠ 0) : (2 : ℝ) ≤ n := by
    have hn1 : n ≠ 1 := by intro he; simp [he] at hc
    exact_mod_cast (show 2 ≤ n by omega)
  have h := LSeries.norm_le_rpow_mul_tsum_norm_of_support (by norm_num : (0 : ℝ) < 2)
    hs hsupport (LSeriesSummable_vonMangoldt hσ)
  simpa only [LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hσ.trans_le hs),
    neg_div, norm_neg, logDeriv_apply] using h

/-- The logarithmic derivative is continuous at every point of the right half-plane. -/
theorem continuousAt_logDeriv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    ContinuousAt (logDeriv riemannZeta) s := by
  have h1 : s ≠ 1 := by intro he; simp [he] at hs
  exact (analyticOn_riemannZeta s h1).deriv.continuousAt.div
    (differentiableAt_riemannZeta h1).continuousAt (riemannZeta_ne_zero_of_one_lt_re hs)

/-- The complete exponential majorant is integrable without evaluating its series coefficient. -/
theorem integrableOn_riemannZetaLogDerivMajorant (σ : ℝ) :
    IntegrableOn (fun x : ℝ => (2 : ℝ) ^ (σ - x) *
      ∑' n, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n‖) (Ioi σ) := by
  have he (x : ℝ) : (2 : ℝ) ^ (σ - x) =
      Real.exp (Real.log 2 * σ) * Real.exp (-Real.log 2 * x) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  exact ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (Real.log_pos (by norm_num))) σ).const_mul
    (Real.exp (Real.log 2 * σ))).mul_const _

/-- The actual logarithmic derivative is absolutely integrable along the entire horizontal ray. -/
theorem integrableOn_logDeriv_riemannZeta_horizontal_Ioi {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    IntegrableOn (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + T * I)) (Ioi σ) := by
  have hc : ContinuousOn (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + T * I)) (Ioi σ) := by
    intro x hx
    exact ((continuousAt_logDeriv_riemannZeta (by simpa using hσ.trans hx)).comp
      (f := fun y : ℝ => (y : ℂ) + T * I) (by fun_prop)).continuousWithinAt
  apply (integrableOn_riemannZetaLogDerivMajorant σ).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa using norm_logDeriv_riemannZeta_le_two_rpow
    (s := (x : ℂ) + T * I) hσ (by simpa using hx.le)

end
