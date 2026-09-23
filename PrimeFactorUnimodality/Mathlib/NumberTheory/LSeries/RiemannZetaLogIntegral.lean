/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerDecay

/-! # Integrable horizontal logarithmic tails of the Riemann zeta function

Mathlib's meromorphic log-integrability handles zeros on finite segments.
The Euler logarithm gives an exponentially decaying absolute majorant on
each right half-plane. Integrating it bounds both signs of the complete
infinite tail uniformly in imaginary height, with no zero-free endpoint
assumption in the finite-segment theorem.
-/

noncomputable section

open Complex MeasureTheory Set

/-- Horizontal log-modulus segments are integrable even when they cross zeta zeros. -/
theorem intervalIntegrable_log_norm_riemannZeta_horizontal {T : ℝ} (hT : T ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  have hs : (x : ℂ) + T * I ≠ 1 := by
    intro he
    exact hT (by simpa using congrArg Complex.im he)
  exact (analyticOn_riemannZeta _ hs).meromorphicAt.comp_analyticAt
    (g := fun y : ℝ => (y : ℂ) + T * I)
    ((Complex.ofRealCLM.analyticAt x).add analyticAt_const)

private theorem two_rpow_sub_eq (c x : ℝ) :
    (2 : ℝ) ^ (c - x) = Real.exp (Real.log 2 * c) * Real.exp (-Real.log 2 * x) := by
  rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
  congr 1
  ring

private theorem integrableOn_horizontalLogMajorant (c K : ℝ) :
    IntegrableOn (fun x : ℝ => (2 : ℝ) ^ (c - x) * K) (Ioi c) := by
  simp_rw [two_rpow_sub_eq]
  exact ((integrableOn_exp_mul_Ioi
    (neg_lt_zero.mpr (Real.log_pos (by norm_num))) c).const_mul _).mul_const K

private theorem integral_horizontalLogMajorant (c K : ℝ) :
    (∫ x in Ioi c, (2 : ℝ) ^ (c - x) * K) = K / Real.log 2 := by
  simp_rw [two_rpow_sub_eq]
  rw [integral_mul_const, integral_const_mul,
    integral_exp_mul_Ioi (neg_lt_zero.mpr (Real.log_pos (by norm_num)))]
  rw [show -Real.log 2 * c = -(Real.log 2 * c) by ring, Real.exp_neg]
  field_simp

/-- The logarithm is continuous on every horizontal right-half-plane ray. -/
theorem continuousOn_log_norm_riemannZeta_horizontal {c : ℝ} (hc : 1 < c) (T : ℝ) :
    ContinuousOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) (Ioi c) := by
  intro x hx
  have hs : 1 < ((x : ℂ) + T * I).re := by simpa using hc.trans hx
  have hs1 : (x : ℂ) + T * I ≠ 1 := by intro he; simp [he] at hs
  have hne : riemannZeta ((x : ℂ) + T * I) ≠ 0 := by
    rw [← exp_riemannZetaEulerLog hs]
    exact exp_ne_zero _
  exact (((differentiableAt_riemannZeta hs1).continuousAt.comp
    (f := fun y : ℝ => (y : ℂ) + T * I)
    (show ContinuousAt (fun y : ℝ => (y : ℂ) + T * I) x by fun_prop)).norm.log
      (norm_ne_zero_iff.mpr hne)).continuousWithinAt

/-- The entire logarithmic horizontal tail is absolutely integrable for every height. -/
theorem integrableOn_log_norm_riemannZeta_horizontal_Ioi {c : ℝ} (hc : 1 < c) (T : ℝ) :
    IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) (Ioi c) := by
  apply (integrableOn_horizontalLogMajorant c (Real.log ‖riemannZeta (c : ℂ)‖)).mono'
    ((continuousOn_log_norm_riemannZeta_horizontal hc T).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa using abs_log_norm_riemannZeta_le_two_rpow (s := (x : ℂ) + T * I) hc
    (by simpa using hx.le)

/-- The entire absolute integral has the same explicit real-axis bound. -/
theorem integral_abs_log_norm_riemannZeta_horizontal_Ioi_le {c : ℝ} (hc : 1 < c) (T : ℝ) :
    (∫ x in Ioi c, |Real.log ‖riemannZeta ((x : ℂ) + T * I)‖|) ≤
      Real.log ‖riemannZeta (c : ℂ)‖ / Real.log 2 := by
  have h := integral_mono_of_nonneg
    (f := fun x : ℝ => |Real.log ‖riemannZeta ((x : ℂ) + T * I)‖|)
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    (integrableOn_horizontalLogMajorant c (Real.log ‖riemannZeta (c : ℂ)‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa using abs_log_norm_riemannZeta_le_two_rpow (s := (x : ℂ) + T * I) hc
        (by simpa using hx.le))
  simpa only [integral_horizontalLogMajorant] using h

/-- Both signs of the complete infinite log-modulus tail have an explicit real-axis bound. -/
theorem abs_integral_log_norm_riemannZeta_horizontal_Ioi_le {c : ℝ} (hc : 1 < c) (T : ℝ) :
    |∫ x in Ioi c, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖| ≤
      Real.log ‖riemannZeta (c : ℂ)‖ / Real.log 2 := by
  have h := norm_integral_le_of_norm_le
    (f := fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖)
    (integrableOn_horizontalLogMajorant c (Real.log ‖riemannZeta (c : ℂ)‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa using abs_log_norm_riemannZeta_le_two_rpow (s := (x : ℂ) + T * I) hc
        (by simpa using hx.le))
  simpa only [Real.norm_eq_abs, integral_horizontalLogMajorant] using h

/-- Every ordered subinterval of a right-half-plane ray has the same absolute budget. -/
theorem abs_integral_log_norm_riemannZeta_horizontal_le {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (T : ℝ) :
    |∫ x in a..b, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖| ≤
      Real.log ‖riemannZeta (a : ℂ)‖ / Real.log 2 := by
  rw [intervalIntegral.integral_of_le hab]
  apply abs_integral_le_integral_abs.trans
  apply (setIntegral_mono_set (integrableOn_log_norm_riemannZeta_horizontal_Ioi ha T).abs
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    (Filter.Eventually.of_forall (fun _ hx => hx.1))).trans
  exact integral_abs_log_norm_riemannZeta_horizontal_Ioi_le ha T

end
