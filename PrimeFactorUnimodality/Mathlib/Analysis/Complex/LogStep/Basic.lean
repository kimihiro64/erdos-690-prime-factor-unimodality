/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Integrated unit steps of complex logarithmic moduli

Differences of real log moduli are integrable even across a real zero.
Keeping the two logarithms separate respects the totalized value at zero.
-/

namespace Complex

noncomputable section

open MeasureTheory

/-- The logarithmic modulus gained by moving a real argument one unit right. -/
def logNormStep (w : ℂ) (x : ℝ) : ℝ :=
  Real.log ‖((x + 1 : ℝ) : ℂ) - w‖ - Real.log ‖(x : ℂ) - w‖

/-- The integrated logarithmic modulus step on the unit interval. -/
def logNormStepIntegral (w : ℂ) : ℝ := ∫ x in (0 : ℝ)..1, logNormStep w x

/-- Horizontal affine log moduli are integrable on every bounded interval. -/
theorem intervalIntegrable_log_norm_real_sub (w : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖(x : ℂ) - w‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  exact ((ofRealCLM.analyticAt x).sub analyticAt_const).meromorphicAt

/-- Both shifted log moduli remain integrable when the interval meets a zero. -/
theorem intervalIntegrable_logNormStep (w : ℂ) (a b : ℝ) :
    IntervalIntegrable (logNormStep w) volume a b := by
  have h := (intervalIntegrable_log_norm_real_sub w (a + 1) (b + 1)).comp_add_right 1
  simp only [add_sub_cancel_right] at h
  exact h.sub (intervalIntegrable_log_norm_real_sub w a b)

/-- The squared horizontal distance separates the real and imaginary coordinates. -/
theorem norm_real_sub_sq (w : ℂ) (x : ℝ) :
    ‖(x : ℂ) - w‖ ^ 2 = (x - w.re) ^ 2 + w.im ^ 2 := by
  rw [← normSq_eq_norm_sq, normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im]
  ring

/-- A unit step away from a zero in the left half-unit strip has nonnegative gain. -/
theorem logNormStep_nonneg {w : ℂ} (hw : w.re ≤ 1 / 2) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ logNormStep w x := by
  by_cases hz : (x : ℂ) - w = 0
  · have he : w = (x : ℂ) := (sub_eq_zero.mp hz).symm
    simp [logNormStep, he]
  · have hn : 0 < ‖(x : ℂ) - w‖ := norm_pos_iff.mpr hz
    have hsq1 := norm_real_sub_sq w x
    have hsq2 := norm_real_sub_sq w (x + 1)
    have hnorm : ‖(x : ℂ) - w‖ ≤ ‖((x + 1 : ℝ) : ℂ) - w‖ := by
      nlinarith [norm_nonneg (((x + 1 : ℝ) : ℂ) - w)]
    exact sub_nonneg.mpr (Real.log_le_log hn hnorm)

/-- The integrated gain is nonnegative, including a real-axis singularity. -/
theorem logNormStepIntegral_nonneg {w : ℂ} (hw : w.re ≤ 1 / 2) :
    0 ≤ logNormStepIntegral w :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ hx => logNormStep_nonneg hw hx.1)

/-- Conjugating the zero does not change a horizontal logarithmic step. -/
@[simp] theorem logNormStep_conj (w : ℂ) (x : ℝ) :
    logNormStep (star w) x = logNormStep w x := by
  unfold logNormStep
  have h (t : ℝ) : ‖(t : ℂ) - star w‖ = ‖(t : ℂ) - w‖ := by
    simpa only [map_sub, conj_ofReal, star_def] using norm_conj ((t : ℂ) - w)
  rw [h, h]

/-- Conjugation also preserves the integrated gain. -/
@[simp] theorem logNormStepIntegral_conj (w : ℂ) :
    logNormStepIntegral (star w) = logNormStepIntegral w := by
  simp only [logNormStepIntegral, logNormStep_conj]

end

end Complex
