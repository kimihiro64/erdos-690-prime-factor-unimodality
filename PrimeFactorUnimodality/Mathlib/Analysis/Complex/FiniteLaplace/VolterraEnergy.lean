/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Energy identity for a finite Volterra integral

For a continuous real source, the exponentially weighted primitive solves
`Q' = q - s*Q`. Integrating the derivative of its squared norm gives a
nonnegative real quadratic form whenever `Re(s)` is nonnegative.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- The exponentially weighted primitive with zero initial value at `a`. -/
def finiteVolterra (q : ℝ → ℝ) (a : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  exp (-s * (v : ℂ)) * ∫ w in a..v, exp (s * (w : ℂ)) * (q w : ℂ)

/-- The weighted primitive vanishes at its initial endpoint. -/
theorem finiteVolterra_self (q : ℝ → ℝ) (a : ℝ) (s : ℂ) : finiteVolterra q a s a = 0 := by
  simp [finiteVolterra]

/-- Direct differentiation gives the first-order Volterra equation. -/
theorem hasDerivAt_finiteVolterra {q : ℝ → ℝ} (hq : Continuous q) (a : ℝ) (s : ℂ) (v : ℝ) :
    HasDerivAt (finiteVolterra q a s) ((q v : ℂ) - s * finiteVolterra q a s v) v := by
  have hc : Continuous (fun w : ℝ => exp (s * (w : ℂ)) * (q w : ℂ)) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a v)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he := (((hasDerivAt_id v).ofReal_comp).const_mul (-s)).cexp
  convert he.mul hi using 1
  · rfl
  · dsimp [finiteVolterra]
    have hexp : exp (-s * (v : ℂ)) * exp (s * (v : ℂ)) = 1 := by
      rw [← exp_add]
      simp
    linear_combination -(q v : ℂ) * hexp

/-- Continuity follows from the actual derivative at every point. -/
theorem continuous_finiteVolterra {q : ℝ → ℝ} (hq : Continuous q) (a : ℝ) (s : ℂ) :
    Continuous (finiteVolterra q a s) :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_finiteVolterra hq a s v).continuousAt

/-- The squared norm satisfies the real energy differential equation. -/
theorem hasDerivAt_norm_sq_finiteVolterra {q : ℝ → ℝ} (hq : Continuous q)
    (a : ℝ) (s : ℂ) (v : ℝ) :
    HasDerivAt (fun v => ‖finiteVolterra q a s v‖ ^ 2)
      (2 * (q v * (finiteVolterra q a s v).re - s.re * ‖finiteVolterra q a s v‖ ^ 2)) v := by
  convert (hasDerivAt_finiteVolterra hq a s v).norm_sq using 1
  rw [Complex.inner]
  simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im,
    normSq_apply, ← normSq_eq_norm_sq]
  ring

/-- The exact real energy identity for the weighted primitive. -/
theorem integral_mul_re_finiteVolterra_eq {q : ℝ → ℝ} (hq : Continuous q)
    (a b : ℝ) (s : ℂ) :
    (∫ v in a..b, q v * (finiteVolterra q a s v).re) =
      ‖finiteVolterra q a s b‖ ^ 2 / 2 +
        s.re * ∫ v in a..b, ‖finiteVolterra q a s v‖ ^ 2 := by
  have hQ := continuous_finiteVolterra hq a s
  have h₁ : IntervalIntegrable (fun v => q v * (finiteVolterra q a s v).re) volume a b :=
    (hq.mul (continuous_re.comp hQ)).intervalIntegrable a b
  have h₂ : IntervalIntegrable (fun v => s.re * ‖finiteVolterra q a s v‖ ^ 2) volume a b :=
    (continuous_const.mul (hQ.norm.pow 2)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_norm_sq_finiteVolterra hq a s v) ((h₁.sub h₂).const_mul 2)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub h₁ h₂,
    intervalIntegral.integral_const_mul, finiteVolterra_self] at h
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at h
  linarith

/-- A nonnegative real parameter makes the real Volterra quadratic form nonnegative. -/
theorem integral_mul_re_finiteVolterra_nonneg {q : ℝ → ℝ} (hq : Continuous q)
    {a b : ℝ} (hab : a ≤ b) {s : ℂ} (hs : 0 ≤ s.re) :
    0 ≤ ∫ v in a..b, q v * (finiteVolterra q a s v).re := by
  rw [integral_mul_re_finiteVolterra_eq hq]
  exact add_nonneg (by positivity) (mul_nonneg hs
    (intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)))

end

end Complex
