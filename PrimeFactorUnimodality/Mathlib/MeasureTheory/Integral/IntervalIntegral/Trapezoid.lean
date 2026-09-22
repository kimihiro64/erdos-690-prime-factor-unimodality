/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The complex trapezoid rule with an integral remainder

Two differentiations and the fundamental theorem of calculus identify the
trapezoid error with the second derivative integrated against a quadratic
weight. Bounding that weight gives an error estimate using the integral
of the second derivative's norm, rather than its supremum.
-/

open Complex MeasureTheory Set

namespace intervalIntegral

/-- The exact second-derivative remainder in the complex trapezoid rule. -/
theorem trapezoid_sub_integral_eq {f f' f'' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hi : IntervalIntegrable f'' volume a b) :
    ((b : ℂ) - a) / 2 * (f a + f b) - (∫ x in a..b, f x) =
      ∫ x in a..b, ((x : ℂ) - a) * (b - x) / 2 * f'' x := by
  let p (x : ℝ) : ℂ := ((x : ℂ) - a) * (b - x) / 2
  let m (x : ℝ) : ℂ := (x : ℂ) - ((a : ℂ) + b) / 2
  let Q (x : ℝ) : ℂ := p x * f' x + m x * f x
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt Q (f x + p x * f'' x) x := by
    have hp := ((((hasDerivAt_id (x : ℂ)).sub_const (a : ℂ)).mul
      ((hasDerivAt_id (x : ℂ)).const_sub (b : ℂ))).div_const 2).comp_ofReal
    have hm := ((hasDerivAt_id (x : ℂ)).sub_const (((a : ℂ) + b) / 2)).comp_ofReal
    convert! (hp.mul (hf' x hx)).add (hm.mul (hf x hx)) using 1
    dsimp [p]
    ring
  have hfi : IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
  have hpi : IntervalIntegrable (fun x => p x * f'' x) volume a b :=
    hi.continuousOn_mul (by dsimp [p]; fun_prop)
  have h := integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa only [uIcc_of_le hab] using hx)) (hfi.add hpi)
  rw [integral_add hfi hpi] at h
  dsimp only [Q, p, m] at h
  linear_combination -h

/-- The trapezoid error is bounded by the integral of the second derivative's norm. -/
theorem norm_trapezoid_sub_integral_le {f f' f'' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hi : IntervalIntegrable f'' volume a b) :
    ‖((b : ℂ) - a) / 2 * (f a + f b) - (∫ x in a..b, f x)‖ ≤
      (b - a) ^ 2 / 8 * ∫ x in a..b, ‖f'' x‖ := by
  rw [trapezoid_sub_integral_eq hab hf hf' hi, ← integral_const_mul]
  apply norm_integral_le_of_norm_le hab _ (hi.norm.const_mul ((b - a) ^ 2 / 8))
  apply Filter.Eventually.of_forall
  intro x hx
  have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1.le
  have hxb : 0 ≤ b - x := sub_nonneg.mpr hx.2
  have hw : ‖((x : ℂ) - a) * (b - x) / 2‖ ≤ (b - a) ^ 2 / 8 := by
    rw [← ofReal_sub, ← ofReal_sub, ← ofReal_mul, ← ofReal_ofNat, ← ofReal_div,
      norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (2 * x - a - b)]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)

end intervalIntegral
