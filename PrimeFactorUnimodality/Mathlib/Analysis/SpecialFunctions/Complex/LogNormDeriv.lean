/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring

/-! # Real derivatives of complex logarithmic moduli

Differentiating the squared norm and then the real logarithm avoids every
principal-log branch restriction. Nonvanishing is required only at the
evaluation point. Horizontal and vertical specializations give the two
Cauchy--Riemann derivatives of the log modulus.
-/

open Complex
open scoped ComplexConjugate

/-- The log modulus derivative is the real logarithmic derivative, independently of argument. -/
theorem HasDerivAt.log_norm_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f t‖) (f' / f x).re x := by
  have hd := (hf.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).div_const 2
  convert hd using 1
  · funext t
    rw [Real.log_pow]
    ring
  · rw [Complex.div_re, Complex.normSq_eq_norm_sq]
    simp only [real_inner_eq_re_inner, RCLike.inner_apply]
    change f'.re * (f x).re / ‖f x‖ ^ 2 + f'.im * (f x).im / ‖f x‖ ^ 2 =
      2 * (f' * conj (f x)).re / ‖f x‖ ^ 2 / 2
    simp only [mul_re, conj_re, conj_im]
    ring

namespace Complex

/-- Moving horizontally differentiates the log modulus to the real logarithmic derivative. -/
theorem HasDerivAt.log_norm_horizontal {f : ℂ → ℂ} {f' : ℂ} {x T : ℝ}
    (hf : HasDerivAt f f' ((x : ℂ) + T * I)) (hne : f ((x : ℂ) + T * I) ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log ‖f ((y : ℂ) + T * I)‖)
      (f' / f ((x : ℂ) + T * I)).re x := by
  have hd := (hf.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (T * I))).comp_ofReal
  simpa using hd.log_norm_complex hne

/-- Moving vertically differentiates the log modulus to minus the imaginary logarithmic derivative. -/
theorem HasDerivAt.log_norm_vertical {f : ℂ → ℂ} {f' : ℂ} {x T : ℝ}
    (hf : HasDerivAt f f' ((x : ℂ) + T * I)) (hne : f ((x : ℂ) + T * I) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖f ((x : ℂ) + t * I)‖)
      (-(f' / f ((x : ℂ) + T * I)).im) T := by
  have hd := (hf.comp (T : ℂ)
    (((hasDerivAt_id (T : ℂ)).mul_const I).const_add (x : ℂ))).comp_ofReal
  simpa only [Function.comp_def, id_eq, one_mul, mul_div_right_comm, mul_I_re]
    using hd.log_norm_complex hne

end Complex
