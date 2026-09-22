/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpLinear

/-! # Real endpoint formulas for damped trigonometric integrals

Take real and imaginary parts of the complex exponential integrals.
The real formulas involve only arithmetic, exponentials, sine, and cosine.
The two purely real integrals include their zero-exponent values; the
trigonometric formulas apply whenever exponent and frequency are not both zero.
-/

namespace Real

noncomputable section

/-- The real exponential integral with the removable value at zero exponent. -/
def expIntegral (w d : ℝ) : ℝ := if w = 0 then d else (exp (w * d) - 1) / w

/-- The linearly weighted real exponential integral, including zero exponent. -/
def expLinearIntegral (w d : ℝ) : ℝ :=
  if w = 0 then d ^ 2 / 2 else (exp (w * d) - 1 - w * d) / w ^ 2

/-- Endpoint expression for an exponential times cosine. -/
def expCosIntegral (w b d : ℝ) : ℝ :=
  (exp (w * d) * (w * cos (b * d) + b * sin (b * d)) - w) / (w ^ 2 + b ^ 2)

/-- Endpoint expression for an exponential times sine. -/
def expSinIntegral (w b d : ℝ) : ℝ :=
  (exp (w * d) * (w * sin (b * d) - b * cos (b * d)) + b) / (w ^ 2 + b ^ 2)

/-- Endpoint expression for an exponential times cosine with linear endpoint weight. -/
def expLinearCosIntegral (w b d : ℝ) : ℝ :=
  ((w ^ 2 - b ^ 2) * (exp (w * d) * cos (b * d) - 1 - w * d) +
    2 * w * b * (exp (w * d) * sin (b * d) - b * d)) / (w ^ 2 + b ^ 2) ^ 2

end

end Real

namespace Complex

noncomputable section

/-- The complex endpoint expression agrees with its real branch formula. -/
theorem expIntegral_ofReal (w d : ℝ) :
    expIntegral (w : ℂ) d = (Real.expIntegral w d : ℂ) := by
  by_cases hw : w = 0
  · simp [hw, Real.expIntegral]
  · simp [expIntegral, Real.expIntegral, hw, ← ofReal_mul, ← ofReal_exp]

/-- The linearly weighted expression agrees with its real branch formula. -/
theorem expLinearIntegral_ofReal (w d : ℝ) :
    expLinearIntegral (w : ℂ) d = (Real.expLinearIntegral w d : ℂ) := by
  by_cases hw : w = 0
  · simp [hw, Real.expLinearIntegral]
  · simp [expLinearIntegral, Real.expLinearIntegral, hw, ← ofReal_mul, ← ofReal_exp]

private theorem frequency_ne_zero {w b : ℝ} (h : w ≠ 0 ∨ b ≠ 0) :
    (w : ℂ) + (b : ℂ) * I ≠ 0 := by
  intro he
  have hr : w = 0 := by simpa using congrArg re he
  have hi : b = 0 := by simpa using congrArg im he
  exact h.elim (fun hw => hw hr) (fun hb => hb hi)

/-- Real part of the complex exponential endpoint formula. -/
theorem expIntegral_re {w b : ℝ} (h : w ≠ 0 ∨ b ≠ 0) (d : ℝ) :
    (expIntegral ((w : ℂ) + (b : ℂ) * I) d).re = Real.expCosIntegral w b d := by
  simp [expIntegral, frequency_ne_zero h, div_re, exp_re, exp_im,
    normSq_apply, Real.expCosIntegral]
  ring

/-- Imaginary part of the same endpoint formula. -/
theorem expIntegral_im {w b : ℝ} (h : w ≠ 0 ∨ b ≠ 0) (d : ℝ) :
    (expIntegral ((w : ℂ) + (b : ℂ) * I) d).im = Real.expSinIntegral w b d := by
  simp [expIntegral, frequency_ne_zero h, div_im, exp_re, exp_im,
    normSq_apply, Real.expSinIntegral]
  ring

/-- Real part of the linearly weighted complex formula. -/
theorem expLinearIntegral_re {w b : ℝ} (h : w ≠ 0 ∨ b ≠ 0) (d : ℝ) :
    (expLinearIntegral ((w : ℂ) + (b : ℂ) * I) d).re = Real.expLinearCosIntegral w b d := by
  simp [expLinearIntegral, frequency_ne_zero h, div_re, exp_re, exp_im,
    normSq_apply, Real.expLinearCosIntegral, pow_two]
  ring

end

end Complex

namespace intervalIntegral

open MeasureTheory

/-- A real exponential integral evaluated at both endpoints, including zero exponent. -/
theorem integral_exp_eq_expIntegral (w d : ℝ) :
    (∫ u in (0 : ℝ)..d, Real.exp (w * u)) = Real.expIntegral w d := by
  have h := Complex.integral_exp_eq_expIntegral (w : ℂ) d
  rw [Complex.expIntegral_ofReal] at h
  have he : (fun u : ℝ => Complex.exp ((w : ℂ) * u)) =
      fun u : ℝ => (Real.exp (w * u) : ℂ) := by
    funext u
    simp [← Complex.ofReal_mul, Complex.ofReal_exp]
  rw [he, integral_ofReal] at h
  exact_mod_cast h

/-- The linear endpoint weight has its exact branch formula. -/
theorem integral_sub_mul_exp_eq_expLinearIntegral (w d : ℝ) :
    (∫ u in (0 : ℝ)..d, (d - u) * Real.exp (w * u)) = Real.expLinearIntegral w d := by
  have h := Complex.integral_sub_mul_exp_eq_expLinearIntegral (w : ℂ) d
  rw [Complex.expLinearIntegral_ofReal] at h
  have he : (fun u : ℝ => ((d : ℂ) - u) * Complex.exp ((w : ℂ) * u)) =
      fun u : ℝ => (((d - u) * Real.exp (w * u) : ℝ) : ℂ) := by
    funext u
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_exp]
  rw [he, integral_ofReal] at h
  exact_mod_cast h

/-- Exact damped cosine integral. -/
theorem integral_exp_mul_cos {w b : ℝ} (h : w ≠ 0 ∨ b ≠ 0) (d : ℝ) :
    (∫ u in (0 : ℝ)..d, Real.exp (w * u) * Real.cos (b * u)) = Real.expCosIntegral w b d := by
  have hi : IntervalIntegrable
      (fun u : ℝ => Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)) volume 0 d :=
    (by fun_prop : Continuous (fun u : ℝ =>
      Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u))).intervalIntegrable 0 d
  calc
    _ = ∫ u in (0 : ℝ)..d,
        (Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)).re := by
      apply integral_congr
      intro u _
      simp [Complex.exp_re]
    _ = (∫ u in (0 : ℝ)..d, Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)).re :=
      intervalIntegral_re hi
    _ = _ := by rw [Complex.integral_exp_eq_expIntegral, Complex.expIntegral_re h]

/-- Exact damped sine integral. -/
theorem integral_exp_mul_sin {w b : ℝ} (h : w ≠ 0 ∨ b ≠ 0) (d : ℝ) :
    (∫ u in (0 : ℝ)..d, Real.exp (w * u) * Real.sin (b * u)) = Real.expSinIntegral w b d := by
  have hi : IntervalIntegrable
      (fun u : ℝ => Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)) volume 0 d :=
    (by fun_prop : Continuous (fun u : ℝ =>
      Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u))).intervalIntegrable 0 d
  calc
    _ = ∫ u in (0 : ℝ)..d,
        (Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)).im := by
      apply integral_congr
      intro u _
      simp [Complex.exp_im]
    _ = (∫ u in (0 : ℝ)..d, Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)).im :=
      intervalIntegral_im hi
    _ = _ := by rw [Complex.integral_exp_eq_expIntegral, Complex.expIntegral_im h]

/-- Exact linearly weighted damped cosine integral. -/
theorem integral_sub_mul_exp_mul_cos {w b : ℝ} (h : w ≠ 0 ∨ b ≠ 0) (d : ℝ) :
    (∫ u in (0 : ℝ)..d, (d - u) * (Real.exp (w * u) * Real.cos (b * u))) =
      Real.expLinearCosIntegral w b d := by
  have hi : IntervalIntegrable (fun u : ℝ =>
      ((d : ℂ) - u) * Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)) volume 0 d :=
    (by fun_prop : Continuous (fun u : ℝ =>
      ((d : ℂ) - u) * Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u))).intervalIntegrable 0 d
  calc
    _ = ∫ u in (0 : ℝ)..d,
        (((d : ℂ) - u) * Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)).re := by
      apply integral_congr
      intro u _
      simp [Complex.exp_re, Complex.mul_re]
    _ = (∫ u in (0 : ℝ)..d,
        ((d : ℂ) - u) * Complex.exp (((w : ℂ) + (b : ℂ) * Complex.I) * u)).re :=
      intervalIntegral_re hi
    _ = _ := by
      rw [Complex.integral_sub_mul_exp_eq_expLinearIntegral, Complex.expLinearIntegral_re h]

end intervalIntegral
