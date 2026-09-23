/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAveragePower

/-! # Relative-step averages of complex powers

Scaling both the base point and the averaging step factors out one complex
power. Separating its real amplitude from its imaginary phase gives fixed
coefficients for Fourier evaluation in the logarithm of the base point.
-/

open Function

namespace Complex

noncomputable section

/-- A positive real base separates into a positive amplitude and a unit phase. -/
theorem ofReal_cpow_eq_exp_mul_phase {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = (Real.exp (z.re * Real.log x) : ℂ) *
      exp (I * ((Real.log x * z.im : ℝ) : ℂ)) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le,
    ofReal_exp, ← exp_add]
  congr 1
  apply Complex.ext <;> simp [mul_comm]

/-- A forward difference with a relative step retains exact homogeneity. -/
theorem fwdDiff_iter_cpow_relative {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x)
    (z : ℂ) (n : ℕ) :
    ((fwdDiff (h * x))^[n] (fun t : ℝ => (t : ℂ) ^ z)) x =
      (x : ℂ) ^ z * ((fwdDiff h)^[n] (fun t : ℝ => (t : ℂ) ^ z)) 1 := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he : x + k • (h * x) = x * (1 + k • h) := by
    simp only [nsmul_eq_mul]
    ring
  have hp : 0 ≤ 1 + k • h := by
    simp only [nsmul_eq_mul]
    positivity
  rw [he, ofReal_mul, mul_cpow_ofReal_nonneg hx.le hp]
  simp only [zsmul_eq_mul]
  ring

end

end Complex

namespace intervalIntegral

noncomputable section

open Complex

/-- Every relative-step averaged divided power is a fixed coefficient times `x^z`. -/
theorem iteratedBoxAverageComplex_cpow_div_relative {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) {z : ℂ} (hz : ∀ j : ℕ, z + j ≠ 0) (n : ℕ) :
    iteratedBoxAverageComplex (h * x) n (fun t => (t : ℂ) ^ z / z) x =
      (x : ℂ) ^ z * iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ z / z) 1 := by
  rw [iteratedBoxAverageComplex_cpow_div_eq_difference (mul_pos hh hx) hx hz,
    iteratedBoxAverageComplex_cpow_div_eq_difference hh zero_lt_one hz,
    fwdDiff_iter_cpow_relative hh.le hx, cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'),
    cpow_natCast, ofReal_mul, mul_pow]
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hhC : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  field_simp [hxC, hhC, cpowPrimitiveDenom_ne_zero hz n]

/-- On a fixed vertical line, the coefficient is independent of the base point. -/
theorem iteratedBoxAverageComplex_cpow_div_phase {h x β : ℝ}
    (hh : 0 < h) (hx : 0 < x) {z : ℂ} (hz : ∀ j : ℕ, z + j ≠ 0)
    (hβ : z.re = β) (n : ℕ) :
    iteratedBoxAverageComplex (h * x) n (fun t => (t : ℂ) ^ z / z) x =
      (Real.exp (β * Real.log x) : ℂ) *
        (iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ z / z) 1 *
          exp (I * ((Real.log x * z.im : ℝ) : ℂ))) := by
  rw [iteratedBoxAverageComplex_cpow_div_relative hh hx hz,
    ofReal_cpow_eq_exp_mul_phase hx, hβ]
  ring

end

end intervalIntegral
