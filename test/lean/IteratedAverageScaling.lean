import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageScaling

/-! # Relative-step homogeneity, arbitrary order and vertical-line phase tests -/

open Complex intervalIntegral

example {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {z : ℂ}
    (hz : ∀ j : ℕ, z + j ≠ 0) (n : ℕ) :
    iteratedBoxAverageComplex (h * x) n (fun t => (t : ℂ) ^ z / z) x =
      (x : ℂ) ^ z * iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ z / z) 1 :=
  iteratedBoxAverageComplex_cpow_div_relative hh hx hz n

example {h x : ℝ} (hh : 0 < h) (hx : 0 < x) (γ : ℝ) (n : ℕ) :
    iteratedBoxAverageComplex (h * x) n
        (fun t => (t : ℂ) ^ ((1 / 2 : ℂ) + γ * I) / ((1 / 2 : ℂ) + γ * I)) x =
      (Real.exp ((1 / 2 : ℝ) * Real.log x) : ℂ) *
        (iteratedBoxAverageComplex h n
          (fun t => (t : ℂ) ^ ((1 / 2 : ℂ) + γ * I) / ((1 / 2 : ℂ) + γ * I)) 1 *
          exp (I * ((Real.log x * γ : ℝ) : ℂ))) := by
  have hz : ∀ j : ℕ, (1 / 2 : ℂ) + γ * I + j ≠ 0 := by
    intro j hj
    have hr := congrArg Complex.re hj
    simp at hr
    have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  simpa using iteratedBoxAverageComplex_cpow_div_phase (β := 1 / 2) hh hx hz (by simp) n

example {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((fwdDiff (0 * x))^[0] (fun t : ℝ => (t : ℂ) ^ z)) x =
      (x : ℂ) ^ z * ((fwdDiff 0)^[0] (fun t : ℝ => (t : ℂ) ^ z)) 1 :=
  fwdDiff_iter_cpow_relative le_rfl hx z 0

example {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = (Real.exp (z.re * Real.log x) : ℂ) *
      exp (I * ((Real.log x * z.im : ℝ) : ℂ)) :=
  ofReal_cpow_eq_exp_mul_phase hx z
