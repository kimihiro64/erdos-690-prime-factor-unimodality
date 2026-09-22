import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaRemainder

set_option autoImplicit false

/-! # Gamma remainder regressions inside the critical strip

The second derivative of the nonzero cubic smoothing weight is `-6 + 12t`.
Its gamma integral must converge even at real part `3/4`, for every height.
Tests also include the endpoint `c=1` of the logarithmic Cauchy majorant and
the digamma lower bound at one.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory Set

private def weight₂ (u : ℝ) : ℂ := ((-6 + 12 * u : ℝ) : ℂ)

private theorem weight₂_bound (u : ℝ) (hu : u ∈ Icc 0 1) : ‖weight₂ u‖ ≤ 6 := by
  rw [weight₂, norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩

example : -Real.eulerMascheroniConstant ≤ (digamma 1).re :=
  neg_eulerMascheroni_le_re_digamma (by norm_num)

example : Integrable (fun t : ℝ => Real.log (|t| + 1) / ((1 / 4) ^ 2 + (t + 7) ^ 2)) := by
  simpa only [sub_neg_eq_add] using
    Real.integrable_log_add_abs_div_cauchy (a := 1 / 4) (c := 1) (by norm_num) le_rfl (-7)

example (t : ℝ) :
    |(digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re| ≤
      Real.log (|t| + 3) + |Real.eulerMascheroniConstant| + 5 :=
  abs_re_digamma_quarter_line_le t

example (t : ℝ) : Continuous (smoothedGammaIntegrand weight₂ 1 ((3 / 4 : ℂ) + t * I)) :=
  continuous_smoothedGammaIntegrand (by norm_num) (by unfold weight₂; fun_prop) (by norm_num)

example (t : ℝ) : Integrable (smoothedGammaIntegrand weight₂ 1 ((3 / 4 : ℂ) + t * I)) :=
  integrable_smoothedGammaIntegrand (M := 6) (by norm_num) (by unfold weight₂; fun_prop)
    (by norm_num) weight₂_bound (by norm_num)

example (s : ℂ) (hs : 1 / 2 < s.re) (t : ℝ) :
    ‖smoothedGammaIntegrand weight₂ 1 s t‖ ≤
      (Real.log (|t| + 3) + |Real.eulerMascheroniConstant| + 5) *
        (6 / (s.re - 1 / 2)) / ((s.re - 1 / 2) ^ 2 + (t - s.im) ^ 2) :=
  norm_smoothedGammaIntegrand_le (by norm_num) (by norm_num) weight₂_bound hs t

end

end PrimeFactorUnimodality.Tests
