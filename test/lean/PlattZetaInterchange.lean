import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletInterchange

/-! The expansion is on the absolute-convergence contour and keeps all phase factors. -/

open PrimeFactorUnimodality MeasureTheory

example (k : ℕ) (t₀ h x : ℝ) {z : ℂ} (hz : z.im < -(1 / 2 : ℝ)) :
    plattZetaContourIntegrand k t₀ h x z =
      ∑' n : ℕ, plattDirichletContourTerm k t₀ h x (n + 1) z :=
  plattZetaContourIntegrand_eq_tsum k t₀ h x hz

example (k : ℕ) (t₀ h x : ℝ) {j : ℕ} (hj : 0 < j) (z : ℂ) :
    plattDirichletContourTerm k t₀ h x j z =
      plattContourIntegrand k t₀ h x z * plattPiPhase t₀ z *
        (1 / (j : ℂ) ^ plattZetaArgument t₀ z) :=
  plattDirichletContourTerm_eq k t₀ h x hj z

example (t₀ v : ℝ) : ‖plattPiPhase t₀ v‖ = 1 := by
  simp only [norm_plattPiPhase, Complex.ofReal_im, Real.rpow_zero]

example (m k : ℕ) (hm : 1 ≤ m) (t₀ h x : ℝ) :
    Summable (fun n : ℕ => ∫ v : ℝ, ‖plattDirichletContourTerm k t₀ h x (n + 1)
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)‖) :=
  summable_integral_norm_plattDirichletContourTerm_right m k hm t₀ h x

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    (∫ v : ℝ, plattZetaContourIntegrand k t₀ h x
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) =
        plattDirichletSeries k t₀ h x :=
  integral_plattZetaContourIntegrand_right_eq_series m k hm ht₀ hh x
