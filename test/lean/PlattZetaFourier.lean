import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaResidueNorm

/-! The actual zeta transform retains the full pole correction and the proved truncation error. -/

open PrimeFactorUnimodality MeasureTheory
open scoped FourierTransform Topology

example (k : ℕ) {h : ℝ} (hh : 0 < h) : Integrable (plattZetaWindow k (-1000) h) :=
  integrable_plattZetaWindow k (-1000) hh

example (k : ℕ) (t₀ h x : ℝ) :
    Filter.Tendsto
      (fun z : ℂ => (z - plattZetaPole t₀) * plattZetaContourIntegrand k t₀ h x z)
      (𝓝[≠] (plattZetaPole t₀)) (𝓝 (plattZetaContourResidueValue k t₀ h x)) :=
  tendsto_plattZetaContour_residue k t₀ h x

example (k : ℕ) (t₀ h x : ℝ) :
    meromorphicOrderAt (plattZetaContourIntegrand k t₀ h x) (plattZetaPole t₀) = (-1 : ℤ) :=
  meromorphicOrderAt_plattZetaContourIntegrand_pole k t₀ h x

example (k : ℕ) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    𝓕 (plattZetaWindow k t₀ h) x = plattDirichletSeries k t₀ h x -
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x :=
  fourier_plattZetaWindow_eq_series_sub_residue k ht₀ hh x

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h)
    (x : ℝ) {J : ℕ} (hJ : 0 < J) :
    ‖𝓕 (plattZetaWindow k t₀ h) x -
        ((∑ n ∈ Finset.range J, plattDirichletTerm k t₀ h x (n + 1)) -
          (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x)‖ ≤
      plattDirichletTailBound m k t₀ h x J :=
  norm_fourier_plattZetaWindow_sub_prefix_le m k hm ht₀ hh x hJ

example (t₀ : ℝ) (ht₀ : 0 ≤ t₀) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    ‖𝓕 (plattZetaWindow 0 t₀ h) x - plattDirichletSeries 0 t₀ h x‖ =
      2 * Real.pi ^ (5 / 4 : ℝ) *
        Real.exp (1 / (8 * h ^ 2) - t₀ ^ 2 / (2 * h ^ 2) - Real.pi * x) :=
  norm_fourier_plattZetaWindow_sub_series t₀ ht₀ hh x

example (k : ℕ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    𝓕 (plattZetaWindow k 0 h) x = plattDirichletSeries k 0 h x -
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k 0 h x :=
  fourier_plattZetaWindow_eq_series_sub_residue k (by norm_num) hh x
