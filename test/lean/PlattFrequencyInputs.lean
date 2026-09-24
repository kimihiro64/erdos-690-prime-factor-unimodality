import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaFrequencyInputs
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaPoleFormula

/-! True Fourier inputs include every finite error and retain the full pole phase and parity. -/

open PrimeFactorUnimodality Finset
open scoped ComplexConjugate FourierTransform

example (m J K k : ℕ) (hm : 1 ≤ m) (hJ : 0 < J) {t₀ h : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) (hx : 0 ≤ x)
    {c : ℕ → ℂ} {u w σ η : ℕ → ℝ} {q : ℕ → ℕ → ℂ} {ε : ℕ → ℕ → ℝ}
    (hc : ∀ n ∈ range J, ‖plattDirichletWeight t₀ (n + 1) - c n‖ ≤ η n)
    (hs : ∀ n ∈ range J, |x + plattDirichletShift (n + 1) - (u n + w n)| ≤ σ n)
    (hq : ∀ n ∈ range J, ∀ r ∈ range K,
      ‖𝓕 (plattWindowKernel (k + r) t₀ h) (u n) - q n r‖ ≤ ε n r)
    {ρ z : ℂ} {δρ τ : ℝ}
    (hρ : ‖(2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x - ρ‖ ≤ δρ)
    (hz : ‖plattApproxDirichletPrefix J K c q w - ρ - z‖ ≤ τ) :
    ‖plattReflectedFrequencyApprox k (-x) z - 𝓕 (plattZetaWindow k t₀ h) (-x)‖ ≤
      plattZetaFrequencyInputError m J K k t₀ h x w σ η c ε δρ τ := by
  rw [norm_sub_rev, norm_fourier_plattZetaWindow_sub_reflected, abs_neg, abs_of_nonneg hx]
  exact norm_fourier_plattZetaWindow_sub_approx_input_le m J K k hm hJ ht₀ hh x hc hs hq hρ hz

example (z : ℂ) : plattReflectedFrequencyApprox 1 (-3) z = -conj z := by
  norm_num [plattReflectedFrequencyApprox]

example (z : ℂ) : plattReflectedFrequencyApprox 2 (-3) z = conj z := by
  norm_num [plattReflectedFrequencyApprox]

example (k : ℕ) (z : ℂ) : plattReflectedFrequencyApprox k 0 z = z := by
  simp [plattReflectedFrequencyApprox]

example (h x : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue 0 0 h x =
      ((2 * Real.pi * Real.pi ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
        Complex.exp (((1 / (8 * h ^ 2) - Real.pi * x : ℝ) : ℂ) +
          (((-Real.pi / 8 : ℝ) : ℂ) * Complex.I)) := by
  simpa using plattZetaPoleCorrection_eq_exp 0 0 h x
