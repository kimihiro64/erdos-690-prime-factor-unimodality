import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletInputs
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaFourier
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaReality

set_option autoImplicit false

/-! # Complete input errors for the actual zeta Fourier evaluator

The genuine zeta-transform identity combines the Dirichlet tail with
approximate finite weights, enclosed shifts, Taylor columns, the complete
complex pole correction and final arithmetic rounding. Conjugation reuses
positive-frequency enclosures on the negative half-grid without increasing
their error or evaluating a growing negative-frequency Dirichlet tail.
-/

open Finset
open scoped ComplexConjugate FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The complete absolute error of an assembled Fourier input. -/
def plattZetaFrequencyInputError (m J K k : ℕ) (t₀ h x : ℝ)
    (w σ η : ℕ → ℝ) (c : ℕ → ℂ) (ε : ℕ → ℕ → ℝ) (δρ τ : ℝ) : ℝ :=
  plattDirichletTailBound m k t₀ h x J +
    (∑ n ∈ range J, plattDirichletInputError K k h (w n) (σ n) (η n) (c n) (ε n)) + δρ + τ

/-- All input errors give an enclosure of the genuine Fourier transform, not just its prefix. -/
theorem norm_fourier_plattZetaWindow_sub_approx_input_le (m J K k : ℕ) (hm : 1 ≤ m)
    (hJ : 0 < J) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ)
    {c : ℕ → ℂ} {u w σ η : ℕ → ℝ}
    (hc : ∀ n ∈ range J, ‖plattDirichletWeight t₀ (n + 1) - c n‖ ≤ η n)
    (hs : ∀ n ∈ range J, |x + plattDirichletShift (n + 1) - (u n + w n)| ≤ σ n)
    {q : ℕ → ℕ → ℂ} {ε : ℕ → ℕ → ℝ}
    (hq : ∀ n ∈ range J, ∀ r ∈ range K,
      ‖𝓕 (plattWindowKernel (k + r) t₀ h) (u n) - q n r‖ ≤ ε n r)
    {ρ z : ℂ} {δρ τ : ℝ}
    (hρ : ‖(2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x - ρ‖ ≤ δρ)
    (hz : ‖plattApproxDirichletPrefix J K c q w - ρ - z‖ ≤ τ) :
    ‖𝓕 (plattZetaWindow k t₀ h) x - z‖ ≤
      plattZetaFrequencyInputError m J K k t₀ h x w σ η c ε δρ τ := by
  have hp := norm_plattDirichletPrefix_sub_approx_le J K k t₀ x hh hc hs hq
  have he : ‖((∑ n ∈ range J, plattDirichletTerm k t₀ h x (n + 1)) -
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x) -
      (plattApproxDirichletPrefix J K c q w - ρ)‖ ≤
        (∑ n ∈ range J, plattDirichletInputError K k h (w n) (σ n) (η n) (c n) (ε n)) + δρ := by
    rw [show ((∑ n ∈ range J, plattDirichletTerm k t₀ h x (n + 1)) -
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x) -
      (plattApproxDirichletPrefix J K c q w - ρ) =
        ((∑ n ∈ range J, plattDirichletTerm k t₀ h x (n + 1)) -
          plattApproxDirichletPrefix J K c q w) -
        ((2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x - ρ) by ring]
    exact (norm_sub_le _ _).trans (add_le_add hp hρ)
  have ht := (norm_sub_le_norm_sub_add_norm_sub (𝓕 (plattZetaWindow k t₀ h) x)
    ((∑ n ∈ range J, plattDirichletTerm k t₀ h x (n + 1)) -
      (2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x)
    (plattApproxDirichletPrefix J K c q w - ρ)).trans
      (add_le_add (norm_fourier_plattZetaWindow_sub_prefix_le m k hm ht₀ hh x hJ) he)
  have hf := (norm_sub_le_norm_sub_add_norm_sub (𝓕 (plattZetaWindow k t₀ h) x)
    (plattApproxDirichletPrefix J K c q w - ρ) z).trans (add_le_add ht hz)
  simpa only [plattZetaFrequencyInputError, add_assoc] using hf

/-- Reflecting an enclosed sample preserves its error at every polynomial order. -/
theorem norm_fourier_plattZetaWindow_neg_sub_approx (k : ℕ) (t₀ h x : ℝ) (z : ℂ) :
    ‖𝓕 (plattZetaWindow k t₀ h) (-x) - (-1 : ℂ) ^ k * conj z‖ =
      ‖𝓕 (plattZetaWindow k t₀ h) x - z‖ := by
  have he : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  have hf : 𝓕 (plattZetaWindow k t₀ h) (-x) =
      (-1 : ℂ) ^ k * conj (𝓕 (plattZetaWindow k t₀ h) x) := by
    rw [conj_fourier_plattZetaWindow, ← mul_assoc, he, one_mul]
  rw [hf, ← mul_sub, ← map_sub, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_conj]

/-- Reuse a sample at the absolute frequency, retaining the polynomial-order parity. -/
def plattReflectedFrequencyApprox (k : ℕ) (x : ℝ) (z : ℂ) : ℂ :=
  if 0 ≤ x then z else (-1 : ℂ) ^ k * conj z

/-- The positive-half-grid enclosure applies to either sign with exactly the same error. -/
theorem norm_fourier_plattZetaWindow_sub_reflected (k : ℕ) (t₀ h x : ℝ) (z : ℂ) :
    ‖𝓕 (plattZetaWindow k t₀ h) x - plattReflectedFrequencyApprox k x z‖ =
      ‖𝓕 (plattZetaWindow k t₀ h) |x| - z‖ := by
  by_cases hx : 0 ≤ x
  · simp [plattReflectedFrequencyApprox, hx, abs_of_nonneg hx]
  · rw [plattReflectedFrequencyApprox, ite_eq_right hx, abs_of_nonpos (le_of_not_ge hx)]
    simpa only [neg_neg] using norm_fourier_plattZetaWindow_neg_sub_approx k t₀ h (-x) z

end

end PrimeFactorUnimodality
