import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaConvolution

/-! Regression checks connecting the full trace to the actual zeta, with analytic errors retained. -/

open Finset PrimeFactorUnimodality
open scoped FourierTransform

example {n : ℕ} (J : ℕ) (bin : ℕ → ZMod (2 ^ n)) (c : ℕ → ℂ) (w : ℕ → ℝ)
    (Q : ℕ → ZMod (2 ^ n) → ℂ) {t : Fourier.CorrelationTrace ℕ n}
    {α β : ℕ → ZMod (2 ^ n) → ℝ}
    (ht : t.Valid (range 0) (plattDirichletTaylorBuckets J bin c w) Q α β)
    (j : ZMod (2 ^ n)) : ‖t.value j‖ ≤ t.error (range 0) α β := by
  simpa [plattApproxDirichletPrefix, plattApproxTaylor] using
    norm_plattApproxDirichletPrefix_sub_correlationTrace_le J 0 bin c w Q ht j

example {n : ℕ} (m J K k : ℕ) (hm : 1 ≤ m) (hJ : 0 < J)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ)
    {c : ℕ → ℂ} {u w σ η : ℕ → ℝ}
    (hc : ∀ i ∈ range J, ‖plattDirichletWeight t₀ (i + 1) - c i‖ ≤ η i)
    (hs : ∀ i ∈ range J, |x + plattDirichletShift (i + 1) - (u i + w i)| ≤ σ i)
    (bin : ℕ → ZMod (2 ^ n)) (j : ZMod (2 ^ n))
    {Q : ℕ → ZMod (2 ^ n) → ℂ} {ε : ℕ → ℕ → ℝ}
    (hQ : ∀ i ∈ range J, ∀ r ∈ range K,
      ‖𝓕 (plattWindowKernel (k + r) t₀ h) (u i) - Q r (j + bin i)‖ ≤ ε i r)
    {t : Fourier.CorrelationTrace ℕ n} {α β : ℕ → ZMod (2 ^ n) → ℝ}
    (ht : t.Valid (range K) (plattDirichletTaylorBuckets J bin c w) Q α β)
    {ρ z : ℂ} {δρ δ : ℝ}
    (hρ : ‖(2 * (Real.pi : ℂ) * Complex.I) * plattZetaContourResidueValue k t₀ h x - ρ‖ ≤ δρ)
    (hz : ‖t.value j - ρ - z‖ ≤ δ) :
    ‖𝓕 (plattZetaWindow k t₀ h) x - z‖ ≤
      plattZetaFrequencyInputError m J K k t₀ h x w σ η c ε δρ
        (t.error (range K) α β + δ) :=
  norm_fourier_plattZetaWindow_sub_shared_convolution_le m J K k hm hJ ht₀ hh x
    hc hs bin j hQ ht hρ hz
