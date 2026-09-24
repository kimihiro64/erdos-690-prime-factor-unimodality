import PrimeFactorUnimodality.Helpers.Analytic.PlattConvolutionInputs
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaFrequencyInputs

set_option autoImplicit false

/-! # Actual zeta Fourier enclosures from shared rounded convolution

The analytic input enclosures still justify the true shifted frequencies,
including any circular wraparound. The finite Dirichlet prefix is computed
by checked forward transforms, summed products and one inverse, not supplied
as an independent numerical premise. Tail, pole and final rounding errors
are retained in the same consumer budget used by the zeta-grid theorem.
-/

open Finset
open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- A complete rounded convolution and the analytic input bounds enclose the true zeta transform. -/
theorem norm_fourier_plattZetaWindow_sub_shared_convolution_le {n : ℕ}
    (m J K k : ℕ) (hm : 1 ≤ m) (hJ : 0 < J)
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
  norm_fourier_plattZetaWindow_sub_approx_input_le m J K k hm hJ ht₀ hh x hc hs hQ hρ
    (norm_plattApproxDirichletPrefix_sub_pole_trace_le J K bin c w Q ht j hz)

end

end PrimeFactorUnimodality
