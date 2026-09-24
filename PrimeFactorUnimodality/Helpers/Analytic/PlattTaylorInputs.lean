import PrimeFactorUnimodality.Helpers.Analytic.PlattTaylorAssembly

set_option autoImplicit false

/-! # Approximate shift and column inputs for the Gamma Taylor evaluator

The first-order remainder gives a uniform frequency perturbation bound.
It is combined with the proved Taylor remainder and all column errors, so
an enclosed logarithmic shift need not be represented by an exact real input.
-/

open Finset
open scoped FourierTransform Nat

namespace PrimeFactorUnimodality

noncomputable section

/-- The finite polynomial actually assembled from approximate derivative columns. -/
def plattApproxTaylor (K : ℕ) (q : ℕ → ℂ) (w : ℝ) : ℂ :=
  ∑ r ∈ range K, (w ^ r / (r ! : ℝ)) • q r

/-- The genuine transform is Lipschitz with the next Gaussian moment as constant. -/
theorem norm_fourier_plattWindowKernel_sub_le (k : ℕ) (t₀ u v : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ‖𝓕 (plattWindowKernel k t₀ h) v - 𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      plattWindowL1Bound (k + 1) h * |v - u| := by
  simpa [plattFourierTaylor, plattFourierTaylorBound] using
    norm_fourier_plattWindowKernel_sub_taylor_le 1 k t₀ u (v - u) hh

/-- Every source of error before the finite weight multiplication. -/
def plattTaylorInputError (K k : ℕ) (h w σ : ℝ) (ε : ℕ → ℝ) : ℝ :=
  plattWindowL1Bound (k + 1) h * σ + plattFourierTaylorBound K k h |w| +
    ∑ r ∈ range K, (|w| ^ r / (r ! : ℝ)) * ε r

/-- Enclosed shifts, Taylor truncation and enclosed columns bound the actual transform. -/
theorem norm_fourier_plattWindowKernel_sub_approx_input_le (K k : ℕ) (t₀ u w v : ℝ)
    {h σ : ℝ} (hh : 0 < h) (hv : |v - (u + w)| ≤ σ)
    {q : ℕ → ℂ} {ε : ℕ → ℝ}
    (hq : ∀ r ∈ range K, ‖𝓕 (plattWindowKernel (k + r) t₀ h) u - q r‖ ≤ ε r) :
    ‖𝓕 (plattWindowKernel k t₀ h) v - plattApproxTaylor K q w‖ ≤
      plattTaylorInputError K k h w σ ε := by
  have he := (norm_fourier_plattWindowKernel_sub_le k t₀ (u + w) v hh).trans
    (mul_le_mul_of_nonneg_left hv (plattWindowL1Bound_nonneg (k + 1) hh))
  have ht := norm_fourier_plattWindowKernel_sub_approx_taylor_le K k t₀ u w hh hq
  exact (norm_sub_le_norm_sub_add_norm_sub _ (𝓕 (plattWindowKernel k t₀ h) (u + w)) _).trans
    ((add_le_add he ht).trans_eq (by unfold plattTaylorInputError; ring))

end

end PrimeFactorUnimodality
