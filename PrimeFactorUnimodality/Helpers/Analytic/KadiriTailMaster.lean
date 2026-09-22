import PrimeFactorUnimodality.Helpers.Analytic.KadiriDistinguishedZero
import PrimeFactorUnimodality.Helpers.Analytic.KadiriOuterTail

/-! # The distinguished-zero master with the outer height tail explicit

Substitute the proved bound for the actual outer-divisor sum into the
distinguished-zero master. This leaves exactly the retained transform,
its polynomial error, the multiplicity-counted absolute-height tail, and
the pole/gamma terms. Numerical tail and gamma estimates are not assumed
to have been proved by this assembly step.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The actual master after bounding all other zero contributions by the paper's height tail. -/
theorem kadiriWeight_tail_master_nonneg {θ η η₀ σ₀ σ δ κ z H : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 1 / 2 ≤ δ)
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    (hc : 0 < σ₀ - η₀ + δ) (hz : z ≤ (σ - 1) / η) (hH : 0 < H)
    (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
    (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
      (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2)
    {ι : Type*} (S : Finset ι) (a k : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i)
    (j : ι) (hj : j ∈ S) (hk : k j = 1) (p : RiemannXiDivisorZeroIndex)
    (hβ : 1 / 2 < (riemannXiDivisorZeroValue p).re)
    (hβσ : (riemannXiDivisorZeroValue p).re ≤ σ)
    (hηρ : η = 1 - (riemannXiDivisorZeroValue p).re)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos (k i * u))
    (hfar : ∀ i ∈ S, ∀ q : RiemannXiDivisorZeroIndex,
      ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue q) →
        |k i * (riemannXiDivisorZeroValue p).im| + H ≤ |(riemannXiDivisorZeroValue q).im|) :
    0 ≤ (∑ i ∈ S, a i * smoothedLaplaceDifference (kadiriWeight θ η)
        (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I) - 1)) -
      a j * ((finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
          ((σ - (riemannXiDivisorZeroValue p).re : ℝ) : ℂ)).re -
        kadiriRetainedPairError θ η η₀ σ₀ κ δ) +
      kadiriOuterError θ η κ σ₀ z / 2 *
        (∑ i ∈ S, a i * xiHeightTail (k i * (riemannXiDivisorZeroValue p).im) H) +
      kadiriWeight θ η 0 * (∑ i ∈ S, a i * smoothedGammaFactorDifference κ δ
        ((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I)) +
      ∑ i ∈ S, a i * smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
        (kadiriWeightSupport θ η) κ δ
        ((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I) := by
  have hm := kadiriWeight_distinguished_master_nonneg hθ hη hη₀ hσ₀ hσ hσ₁
    (by linarith : 0 < δ) hκ hκ₂ hκ₃ hc S a k ha j hj hk p hβ hβσ hηρ hκ₁ hpoly
  have ht := kadiriWeight_weighted_outer_zero_sum_lower_bound
    hθ hη hκ hσ₀ hσ hδ hz hH hgap hcut S a k ha (riemannXiDivisorZeroValue p).im hfar
  linarith only [hm, ht]

end

end PrimeFactorUnimodality
