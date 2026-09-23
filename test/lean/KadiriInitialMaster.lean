import PrimeFactorUnimodality.Helpers.Analytic.KadiriInitialMaster

/-! # The actual initial master no longer requires supplied low-zero information -/

namespace PrimeFactorUnimodality.Tests

open Complex Real

example {θ η η₀ σ₀ σ δ κ z H A : ℝ}
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
    (hηρ : η = 1 - (riemannXiDivisorZeroValue p).re)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos (k i * u))
    (hσA : 1 - 1 / (56 * Real.log A) ≤ σ)
    (hharm : ∀ i ∈ S, |k i * (riemannXiDivisorZeroValue p).im| + H ≤ A)
    (hA : ∀ i ∈ S, k i * (riemannXiDivisorZeroValue p).im ≠ 0 →
      10 ^ 9 ≤ |k i * (riemannXiDivisorZeroValue p).im| + H) :
    0 ≤ (∑ i ∈ S, a i * kadiriPoleMajorant θ η z σ
        (k i * (riemannXiDivisorZeroValue p).im)) -
      a j * ((finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
          ((σ - (riemannXiDivisorZeroValue p).re : ℝ) : ℂ)).re -
        kadiriRetainedPairError θ η η₀ σ₀ κ δ) +
      kadiriOuterError θ η κ σ₀ z / 2 *
        (∑ i ∈ S, a i * xiLehmanTailMajorant (k i * (riemannXiDivisorZeroValue p).im) H) +
      kadiriWeight θ η 0 * (∑ i ∈ S, a i * smoothedGammaFactorMajorant κ σ
        (k i * (riemannXiDivisorZeroValue p).im)) +
      (∑ i ∈ S, a i) * ((1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4) :=
  kadiriWeight_initial_region_master_nonneg
    hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut
    S a k ha j hj hk p hβ hηρ hpoly hσA hharm hA

end PrimeFactorUnimodality.Tests
