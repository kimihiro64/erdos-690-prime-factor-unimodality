import PrimeFactorUnimodality.Helpers.Analytic.KadiriGammaRemainderBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriLehmanMaster
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaFactorBounds

/-! # The actual smoothed master with all analytic error terms bounded

Substitute the proved logarithmic Gamma factor and uniform cubic remainder
into the pole/Lehman master. The resulting inequality contains only the
explicit transforms, weighted derivative mass, finite low-zero subtraction,
and elementary majorants. Separation and numerical parameter verification
remain hypotheses; this is not yet the numerical zero-free-region theorem.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- Every pole, zero-tail, and Gamma contribution has its proved explicit majorant. -/
theorem kadiriWeight_explicit_master_nonneg {θ η η₀ σ₀ σ δ κ z H : ℝ}
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
        |k i * (riemannXiDivisorZeroValue p).im| + H ≤ |(riemannXiDivisorZeroValue q).im|)
    (hA : ∀ i ∈ S, k i * (riemannXiDivisorZeroValue p).im ≠ 0 →
      10 < |k i * (riemannXiDivisorZeroValue p).im| + H) :
    0 ≤ (∑ i ∈ S, a i * kadiriPoleMajorant θ η z σ
        (k i * (riemannXiDivisorZeroValue p).im)) -
      a j * ((finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
          ((σ - (riemannXiDivisorZeroValue p).re : ℝ) : ℂ)).re -
        kadiriRetainedPairError θ η η₀ σ₀ κ δ) +
      kadiriOuterError θ η κ σ₀ z / 2 *
        (∑ i ∈ S, a i * xiLehmanTailMajorant (k i * (riemannXiDivisorZeroValue p).im) H) +
      kadiriWeight θ η 0 * (∑ i ∈ S, a i * smoothedGammaFactorMajorant κ σ
        (k i * (riemannXiDivisorZeroValue p).im)) +
      (∑ i ∈ S, a i) * ((1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4) := by
  have hm := kadiriWeight_lehman_pole_master_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₁ hκ₂ hκ₃
    hc hz hH hgap hcut S a k ha j hj hk p hβ hβσ hηρ hpoly hfar hA
  have hf := sum_smoothedGammaFactorDifference_le hκ hκ₁ (by linarith : 0 ≤ δ)
    (by linarith : 0 ≤ σ) (by linarith : σ ≤ 2) S a k ha (riemannXiDivisorZeroValue p).im
  have hw := mul_le_mul_of_nonneg_left hf (kadiriWeight_nonneg hθ hη 0)
  have hr := sum_kadiriWeight_gammaRemainderDifference_le hθ hη hκ
    (by linarith : 0 ≤ δ) (hσ₀.trans_le hσ) S a k ha (riemannXiDivisorZeroValue p).im
  linarith only [hm, hw, hr]

end

end PrimeFactorUnimodality
