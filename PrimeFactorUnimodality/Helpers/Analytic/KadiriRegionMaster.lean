import PrimeFactorUnimodality.Helpers.Analytic.KadiriExplicitMaster
import PrimeFactorUnimodality.Helpers.Analytic.KadiriOuterSeparation

/-! # The smoothed master for successive proved zero-free regions

The high-region parameter is arbitrary and must be supplied by a proved
previous stage. Low-height data is kept separate. The existing separation
argument discharges both the outer cutoff and the distinguished zero's
upper strip bound; no numerical region is asserted by this generalization.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- Any established region supplies the two separation inputs to the explicit master. -/
theorem kadiriWeight_region_master_nonneg {θ η η₀ σ₀ σ δ κ z H A R T : ℝ}
    (hR : 0 < R) (hT : 1 < T)
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
    (hσA : 1 - 1 / (R * Real.log A) ≤ σ)
    (hlow : ∀ q : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue q).im| < T → (riemannXiDivisorZeroValue q).re ≤ σ)
    (hhigh : ∀ q : RiemannXiDivisorZeroIndex,
      T ≤ |(riemannXiDivisorZeroValue q).im| →
        1 / (R * Real.log |(riemannXiDivisorZeroValue q).im|) ≤
          1 - (riemannXiDivisorZeroValue q).re)
    (hharm : ∀ i ∈ S, |k i * (riemannXiDivisorZeroValue p).im| + H ≤ A)
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
  have hsep := kadiri_outer_separation_of_region hR hT hσA hlow hhigh
  have hβσ : (riemannXiDivisorZeroValue p).re ≤ σ := by
    have hh := hharm j hj
    rw [hk, one_mul] at hh
    by_contra hn
    have hhsep := hsep p (fun hp => hn hp.2)
    linarith
  exact kadiriWeight_explicit_master_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₁ hκ₂ hκ₃
    hc hz hH hgap hcut S a k ha j hj hk p hβ hβσ hηρ hpoly
    (fun i hi q hq => (hharm i hi).trans (hsep q hq)) hA

end

end PrimeFactorUnimodality
