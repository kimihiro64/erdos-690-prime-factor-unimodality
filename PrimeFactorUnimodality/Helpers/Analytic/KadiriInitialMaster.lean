import PrimeFactorUnimodality.Helpers.Analytic.KadiriRegionMaster
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeBounded

/-! # The actual smoothed master with proved separation at every height

The bounded-strip and high-height initial regions discharge the former
outer-zero separation hypothesis at every harmonic. No low-height,
high-height, or zero-counting premise remains. The final numerical
improvement of the initial constant is still a separate obligation.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The proved initial region supplies the separation in the actual explicit master. -/
theorem kadiriWeight_initial_region_master_nonneg {θ η η₀ σ₀ σ δ κ z H A : ℝ}
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
      (∑ i ∈ S, a i) * ((1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4) := by
  have hjne : k j * (riemannXiDivisorZeroValue p).im ≠ 0 := by
    rw [hk, one_mul]
    exact abs_pos.mp (lt_trans zero_lt_one (one_lt_abs_im_xi_divisor p))
  have hA' : 10 ^ 9 ≤ A := (hA j hj hjne).trans (hharm j hj)
  have hlow (q : RiemannXiDivisorZeroIndex)
      (hq : |(riemannXiDivisorZeroValue q).im| < 10 ^ 9) :
      (riemannXiDivisorZeroValue q).re ≤ σ := by
    have hg := xi_zero_gap_bounded hA' (riemannXiDivisorZeroValue_eq_zero q)
      (hq.le.trans hA')
    linarith
  exact kadiriWeight_region_master_nonneg (by norm_num) (by norm_num)
    hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₁ hκ₂ hκ₃
    hc hz hH hgap hcut S a k ha j hj hk p hβ hηρ hpoly hσA hlow
    (fun q hq => xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero q) hq) hharm
    (fun i hi ht => by have h := hA i hi ht; linarith)

end

end PrimeFactorUnimodality
