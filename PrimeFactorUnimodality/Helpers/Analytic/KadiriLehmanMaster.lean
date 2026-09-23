import PrimeFactorUnimodality.Helpers.Analytic.KadiriPoleBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriTailMaster
import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanBudget

/-! # The weighted master with proved pole and zero-tail bounds

Insert the unconditional Lehman majorant into the actual distinguished-zero
master, and bound its pole contribution using correlation positivity and
the weighted transform error. The zero harmonic retains a finite low reciprocal mass
and the unshifted real transform; nonzero harmonics have explicit bounds.
Outer-zero separation, numerical parameter inequalities, and the smoothed
Gamma estimates remain distinct obligations.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The actual master with all pole terms and infinite height-tail sums bounded. -/
theorem kadiriWeight_lehman_pole_master_nonneg {θ η η₀ σ₀ σ δ κ z H : ℝ}
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
      kadiriWeight θ η 0 * (∑ i ∈ S, a i * smoothedGammaFactorDifference κ δ
        ((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I)) +
      ∑ i ∈ S, a i * smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
        (kadiriWeightSupport θ η) κ δ
        ((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I) := by
  have hm := kadiriWeight_tail_master_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₁ hκ₂ hκ₃
    hc hz hH hgap hcut S a k ha j hj hk p hβ hβσ hηρ hpoly hfar
  have ht := sum_xiHeightTail_le_lehmanMajorant S a k ha hH hA
  have he := mul_le_mul_of_nonneg_left ht
    (div_nonneg (kadiriOuterError_nonneg hθ hη hκ hσ₀ (z := z)) (by norm_num : (0 : ℝ) ≤ 2))
  have hp := sum_kadiriWeight_pole_le_majorant hθ hη hκ hσ₁
    (by linarith : 0 ≤ σ - 1 + δ) hz S a k ha
    (riemannXiDivisorZeroValue p).im
  linarith only [hm, he, hp]

end

end PrimeFactorUnimodality
