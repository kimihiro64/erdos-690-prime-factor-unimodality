import PrimeFactorUnimodality.Helpers.Analytic.KadiriStechkin
import PrimeFactorUnimodality.Helpers.Analytic.KadiriZeroSums

/-! # The smoothed master inequality after central-zero elimination

Insert the actual multiplicity-counted zero comparison into the paper-weight
master inequality. The remaining zero term is precisely the outer-strip
series. Pole terms, gamma factors, and boundary remainders remain exact;
their quantitative estimates are separate obligations.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The actual master inequality with only outer-strip zeros left to estimate. -/
theorem kadiriWeight_outer_master_nonneg {θ η η₀ σ₀ σ δ κ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 < δ)
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    {ι : Type*} (S : Finset ι) (a k : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (t : ℝ)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos (k i * u)) :
    0 ≤ (∑ i ∈ S, a i * smoothedLaplaceDifference (kadiriWeight θ η)
        (kadiriWeightSupport θ η) κ δ (((σ : ℂ) + (k i * t : ℝ) * I) - 1)) -
      (∑ i ∈ S, a i * ∑' p : {p : RiemannXiDivisorZeroIndex //
          ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue p.1)) +
      kadiriWeight θ η 0 * (∑ i ∈ S, a i * smoothedGammaFactorDifference κ δ
        ((σ : ℂ) + (k i * t : ℝ) * I)) +
      ∑ i ∈ S, a i * smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
        (kadiriWeightSupport θ η) κ δ ((σ : ℂ) + (k i * t : ℝ) * I) := by
  have hm := kadiriWeight_master_nonneg hθ hη S a k (hσ₀.trans_le hσ) hδ.le hκ₁ t hpoly
  have hz := Summable.tsum_finsetSum (s := S) (fun i _ =>
    (summable_kadiriWeight_zero_difference hθ hη κ δ
      ((σ : ℂ) + (k i * t : ℝ) * I)).mul_left (a i))
  simp_rw [tsum_mul_left] at hz
  rw [hz] at hm
  have hb := kadiriWeight_weighted_outer_zero_sum_le
    hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ S a k ha t
  linarith

end

end PrimeFactorUnimodality
