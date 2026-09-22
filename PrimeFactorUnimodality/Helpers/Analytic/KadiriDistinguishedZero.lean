import PrimeFactorUnimodality.Helpers.Analytic.KadiriRetainedBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriRetainedMaster

/-! # The quantitative distinguished-zero contribution in the actual master inequality

Set the scale to `η=1-Re(ρ)` and select the harmonic with frequency one.
The proved retained-pair estimate leaves its main transform minus the exact
linear/cubic error. All other central pairs have already been discarded
legitimately; the outer-strip sum remains, rather than being assumed small.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

variable {θ η η₀ σ₀ σ δ κ : ℝ}
  (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
  (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
  (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
  (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
  (hc : 0 < σ₀ - η₀ + δ)
  {ι : Type*} (S : Finset ι) (a k : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i)
  (j : ι) (hj : j ∈ S) (hk : k j = 1) (p : RiemannXiDivisorZeroIndex)
  (hβ : 1 / 2 < (riemannXiDivisorZeroValue p).re)
  (hβσ : (riemannXiDivisorZeroValue p).re ≤ σ)
  (hηρ : η = 1 - (riemannXiDivisorZeroValue p).re)

include hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ hc ha hj hk hβ hβσ hηρ

/-- The actual weighted zero sum retains the distinguished transform with an explicit error. -/
theorem kadiriWeight_distinguished_zero_sum_lower_bound :
    a j * ((finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
        ((σ - (riemannXiDivisorZeroValue p).re : ℝ) : ℂ)).re -
      kadiriRetainedPairError θ η η₀ σ₀ κ δ) +
      (∑ i ∈ S, a i * ∑' q : {q : RiemannXiDivisorZeroIndex //
          ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue q)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I) -
            riemannXiDivisorZeroValue q.1)) ≤
      ∑ i ∈ S, a i * ∑' q : RiemannXiDivisorZeroIndex,
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I) -
            riemannXiDivisorZeroValue q) := by
  have hp : kadiriCentralStrip σ (riemannXiDivisorZeroValue p) := ⟨by linarith, hβσ⟩
  have hb := kadiriWeight_retained_pair_at_height_lower_bound hθ hη hσ hσ₁
    (ρ := riemannXiDivisorZeroValue p) (by linarith) hβσ hδ hc hκ
  have hret := kadiriWeight_weighted_retained_pair_add_outer_le
    hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ S a k ha j hj p hp (ne_of_gt hβ)
    (riemannXiDivisorZeroValue p).im
  simp only [hk, one_mul] at hret
  have hw := mul_le_mul_of_nonneg_left hb (ha j hj)
  linarith

/-- The master inequality with the distinguished transform and its polynomial error explicit. -/
theorem kadiriWeight_distinguished_master_nonneg (hκ₁ : κ ≤ 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos (k i * u)) :
    0 ≤ (∑ i ∈ S, a i * smoothedLaplaceDifference (kadiriWeight θ η)
        (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I) - 1)) -
      a j * ((finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
          ((σ - (riemannXiDivisorZeroValue p).re : ℝ) : ℂ)).re -
        kadiriRetainedPairError θ η η₀ σ₀ κ δ) -
      (∑ i ∈ S, a i * ∑' q : {q : RiemannXiDivisorZeroIndex //
          ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue q)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I) -
            riemannXiDivisorZeroValue q.1)) +
      kadiriWeight θ η 0 * (∑ i ∈ S, a i * smoothedGammaFactorDifference κ δ
        ((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I)) +
      ∑ i ∈ S, a i * smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
        (kadiriWeightSupport θ η) κ δ
        ((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I) := by
  have hm := kadiriWeight_master_nonneg hθ hη S a k (hσ₀.trans_le hσ) hδ.le hκ₁
    (riemannXiDivisorZeroValue p).im hpoly
  have hz := Summable.tsum_finsetSum (s := S) (fun i _ =>
    (summable_kadiriWeight_zero_difference hθ hη κ δ
      ((σ : ℂ) + (k i * (riemannXiDivisorZeroValue p).im : ℝ) * I)).mul_left (a i))
  simp_rw [tsum_mul_left] at hz
  rw [hz] at hm
  have hb := kadiriWeight_distinguished_zero_sum_lower_bound
    hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ hc S a k ha j hj hk p hβ hβσ hηρ
  linarith

end

end PrimeFactorUnimodality
