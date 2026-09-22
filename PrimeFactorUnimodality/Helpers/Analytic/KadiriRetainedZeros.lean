import PrimeFactorUnimodality.Helpers.Analytic.KadiriZeroSums

/-! # Retaining a distinguished zero pair at one harmonic

The other central-strip contributions remain nonnegative, including the
other harmonics. A finite-subsum bound retains the selected coefficient
times one actual off-critical pair without discarding the outer-strip sum.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real
open scoped ComplexConjugate

/-- Retain one zero pair at any selected harmonic of a nonnegatively weighted sum. -/
theorem kadiriWeight_weighted_retained_pair_add_outer_le {θ η η₀ σ₀ σ δ κ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    {ι : Type*} (S : Finset ι) (a k : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i)
    (j : ι) (hj : j ∈ S) (p : RiemannXiDivisorZeroIndex)
    (hp : kadiriCentralStrip σ (riemannXiDivisorZeroValue p))
    (hne : (riemannXiDivisorZeroValue p).re ≠ 1 / 2) (t : ℝ) :
    a j * (smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (k j * t : ℝ) * I) - riemannXiDivisorZeroValue p) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (k j * t : ℝ) * I) - (1 - conj (riemannXiDivisorZeroValue p)))) +
      (∑ i ∈ S, a i * ∑' q : {q : RiemannXiDivisorZeroIndex //
          ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue q)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue q.1)) ≤
      ∑ i ∈ S, a i * ∑' q : RiemannXiDivisorZeroIndex,
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue q) := by
  let Z (i : ι) := ∑' q : RiemannXiDivisorZeroIndex,
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
      (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue q)
  let O (i : ι) := ∑' q : {q : RiemannXiDivisorZeroIndex //
      ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue q)},
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
      (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue q.1)
  have hgap (i : ι) (hi : i ∈ S) : 0 ≤ a i * (Z i - O i) :=
    mul_nonneg (ha i hi) (sub_nonneg.mpr
      (kadiriWeight_outer_zero_sum_le hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ (k i * t)))
  have hsingle := Finset.single_le_sum hgap hj
  simp_rw [mul_sub] at hsingle
  rw [Finset.sum_sub_distrib] at hsingle
  have hpair := mul_le_mul_of_nonneg_left
    (kadiriWeight_retained_pair_add_outer_le hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃
      p hp hne (k j * t)) (ha j hj)
  dsimp only [Z, O] at hsingle
  linarith

end

end PrimeFactorUnimodality
