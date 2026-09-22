import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeBound
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightPositivity
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # The smoothed Stechkin inequality for the actual paper weight

All weight-side hypotheses, including global nonnegativity, are proved
for the paper's trigonometric kernel. The remaining hypotheses describe
only the parameters and the nonnegative trigonometric polynomial.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The paper-weight master inequality, with no assumed regularity or positivity facts. -/
theorem kadiriWeight_master_nonneg {θ η : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    {ι : Type*} (S : Finset ι) (a k : ι → ℝ)
    {σ κ δ : ℝ} (hσ : 1 / 2 < σ) (hδ : 0 ≤ δ) (hκ : κ ≤ 1) (t : ℝ)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos (k i * u)) :
    0 ≤ (∑ i ∈ S, a i * smoothedLaplaceDifference (kadiriWeight θ η)
        (kadiriWeightSupport θ η) κ δ (((σ : ℂ) + (k i * t : ℝ) * I) - 1)) -
      (∑' p : RiemannXiDivisorZeroIndex, ∑ i ∈ S, a i *
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue p)) +
      kadiriWeight θ η 0 * (∑ i ∈ S, a i * smoothedGammaFactorDifference κ δ
        ((σ : ℂ) + (k i * t : ℝ) * I)) +
      ∑ i ∈ S, a i * smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
        (kadiriWeightSupport θ η) κ δ ((σ : ℂ) + (k i * t : ℝ) * I) := by
  exact smoothedStechkin_master_nonneg
    (g := fun u => (kadiriWeight₁ θ η u : ℂ)) (M := η ^ 3 * (-kadiriKernel₂ θ 0))
    (kadiriWeightSupport_pos hθ hη).le
    (mul_nonneg (pow_nonneg hη.le 3) (neg_kadiriKernel₂_zero_nonneg hθ))
    (continuousOn_kadiriWeight θ η)
    (Complex.continuous_ofReal.comp (continuous_kadiriWeight₁ θ η)).continuousOn
    (Complex.continuous_ofReal.comp (continuous_kadiriWeight₂ θ η)).continuousOn
    (fun u hu => (hasDerivAt_kadiriWeight hu).ofReal_comp)
    (fun u _ => (hasDerivAt_kadiriWeight₁ θ η u).ofReal_comp)
    (kadiriWeight_support hθ hη)
    (by rw [kadiriWeight₁_zero hθ, ofReal_zero])
    (by rw [kadiriWeight₁_support hθ hη, ofReal_zero])
    (fun _ hu => norm_kadiriWeight₂_le hθ hη hu) S a k
    (kadiriWeight_tail θ η) (fun u _ => kadiriWeight_nonneg hθ hη u) hσ hδ hκ t hpoly

end

end PrimeFactorUnimodality
