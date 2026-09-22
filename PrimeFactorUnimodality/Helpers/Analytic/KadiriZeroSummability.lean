import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeBound
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # Absolute zero summability for the actual paper weight

The compact weight's proved regularity and sharp second-derivative bound
discharge the generic summability hypotheses, at every complex parameter.
This supplies legitimate reindexing and splitting of the actual xi divisor
series, including its multiplicities.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The actual shifted weight contributions are summable over the complete xi divisor. -/
theorem summable_kadiriWeight_zero_difference {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (κ δ : ℝ) (s : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (s - riemannXiDivisorZeroValue p)) := by
  exact summable_smoothedLaplaceDifference_zeros
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
    (fun _ hu => norm_kadiriWeight₂_le hθ hη hu) κ δ s

end

end PrimeFactorUnimodality
