import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeBound
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedRealExplicitFormula

/-! # The proved explicit formula instantiated with the actual paper weight

All regularity, support, derivative-bound, and endpoint conditions are
discharged for the trigonometric weight, for every admissible `theta` and
positive scale `eta`. This is not a conditional weight interface: its only
hypotheses are those parameter ranges and `Re(s)>1/2`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The complete explicit formula for the actual compact trigonometric weight. -/
theorem kadiriWeight_explicitFormula {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ} (hs : 1 / 2 < s.re) :
    (smoothedVonMangoldt (kadiriWeight θ η) s).re =
      (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) (s - 1)).re -
      (∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
          (s - riemannXiDivisorZeroValue p)).re) +
      kadiriWeight θ η 0 *
        (-(1 / 2 : ℝ) * Real.log Real.pi + (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re) +
      (smoothedGammaRemainder (fun u => (kadiriWeight₂ θ η u : ℂ))
        (kadiriWeightSupport θ η) s).re := by
  apply re_smoothedVonMangoldt_explicitFormula
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
    (fun _ hu => norm_kadiriWeight₂_le hθ hη hu) (kadiriWeight_tail θ η) hs

end

end PrimeFactorUnimodality
