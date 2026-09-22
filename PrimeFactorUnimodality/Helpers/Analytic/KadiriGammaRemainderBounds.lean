import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeBound
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaBounds
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # The actual paper weight's cubic Gamma error

The sharp derivative bound supplies the explicit constant in the uniform
Gamma remainder estimate. Nonnegative shifts and polynomial coefficients
preserve it, including at the zero harmonic and arbitrary signed heights.
The Gamma factor multiplying the endpoint weight is a separate term.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The compact weight's actual Gamma remainder has a uniform cubic bound. -/
theorem norm_kadiriWeight_gammaRemainder_le {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖smoothedGammaRemainder (fun u => (kadiriWeight₂ θ η u : ℂ))
      (kadiriWeightSupport θ η) s‖ ≤ η ^ 3 * (-kadiriKernel₂ θ 0) / 4 := by
  exact norm_smoothedGammaRemainder_le_quarter
    (f := fun u => (kadiriWeight θ η u : ℂ))
    (g := fun u => (kadiriWeight₁ θ η u : ℂ))
    (kadiriWeightSupport_pos hθ hη).le
    (mul_nonneg (pow_nonneg hη.le 3) (neg_kadiriKernel₂_zero_nonneg hθ))
    (continuous_ofReal.comp_continuousOn (continuousOn_kadiriWeight θ η))
    (continuous_ofReal.comp (continuous_kadiriWeight₁ θ η)).continuousOn
    (continuous_ofReal.comp (continuous_kadiriWeight₂ θ η)).continuousOn
    (fun u hu => (hasDerivAt_kadiriWeight hu).ofReal_comp)
    (fun u _ => (hasDerivAt_kadiriWeight₁ θ η u).ofReal_comp)
    (by rw [kadiriWeight_support hθ hη, ofReal_zero])
    (by rw [kadiriWeight₁_zero hθ, ofReal_zero])
    (by rw [kadiriWeight₁_support hθ hη, ofReal_zero])
    (fun _ hu => norm_kadiriWeight₂_le hθ hη hu) hs

/-- The shifted real remainder retains a fully explicit cubic coefficient. -/
theorem abs_kadiriWeight_gammaRemainderDifference_le {θ η κ δ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    |smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
      (kadiriWeightSupport θ η) κ δ s| ≤ (1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4 := by
  have h₀ := (abs_re_le_norm _).trans (norm_kadiriWeight_gammaRemainder_le hθ hη hs)
  have h₁ := (abs_re_le_norm _).trans (norm_kadiriWeight_gammaRemainder_le hθ hη
    (s := s + (δ : ℂ)) (by simp only [add_re, ofReal_re]; linarith))
  unfold smoothedGammaRemainderDifference
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg hκ]
  have h := add_le_add h₀ (mul_le_mul_of_nonneg_left h₁ hκ)
  exact h.trans_eq (by ring)

/-- Every harmonic is controlled by the same cubic bound before summing the coefficients. -/
theorem sum_kadiriWeight_gammaRemainderDifference_le {θ η κ δ σ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (hσ : 1 / 2 < σ) {ι : Type*} (S : Finset ι) (a k : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (t : ℝ) :
    (∑ i ∈ S, a i * smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
      (kadiriWeightSupport θ η) κ δ ((σ : ℂ) + (k i * t : ℝ) * I)) ≤
      (∑ i ∈ S, a i) * ((1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (ha i hi)
  exact (le_abs_self _).trans
    (abs_kadiriWeight_gammaRemainderDifference_le hθ hη hκ hδ (by simpa using hσ))

end

end PrimeFactorUnimodality
