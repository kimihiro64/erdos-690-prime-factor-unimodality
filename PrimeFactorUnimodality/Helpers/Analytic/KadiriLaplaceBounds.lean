import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeBound
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Bounds

/-! # Explicit transform error for the actual compact paper weight

The sharp second-derivative bound and two integrations by parts give the
paper's cubic-in-eta transform error on the right half-plane. The weight,
support, and error constant are all the proved trigonometric ones.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The complex pole-subtracted transform has the explicit sharp derivative constant. -/
theorem norm_kadiriWeight_laplace_sub_pole_le {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ} (hs : 0 < s.re) :
    ‖finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s -
      (kadiriWeight θ η 0 : ℂ) / s‖ ≤
        η ^ 3 * (-kadiriKernel₂ θ 0) / (s.re * ‖s‖ ^ 2) := by
  exact norm_finiteLaplace_sub_pole_le_div_re
    (f := fun u => (kadiriWeight θ η u : ℂ))
    (g := fun u => (kadiriWeight₁ θ η u : ℂ))
    (h := fun u => (kadiriWeight₂ θ η u : ℂ))
    (kadiriWeightSupport_pos hθ hη).le
    (mul_nonneg (pow_nonneg hη.le 3) (neg_kadiriKernel₂_zero_nonneg hθ))
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_kadiriWeight θ η))
    (Complex.continuous_ofReal.comp (continuous_kadiriWeight₁ θ η)).continuousOn
    (Complex.continuous_ofReal.comp (continuous_kadiriWeight₂ θ η)).continuousOn
    (fun u hu => (hasDerivAt_kadiriWeight hu).ofReal_comp)
    (fun u _ => (hasDerivAt_kadiriWeight₁ θ η u).ofReal_comp)
    (by rw [kadiriWeight_support hθ hη, ofReal_zero])
    (by rw [kadiriWeight₁_zero hθ, ofReal_zero])
    (by rw [kadiriWeight₁_support hθ hη, ofReal_zero])
    (fun _ hu => norm_kadiriWeight₂_le hθ hη hu) hs

/-- The real transform differs from its pole term by at most the explicit cubic error. -/
theorem abs_re_kadiriWeight_laplace_sub_pole_le {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ} (hs : 0 < s.re) :
    |(finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re -
      kadiriWeight θ η 0 * s.re / (s.re ^ 2 + s.im ^ 2)| ≤
        η ^ 3 * (-kadiriKernel₂ θ 0) / (s.re * (s.re ^ 2 + s.im ^ 2)) := by
  have h := (abs_re_le_norm _).trans (norm_kadiriWeight_laplace_sub_pole_le hθ hη hs)
  simpa only [sub_re, div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero,
    normSq_apply, ← sq, ← normSq_eq_norm_sq] using h

end

end PrimeFactorUnimodality
