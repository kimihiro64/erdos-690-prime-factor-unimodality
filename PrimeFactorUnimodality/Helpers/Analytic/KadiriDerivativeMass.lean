import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeBound
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Bounds
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Scaling
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.WeightedBounds

/-! # The exact weighted second-derivative integral

This is `M(z,θ)` from Mossinghoff--Trudgian section 4,
<https://arxiv.org/pdf/1410.3926>, retaining the integral of the absolute
second derivative of the actual kernel. Its real-axis monotonicity and
the exact positive scaling connect it to the paper's transform remainder.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set

/-- The exact weighted second-derivative mass of the unscaled compact kernel. -/
def kadiriDerivativeMass (θ x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..kadiriSupport θ, |kadiriKernel₂ θ u| * Real.exp (-x * u)

/-- The weighted mass is exactly the real-axis transform of the absolute derivative. -/
theorem kadiriDerivativeMass_eq_re_finiteLaplace (θ x : ℝ) :
    kadiriDerivativeMass θ x =
      (finiteLaplace (fun u => ((|kadiriKernel₂ θ u| : ℝ) : ℂ)) (kadiriSupport θ) x).re := by
  rw [re_finiteLaplace_ofReal (continuous_kadiriKernel₂ θ).abs.continuousOn]
  simp only [kadiriDerivativeMass, mul_comm]

/-- The exact derivative mass is nonnegative at every real argument. -/
theorem kadiriDerivativeMass_nonneg {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (x : ℝ) :
    0 ≤ kadiriDerivativeMass θ x := by
  apply intervalIntegral.integral_nonneg (kadiriSupport_pos hθ).le
  intro u _
  exact mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)

/-- The derivative mass decreases along the entire real axis, including negative arguments. -/
theorem antitone_kadiriDerivativeMass {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) :
    Antitone (kadiriDerivativeMass θ) := by
  intro x y hxy
  rw [kadiriDerivativeMass_eq_re_finiteLaplace, kadiriDerivativeMass_eq_re_finiteLaplace]
  exact antitone_re_finiteLaplace (kadiriSupport_pos hθ).le
    (continuous_kadiriKernel₂ θ).abs.continuousOn (fun u _ => abs_nonneg _) hxy

/-- The mass bounds the transform of the signed second derivative on every vertical line. -/
theorem norm_kadiriKernel₂_laplace_le_mass {θ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (s : ℂ) :
    ‖finiteLaplace (fun u => (kadiriKernel₂ θ u : ℂ)) (kadiriSupport θ) s‖ ≤
      kadiriDerivativeMass θ s.re := by
  have h := norm_finiteLaplace_le_weighted_norm (kadiriSupport_pos hθ).le
    (f := fun u => (kadiriKernel₂ θ u : ℂ))
    (continuous_ofReal.comp (continuous_kadiriKernel₂ θ)).continuousOn s
  simpa only [kadiriDerivativeMass_eq_re_finiteLaplace, norm_real, Real.norm_eq_abs] using h

/-- The sharp pointwise derivative bound gives the usual positive-axis inverse bound. -/
theorem kadiriDerivativeMass_le_div {θ x : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hx : 0 < x) :
    kadiriDerivativeMass θ x ≤ (-kadiriKernel₂ θ 0) / x := by
  rw [kadiriDerivativeMass_eq_re_finiteLaplace]
  apply (re_le_norm _).trans
  exact norm_finiteLaplace_le_div_re (kadiriSupport_pos hθ).le
    (neg_kadiriKernel₂_zero_nonneg hθ) (fun u hu => by
      simpa only [norm_real, Real.norm_eq_abs, abs_abs] using
        abs_kadiriKernel₂_le_neg_zero hθ hu) hx

/-- Scaling the actual second derivative contributes exactly `η²` to its transform. -/
theorem finiteLaplace_kadiriWeight₂_rescale (θ : ℝ) {η : ℝ} (hη : η ≠ 0) (s : ℂ) :
    finiteLaplace (fun u => (kadiriWeight₂ θ η u : ℂ)) (kadiriWeightSupport θ η) s =
      (η : ℂ) ^ 2 * finiteLaplace (fun u => (kadiriKernel₂ θ u : ℂ))
        (kadiriSupport θ) (s / (η : ℂ)) := by
  have heq : (fun u => (kadiriWeight₂ θ η u : ℂ)) =
      (fun u => (η : ℂ) ^ 2 * ((η : ℂ) * (kadiriKernel₂ θ (η * u) : ℂ))) := by
    funext u
    simp only [kadiriWeight₂, ofReal_mul, ofReal_pow]
    ring
  rw [heq, finiteLaplace_const_mul, kadiriWeightSupport,
    finiteLaplace_rescale (fun u => (kadiriKernel₂ θ u : ℂ)) (kadiriSupport θ) s hη]

/-- The scaled derivative transform has the exact weighted-mass bound, at any complex point. -/
theorem norm_kadiriWeight₂_laplace_le_mass {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (s : ℂ) :
    ‖finiteLaplace (fun u => (kadiriWeight₂ θ η u : ℂ)) (kadiriWeightSupport θ η) s‖ ≤
      η ^ 2 * kadiriDerivativeMass θ (s.re / η) := by
  rw [finiteLaplace_kadiriWeight₂_rescale θ hη.ne' s, norm_mul, norm_pow,
    norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have h := norm_kadiriKernel₂_laplace_le_mass hθ (s / (η : ℂ))
  simpa only [div_ofReal_re] using mul_le_mul_of_nonneg_left h (sq_nonneg η)

end

end PrimeFactorUnimodality
