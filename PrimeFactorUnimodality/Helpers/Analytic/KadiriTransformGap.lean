import PrimeFactorUnimodality.Helpers.Analytic.KadiriLaplacePositivity
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Monotonicity

/-! # The retained transform minus the zero-harmonic pole

The exact positive rescaling identifies this difference with `K(w,theta)`
in Mossinghoff--Trudgian, equation (2.2), where `w=(1-sigma)/eta`.
The zero harmonic is retained, not estimated separately, and no sign
condition on the integrand or monotonicity of `K` is assumed.
Source: <https://arxiv.org/pdf/1410.3926>, section 2.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real MeasureTheory Set

/-- The exact real integral governing the zero-free-region improvement. -/
def kadiriTransformGap (θ a₀ a₁ w : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..kadiriSupport θ,
    (a₁ * Real.exp (-u) - a₀) * kadiriKernel θ u * Real.exp (w * u)

/-- The paper's integral is precisely a difference of two unscaled Laplace transforms. -/
theorem kadiriTransformGap_eq_laplace (θ a₀ a₁ w : ℝ) :
    kadiriTransformGap θ a₀ a₁ w =
      a₁ * (finiteLaplace (fun u => (kadiriKernel θ u : ℂ)) (kadiriSupport θ)
        ((1 - w : ℝ) : ℂ)).re -
      a₀ * (finiteLaplace (fun u => (kadiriKernel θ u : ℂ)) (kadiriSupport θ)
        ((-w : ℝ) : ℂ)).re := by
  have hi (x : ℝ) : IntervalIntegrable
      (fun u => Real.exp (-x * u) * kadiriKernel θ u) volume 0 (kadiriSupport θ) :=
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-x * u))).mul
      (continuous_kadiriKernel θ)).intervalIntegrable 0 _
  rw [re_finiteLaplace_ofReal (continuous_kadiriKernel θ).continuousOn,
    re_finiteLaplace_ofReal (continuous_kadiriKernel θ).continuousOn,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hi (1 - w)).const_mul a₁) ((hi (-w)).const_mul a₀)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [show -(1 - w) * u = -u + w * u by ring, Real.exp_add]
  simp only [neg_neg]
  ring

/-- The actual scaled weight yields the same integral with no residual scale factor. -/
theorem kadiriWeight_transform_gap_eq {θ η σ β : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hηβ : η = 1 - β) (a₀ a₁ : ℝ) :
    a₁ * (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
        ((σ - β : ℝ) : ℂ)).re -
      a₀ * (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
        ((σ - 1 : ℝ) : ℂ)).re =
      kadiriTransformGap θ a₀ a₁ ((1 - σ) / η) := by
  rw [kadiriWeight_laplace_eq_rescale hθ hη, kadiriWeight_laplace_eq_rescale hθ hη,
    kadiriTransformGap_eq_laplace]
  have h₁ : ((σ - β : ℝ) : ℂ) / (η : ℂ) = ((1 - (1 - σ) / η : ℝ) : ℂ) := by
    rw [← ofReal_div]
    congr 1
    field_simp
    linarith
  have h₀ : ((σ - 1 : ℝ) : ℂ) / (η : ℂ) = ((-((1 - σ) / η) : ℝ) : ℂ) := by
    rw [← ofReal_div]
    congr 1
    ring
  rw [h₁, h₀]

/-- The normalized parameter lies in the closed unit interval for the working strip. -/
theorem kadiri_normalized_gap_mem_Icc {η σ β : ℝ}
    (hη : 0 < η) (hηβ : η = 1 - β) (hβσ : β ≤ σ) (hσ : σ ≤ 1) :
    (1 - σ) / η ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hσ) hη.le
  · apply (div_le_iff₀ hη).mpr
    linarith

end

end PrimeFactorUnimodality
