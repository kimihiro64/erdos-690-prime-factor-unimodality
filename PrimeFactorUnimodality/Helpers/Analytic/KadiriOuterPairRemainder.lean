import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightedRemainder
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # The four transform errors in an outer zero pair

Combine the weighted error for `σ-β` with cubic errors for the other three
arguments. This is the pointwise remainder calculation in Kadiri (49),
retaining the rational four-kernel term explicitly. Its sign is a separate
inside-strip comparison; no right-half-plane Stechkin theorem is applied
outside its domain.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The exact rational contribution minus the paper's weighted/cubic error bounds the pair. -/
theorem kadiriWeight_outer_pair_remainder_lower_bound {θ η σ β κ δ a z y : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hz : z ≤ (σ - β) / η) (hy : y ≠ 0)
    (ha₁ : a ≤ σ - 1 + β) (ha₂ : a ≤ σ - β + δ) (ha₃ : a ≤ σ - 1 + β + δ) :
    kadiriWeight θ η 0 *
        (Real.stechkinPair σ β y - κ * Real.stechkinPair (σ + δ) β y) -
      (η ^ 2 * kadiriDerivativeMass θ z +
        (1 + 2 * κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / a) / y ^ 2 ≤
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ - β : ℝ) : ℂ) + (y : ℂ) * I) +
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ - 1 + β : ℝ) : ℂ) + (y : ℂ) * I) := by
  let F (x : ℝ) := (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
    (kadiriWeightSupport θ η) ((x : ℂ) + (y : ℂ) * I)).re
  let K (x : ℝ) := x / (x ^ 2 + y ^ 2)
  have h₀ : |F (σ - β) - kadiriWeight θ η 0 * K (σ - β)| ≤
      η ^ 2 * kadiriDerivativeMass θ z / y ^ 2 := by
    simpa [F, K, mul_div_assoc] using abs_re_kadiriWeight_laplace_sub_pole_le_mass_im
      hθ hη (s := ((σ - β : ℝ) : ℂ) + (y : ℂ) * I) (by simpa using hz) (by simpa using hy)
  have hb (x : ℝ) (hx : a ≤ x) : |F x - kadiriWeight θ η 0 * K x| ≤
      η ^ 3 * (-kadiriKernel₂ θ 0) / (a * y ^ 2) := by
    simpa [F, K, mul_div_assoc] using abs_re_kadiriWeight_laplace_sub_pole_le_cubic_im
      hθ hη ha (s := (x : ℂ) + (y : ℂ) * I) (by simpa using hx) (by simpa using hy)
  have h₁ := (abs_le.mp (hb (σ - 1 + β) ha₁)).1
  have h₂ := mul_le_mul_of_nonneg_left (abs_le.mp (hb (σ - β + δ) ha₂)).2 hκ
  have h₃ := mul_le_mul_of_nonneg_left (abs_le.mp (hb (σ - 1 + β + δ) ha₃)).2 hκ
  have h₀' := (abs_le.mp h₀).1
  have hshift (x : ℝ) : ((x : ℂ) + (y : ℂ) * I) + (δ : ℂ) =
      ((x + δ : ℝ) : ℂ) + (y : ℂ) * I := by push_cast; ring
  simp only [smoothedLaplaceDifference, hshift, Real.stechkinPair,
    show σ + δ - β = σ - β + δ by ring,
    show σ + δ - 1 + β = σ - 1 + β + δ by ring]
  change kadiriWeight θ η 0 *
      (K (σ - β) + K (σ - 1 + β) - κ * (K (σ - β + δ) + K (σ - 1 + β + δ))) -
      (η ^ 2 * kadiriDerivativeMass θ z +
        (1 + 2 * κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / a) / y ^ 2 ≤
    F (σ - β) - κ * F (σ - β + δ) + (F (σ - 1 + β) - κ * F (σ - 1 + β + δ))
  simp only [div_eq_mul_inv, mul_inv_rev] at h₀' h₁ h₂ h₃ ⊢
  nlinarith only [h₀', h₁, h₂, h₃]

end

end PrimeFactorUnimodality
