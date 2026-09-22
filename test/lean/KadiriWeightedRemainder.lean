import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeMoments
import PrimeFactorUnimodality.Helpers.Analytic.KadiriOuterPairRemainder

/-! # Weighted remainder and moment regressions

Cover arbitrary complex sources, negative rescaling, the imaginary axis,
the cubic exponential comparison with a discharged endpoint, and the
directions of moment bounds for nonpositive transform arguments.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real

example {f : ℝ → ℂ} {d : ℝ} (hd : 0 ≤ d) (hf : ContinuousOn f (Set.Icc 0 d)) (s : ℂ) :
    ‖finiteLaplace f d s‖ ≤ (finiteLaplace (fun u => (‖f u‖ : ℂ)) d (s.re : ℂ)).re :=
  norm_finiteLaplace_le_weighted_norm hd hf s

example (θ : ℝ) (s : ℂ) :
    finiteLaplace (fun u => (kadiriWeight₂ θ (-1) u : ℂ)) (kadiriWeightSupport θ (-1)) s =
      finiteLaplace (fun u => (kadiriKernel₂ θ u : ℂ)) (kadiriSupport θ) (-s) := by
  simpa [div_neg] using finiteLaplace_kadiriWeight₂_rescale θ (η := -1) (by norm_num) s

example (θ : ℝ) : kadiriDerivativeMass θ 0 = kadiriDerivativeMoment θ 0 := by
  simp [kadiriDerivativeMass, kadiriDerivativeMoment]

example {x : ℝ} (hx : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + (1 / 2) * x ^ 3 := by
  apply Real.exp_le_cubic_of_endpoint zero_lt_one hx hx₁
  convert Real.exp_one_lt_three.le using 1
  norm_num

example {θ η t : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (ht : t ≠ 0) :
    |(finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
      ((t : ℂ) * I)).re| ≤ η ^ 2 * kadiriDerivativeMass θ 0 / t ^ 2 := by
  simpa using abs_re_kadiriWeight_laplace_sub_pole_le_mass_im hθ hη
    (s := (t : ℂ) * I) (z := 0) (by simp) (by simpa using ht)

example {θ z B₀ B₁ B₂ B₃ : ℝ} (hz : z ≤ 0)
    (h₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (h₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (h₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (h₃ : kadiriDerivativeMoment θ 3 ≤ B₃) :
    kadiriDerivativeMassMajorant θ z ≤
      B₀ - B₁ * z + B₂ * z ^ 2 / 2 - B₃ * z ^ 3 / (345 / 100) :=
  kadiriDerivativeMassMajorant_le_of_moment_bounds hz h₀ h₁ h₂ h₃

example {θ η σ β κ δ a z y : ℝ}
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
          (((σ - 1 + β : ℝ) : ℂ) + (y : ℂ) * I) :=
  kadiriWeight_outer_pair_remainder_lower_bound hθ hη hκ ha hz hy ha₁ ha₂ ha₃

end

end PrimeFactorUnimodality.Tests
