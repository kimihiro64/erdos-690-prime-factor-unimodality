import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightExplicitFormula

/-! # The actual trigonometric weight and its instantiated explicit formula

The tests retain arbitrary positive scales, all evaluation points in the
required half-plane, and the exact rational angle used by the sharper
Mossinghoff--Trudgian argument. The weight is explicitly nonzero at zero.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real Set

private def angle : ℝ := 185573 / 100000

example : π / 2 < angle ∧ angle < π := mossinghoffTrudgian_theta_mem

example (θ u : ℝ) : HasDerivAt (kadiriKernel θ) (kadiriKernel₁ θ u) u :=
  hasDerivAt_kadiriKernel θ u

example (θ u : ℝ) : HasDerivAt (kadiriKernel₁ θ) (kadiriKernel₂ θ u) u :=
  hasDerivAt_kadiriKernel₁ θ u

example {η : ℝ} (hη : 0 < η) : 0 < kadiriWeight angle η 0 :=
  kadiriWeight_zero_pos mossinghoffTrudgian_theta_mem hη

example {η : ℝ} (hη : 0 < η) :
    kadiriWeight angle η (kadiriWeightSupport angle η) = 0 ∧
    kadiriWeight₁ angle η 0 = 0 ∧
    kadiriWeight₁ angle η (kadiriWeightSupport angle η) = 0 ∧
    kadiriWeight₂ angle η (kadiriWeightSupport angle η) = 0 :=
  ⟨kadiriWeight_support mossinghoffTrudgian_theta_mem hη,
    kadiriWeight₁_zero mossinghoffTrudgian_theta_mem,
    kadiriWeight₁_support mossinghoffTrudgian_theta_mem hη,
    kadiriWeight₂_support mossinghoffTrudgian_theta_mem hη⟩

example {η u : ℝ} (hu : u ∈ Ioo 0 (kadiriWeightSupport angle η)) :
    HasDerivAt (fun u => (kadiriWeight angle η u : ℂ)) (kadiriWeight₁ angle η u : ℂ) u :=
  (hasDerivAt_kadiriWeight hu).ofReal_comp

example (η : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc 0 (kadiriWeightSupport angle η),
    ‖(kadiriWeight₂ angle η u : ℂ)‖ ≤ M := exists_bound_kadiriWeight₂ angle η

example {η : ℝ} (hη : 0 < η) (s : ℂ) (hs : 1 / 2 < s.re) :
    (smoothedVonMangoldt (kadiriWeight angle η) s).re =
      (finiteLaplace (fun u => (kadiriWeight angle η u : ℂ)) (kadiriWeightSupport angle η)
        (s - 1)).re -
      (∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace (fun u => (kadiriWeight angle η u : ℂ)) (kadiriWeightSupport angle η)
          (s - riemannXiDivisorZeroValue p)).re) +
      kadiriWeight angle η 0 *
        (-(1 / 2 : ℝ) * Real.log Real.pi + (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re) +
      (smoothedGammaRemainder (fun u => (kadiriWeight₂ angle η u : ℂ))
        (kadiriWeightSupport angle η) s).re :=
  kadiriWeight_explicitFormula mossinghoffTrudgian_theta_mem hη hs

end

end PrimeFactorUnimodality.Tests
