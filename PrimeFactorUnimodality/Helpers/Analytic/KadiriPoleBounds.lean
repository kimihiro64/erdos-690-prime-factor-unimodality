import PrimeFactorUnimodality.Helpers.Analytic.KadiriLaplacePositivity
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightPositivity
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightedRemainder
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # Explicit bounds for the smoothed pole contribution

For nonzero harmonics the pole at `s-1` has nonpositive rational part when
`Re(s)<=1`. The already-proved correlation theorem makes the entire
shifted transform nonnegative on the closed right half-plane. Thus only
the weighted unshifted remainder is needed for an inverse-height-square
bound. The zero harmonic keeps the exact unshifted real transform.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set

/-- At height zero the subtracted shifted transform is nonnegative. -/
theorem kadiriWeight_pole_zero_le {θ η κ δ σ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ)
    (hδ : 0 ≤ σ - 1 + δ) :
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
      (((σ : ℂ) + (0 : ℂ) * I) - 1) ≤
      (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((σ - 1 : ℝ) : ℂ)).re := by
  have hp := mul_nonneg hκ (re_kadiriWeight_laplace_nonneg hθ hη
    (s := ((σ - 1 + δ : ℝ) : ℂ)) (by simpa using hδ))
  simpa only [smoothedLaplaceDifference, zero_mul, add_zero, ofReal_add, ofReal_sub,
    ofReal_one, sub_le_self_iff] using hp

/-- The coefficient in the inverse-height-square pole bound. -/
def kadiriPoleError (θ η z : ℝ) : ℝ := η ^ 2 * kadiriDerivativeMass θ z

/-- Nonzero harmonics have no positive rational pole part in the working strip. -/
theorem kadiriWeight_pole_nonzero_le {θ η κ δ σ z y : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ) (hσ : σ ≤ 1)
    (hδ : 0 ≤ σ - 1 + δ) (hz : z ≤ (σ - 1) / η) (hy : y ≠ 0) :
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
      (((σ : ℂ) + (y : ℂ) * I) - 1) ≤ kadiriPoleError θ η z / y ^ 2 := by
  let F (x : ℝ) := (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
    (kadiriWeightSupport θ η) ((x : ℂ) + (y : ℂ) * I)).re
  let K (x : ℝ) := kadiriWeight θ η 0 * x / (x ^ 2 + y ^ 2)
  have h₀ : |F (σ - 1) - K (σ - 1)| ≤ η ^ 2 * kadiriDerivativeMass θ z / y ^ 2 := by
    simpa [F, K] using abs_re_kadiriWeight_laplace_sub_pole_le_mass_im hθ hη
      (s := ((σ - 1 : ℝ) : ℂ) + (y : ℂ) * I) (by simpa using hz) (by simpa using hy)
  have hK₀ : K (σ - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (kadiriWeight_nonneg hθ hη 0) (sub_nonpos.mpr hσ))
    (by positivity)
  have hF₁ : 0 ≤ κ * F (σ - 1 + δ) := mul_nonneg hκ
    (re_kadiriWeight_laplace_nonneg hθ hη (by simpa using hδ))
  have hupper := (abs_le.mp h₀).2
  have he : (σ : ℂ) + (y : ℂ) * I - 1 = ((σ - 1 : ℝ) : ℂ) + (y : ℂ) * I := by
    push_cast
    ring
  have hshift : (((σ - 1 : ℝ) : ℂ) + (y : ℂ) * I) + (δ : ℂ) =
      ((σ - 1 + δ : ℝ) : ℂ) + (y : ℂ) * I := by push_cast; ring
  simp only [smoothedLaplaceDifference, he, hshift]
  change F (σ - 1) - κ * F (σ - 1 + δ) ≤ _
  dsimp only [kadiriPoleError]
  linarith only [hupper, hK₀, hF₁]

/-- A uniform pole majorant retains the exact real transform at the zero harmonic. -/
def kadiriPoleMajorant (θ η z σ y : ℝ) : ℝ :=
  if y = 0 then
    (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
      (kadiriWeightSupport θ η) ((σ - 1 : ℝ) : ℂ)).re
  else kadiriPoleError θ η z / y ^ 2

/-- Both harmonic cases use the actual compact weight and its proved transform bounds. -/
theorem kadiriWeight_pole_le_majorant {θ η κ δ σ z y : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ) (hσ : σ ≤ 1)
    (hδ : 0 ≤ σ - 1 + δ) (hz : z ≤ (σ - 1) / η) :
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
      (((σ : ℂ) + (y : ℂ) * I) - 1) ≤ kadiriPoleMajorant θ η z σ y := by
  by_cases hy : y = 0
  · subst y
    simpa only [kadiriPoleMajorant, ofReal_zero, ↓reduceIte] using
      kadiriWeight_pole_zero_le hθ hη hκ hδ
  · simpa only [kadiriPoleMajorant, hy, ↓reduceIte] using
      kadiriWeight_pole_nonzero_le hθ hη hκ hσ hδ hz hy

/-- Nonnegative polynomial weights preserve the bound for the entire pole contribution. -/
theorem sum_kadiriWeight_pole_le_majorant {θ η κ δ σ z : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ) (hσ : σ ≤ 1)
    (hδ : 0 ≤ σ - 1 + δ) (hz : z ≤ (σ - 1) / η)
    {ι : Type*} (S : Finset ι) (c k : ι → ℝ) (hc : ∀ i ∈ S, 0 ≤ c i) (t : ℝ) :
    (∑ i ∈ S, c i * smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η)
      κ δ (((σ : ℂ) + (k i * t : ℝ) * I) - 1)) ≤
      ∑ i ∈ S, c i * kadiriPoleMajorant θ η z σ (k i * t) :=
  Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
    (kadiriWeight_pole_le_majorant hθ hη hκ hσ hδ hz) (hc i hi))

end

end PrimeFactorUnimodality
