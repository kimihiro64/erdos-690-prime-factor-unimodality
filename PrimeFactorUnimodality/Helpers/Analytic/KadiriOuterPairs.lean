import PrimeFactorUnimodality.Helpers.Analytic.KadiriOuterPairRemainder
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightPositivity
import PrimeFactorUnimodality.Helpers.Analytic.KadiriZeroSums
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.OuterStrip

/-! # Uniform outer-zero pair errors inside the critical strip

The signed rational-kernel comparison removes the rational term from
Kadiri's four-transform error. Reflecting the left outer strip gives the
same bound on both sides, with no assumption about the real parts of zeros
beyond the closed critical strip. The cutoff inequality remains explicit
until the numerical parameters are certified.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real
open scoped ComplexConjugate

/-- The coefficient of the inverse-height-square error in an outer pair. -/
def kadiriOuterError (θ η κ σ₀ z : ℝ) : ℝ :=
  η ^ 2 * kadiriDerivativeMass θ z +
    (1 + 2 * κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / (σ₀ - 1 / 2)

/-- The uniform outer error is nonnegative for the admissible analytic parameters. -/
theorem kadiriOuterError_nonneg {θ η κ σ₀ z : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ) (hσ₀ : 1 / 2 < σ₀) :
    0 ≤ kadiriOuterError θ η κ σ₀ z := by
  have hm := kadiriDerivativeMass_nonneg hθ z
  have hd := neg_kadiriKernel₂_zero_nonneg hθ
  unfold kadiriOuterError
  positivity

variable {θ η κ δ σ₀ σ z H : ℝ}
  (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ)
  (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hδ : 1 / 2 ≤ δ)
  (hz : z ≤ (σ - 1) / η) (hH : 0 < H)
  (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
  (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
    (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2)

include hθ hη hκ hσ₀ hσ hδ hz hH hgap hcut

/-- Right outer pairs have only the weighted and cubic errors after the height cutoff. -/
theorem kadiriWeight_right_outer_pair_lower_bound {β y : ℝ}
    (hβ₀ : σ ≤ β) (hβ₁ : β ≤ 1) (hy : H ^ 2 ≤ y ^ 2) :
    -kadiriOuterError θ η κ σ₀ z / y ^ 2 ≤
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ - β : ℝ) : ℂ) + (y : ℂ) * I) +
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ - 1 + β : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hy₀ : y ≠ 0 := by intro he; rw [he] at hy; nlinarith [sq_pos_of_pos hH]
  have hp := Real.stechkinPair_outer_sub_nonneg_of_cutoff hσ₀ hσ hβ₀ hβ₁ hκ
    (by linarith : 1 - σ₀ ≤ δ) hH hy hgap hcut
  have hw := mul_nonneg (kadiriWeight_nonneg hθ hη 0) hp
  have he := kadiriWeight_outer_pair_remainder_lower_bound hθ hη hκ
    (by linarith : 0 < σ₀ - 1 / 2)
    (hz.trans (div_le_div_of_nonneg_right (by linarith) hη.le)) hy₀
    (by linarith : σ₀ - 1 / 2 ≤ σ - 1 + β)
    (by linarith : σ₀ - 1 / 2 ≤ σ - β + δ)
    (by linarith : σ₀ - 1 / 2 ≤ σ - 1 + β + δ)
  dsimp [kadiriOuterError]
  rw [neg_div]
  linarith only [he, hw]

/-- Both outer strips satisfy the same bound, with same-height reflection retaining the pair. -/
theorem kadiriWeight_outer_zero_pair_lower_bound {ρ : ℂ}
    (hρ₀ : 0 ≤ ρ.re) (hρ₁ : ρ.re ≤ 1) (houter : ¬ kadiriCentralStrip σ ρ)
    (t : ℝ) (hy : H ^ 2 ≤ (t - ρ.im) ^ 2) :
    -kadiriOuterError θ η κ σ₀ z / (t - ρ.im) ^ 2 ≤
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - ρ) +
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - (1 - conj ρ)) := by
  have hright (w : ℂ) (hw₀ : σ ≤ w.re) (hw₁ : w.re ≤ 1)
      (hwy : H ^ 2 ≤ (t - w.im) ^ 2) :
      -kadiriOuterError θ η κ σ₀ z / (t - w.im) ^ 2 ≤
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
            (((σ : ℂ) + (t : ℂ) * I) - w) +
          smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
            (((σ : ℂ) + (t : ℂ) * I) - (1 - conj w)) := by
    have hp := kadiriWeight_right_outer_pair_lower_bound hθ hη hκ hσ₀ hσ hδ hz hH hgap hcut
      hw₀ hw₁ hwy
    have he₁ : ((σ - w.re : ℝ) : ℂ) + ((t - w.im : ℝ) : ℂ) * I =
        ((σ : ℂ) + (t : ℂ) * I) - w := by apply Complex.ext <;> simp
    have he₂ : ((σ - 1 + w.re : ℝ) : ℂ) + ((t - w.im : ℝ) : ℂ) * I =
        ((σ : ℂ) + (t : ℂ) * I) - (1 - conj w) := by
      apply Complex.ext <;> simp
      ring
    rwa [he₁, he₂] at hp
  by_cases hr : σ ≤ ρ.re
  · exact hright ρ hr hρ₁ hy
  · have hl : ρ.re < 1 - σ := by
      by_contra! hn
      exact houter ⟨hn, (lt_of_not_ge hr).le⟩
    have hp := hright (1 - conj ρ) (by simp only [sub_re, one_re, conj_re]; linarith)
      (by simp only [sub_re, one_re, conj_re]; linarith) (by simpa using hy)
    simpa only [sub_im, one_im, conj_im, zero_sub, neg_neg, map_sub, map_one, conj_conj,
      sub_sub_cancel, add_comm] using hp

end

end PrimeFactorUnimodality
