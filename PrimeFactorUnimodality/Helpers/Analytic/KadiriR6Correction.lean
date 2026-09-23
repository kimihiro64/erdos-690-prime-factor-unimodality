import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Gamma
import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Polynomial
import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Tail

/-! # The actual endpoint correction is nonpositive uniformly

Insert the proved Gamma, pole and complete tail bounds into the polynomial
estimate. The only remaining scalar enclosures are the shared kernel and
support bounds, already checked separately. This removes every correction
sign obligation from the proposed three-step chain; the transform margins
remain separate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Real

/-- The complete correction has the required sign at every relevant pair of region constants. -/
theorem kadiriSix_correction_nonpos {R r : ℝ} (hR : 13 / 2 ≤ R) (hr : 6 ≤ r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0)
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ)) :
    kadiriSixRow.correction R r 1000000000 16 mossinghoffTrudgianCoefficient ≤ 0 := by
  obtain ⟨hη, hη'⟩ := kadiriSix_scale_bounds hr
  obtain ⟨hσ, _⟩ := kadiriSix_sigma_bounds hR
  have ha : ∀ i ∈ range 17, 0 ≤ mossinghoffTrudgianCoefficient i :=
    fun i hi => mossinghoffTrudgianCoefficient_nonneg (mem_range.mp hi)
  have hL₀ : 0 ≤ kadiriTailConservativeConstant 1000000000 100000 (range 17)
      mossinghoffTrudgianCoefficient :=
    (kadiriTailAffineConstant_nonneg (by norm_num) (by norm_num)
      (range 17) (by simp) mossinghoffTrudgianCoefficient ha).trans
        (kadiriTailAffineConstant_le_conservative 1000000000 100000 (range 17)
          mossinghoffTrudgianCoefficient (by simp))
  have hq : 0 ≤ (1 : ℝ) / r := (one_div_pos.mpr (by linarith : 0 < r)).le
  have hq' : (1 : ℝ) / r ≤ 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num) hr
  exact kadiriSix_polynomial_nonpos hη.le hη' hσ (kadiriSix_moment_mass_le hm hd)
    (kadiriPoleCoefficient_nonneg (range 17) mossinghoffTrudgianCoefficient ha 1000000000)
    kadiriSix_pole_coefficient_le hL₀ kadiriSix_tail_constant_le
    (kadiriTailLogCoefficient_nonneg (T := 1000000000) (H := 100000) (by norm_num) (by norm_num)
      (range 17) mossinghoffTrudgianCoefficient ha)
    kadiriSix_tail_log_coefficient_le (kadiriSix_gamma_residual_le hσ) hq hq' hg hm

/-- With the common scalar enclosures, only the two transform margins are needed for a valid row. -/
theorem kadiriSix_valid_of_transform_margins {R r : ℝ} (hR : 13 / 2 ≤ R) (hr : 6 ≤ r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hlo : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1)
          (kadiriBootstrapLowerArgument R r 16 100000 1000000000))
    (hhi : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) 1) :
    kadiriSixRow.Valid R r 1000000000 16 mossinghoffTrudgianCoefficient :=
  kadiriSix_valid hR hr hg hm hd he (kadiriSix_correction_nonpos hR hr hg.1 hm hd) hlo hhi

end

end PrimeFactorUnimodality
