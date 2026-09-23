import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Transform

/-! # Four rational transform bounds assemble the region bootstrap

The three improving rows share their upper endpoint and all kernel
parameters. Their lower endpoints are bounded by rational points before
any evaluation. One four-element family of scalar inequalities therefore
supplies the complete ordered chain, with no height or scale enumeration.
The family is an explicit input here, not an assertion of numerical validity.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Real

/-- A rational interval and two transform bounds suffice for one complete bootstrap row. -/
theorem kadiriSix_valid_of_rational_points {R r l b : ℝ}
    (hR : 13 / 2 ≤ R) (hr : 6 ≤ r) (hrR : r ≤ R)
    (hl : l ≤ (r / R) * ((20718 / 1000) / (47 / 2))) (hb : 138 ≤ b * r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hlo : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) l)
    (hhi : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) 1) :
    kadiriSixRow.Valid R r 1000000000 16 mossinghoffTrudgianCoefficient := by
  have hw := kadiriSix_argument_mem (by linarith : 0 < R) (by linarith : 0 ≤ r) hrR hl
  have hbudget : kadiriBootstrapLogCoefficient (185573 / 100000) (439 / 1000)
      (range 17) mossinghoffTrudgianCoefficient / r ≤ b :=
    (div_le_iff₀ (by linarith : 0 < r)).mpr ((kadiriSix_log_coefficient_le hg.2).trans hb)
  exact kadiriSix_valid_of_transform_margins hR hr hg hm hd he
    (hbudget.trans (kadiriSix_gap_le_of_rounded_endpoints hw hlo hhi))
    (hbudget.trans (hhi.trans (kadiriSix_rounded_gap_le 1)))

/-- The four required rational points and their lower bounds, stored once. -/
def kadiriSixTransformRow (i : Fin 4) : ℚ × ℚ :=
  match i.val with
  | 0 => (12 / 100, 18)
  | 1 => (71 / 100, 22)
  | 2 => (81 / 100, 23)
  | _ => (1, 23)

/-- Each row bounds the actual closed-form transform; no approximate evaluator is assumed. -/
def KadiriSixTransformBounds : Prop :=
  ∀ i : Fin 4, ((kadiriSixTransformRow i).2 : ℝ) ≤
    kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000)
      ((kadiriSixTransformRow i).1 : ℝ)

/-- All scale intervals and both absolute-height rays follow from these four scalar points. -/
theorem kadiriSix_chain_of_four_points
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6 := by
  have h₀ := hpoints 0
  have h₁ := hpoints 1
  have h₂ := hpoints 2
  have h₃ := hpoints 3
  norm_num [kadiriSixTransformRow] at h₀ h₁ h₂ h₃
  have first : kadiriSixRow.Valid 56 8 1000000000 16 mossinghoffTrudgianCoefficient :=
    kadiriSix_valid_of_rational_points (l := 12 / 100) (b := 18)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hg hm hd he (by norm_num at h₀ ⊢; exact h₀) ((by norm_num : (18 : ℝ) ≤ 23).trans h₃)
  have middle : kadiriSixRow.Valid 8 (13 / 2) 1000000000 16
      mossinghoffTrudgianCoefficient :=
    kadiriSix_valid_of_rational_points (l := 71 / 100) (b := 22)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hg hm hd he (by simpa using h₁) ((by norm_num : (22 : ℝ) ≤ 23).trans h₃)
  have last : kadiriSixRow.Valid (13 / 2) 6 1000000000 16
      mossinghoffTrudgianCoefficient :=
    kadiriSix_valid_of_rational_points (l := 81 / 100) (b := 23)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hg hm hd he (by simpa using h₂) h₃
  exact (first.chain.append middle.chain).append last.chain

end

end PrimeFactorUnimodality
