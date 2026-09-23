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
theorem kadiriSix_valid_of_rational_points {T R r l b : ℝ} (hT : 25000000 ≤ T)
    (hR : 13 / 2 ≤ R) (hr : 6 ≤ r) (hrR : r ≤ R)
    (hl : l ≤ (r / R) * ((17034 / 1000) / (991 / 50))) (hb : 138 ≤ b * r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hlo : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) l)
    (hhi : b ≤ kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000) 1) :
    kadiriSixRow.Valid R r T 16 mossinghoffTrudgianCoefficient := by
  have hw := kadiriSix_argument_mem hT (by linarith : 0 < R) (by linarith : 0 ≤ r) hrR hl
  have hbudget : kadiriBootstrapLogCoefficient (185573 / 100000) (437 / 1000)
      (range 17) mossinghoffTrudgianCoefficient / r ≤ b :=
    (div_le_iff₀ (by linarith : 0 < r)).mpr ((kadiriSix_log_coefficient_le hg.2).trans hb)
  exact kadiriSix_valid_of_transform_margins hT hR hr hg hm hd he
    (hbudget.trans (kadiriSix_gap_le_of_rounded_endpoints hw hlo hhi))
    (hbudget.trans (hhi.trans (kadiriSix_rounded_gap_le 1)))

/-- The four required rational points and their lower bounds, stored once. -/
def kadiriSixTransformRow (i : Fin 4) : ℚ × ℚ :=
  match i.val with
  | 0 => (9 / 100, 18)
  | 1 => (69 / 100, 22)
  | 2 => (79 / 100, 23)
  | _ => (1, 23)

/-- Each row bounds the actual closed-form transform; no approximate evaluator is assumed. -/
def KadiriSixTransformBounds : Prop :=
  ∀ i : Fin 4, ((kadiriSixTransformRow i).2 : ℝ) ≤
    kadiriTransformGapClosedForm (185573 / 100000) 1 (1741 / 1000)
      ((kadiriSixTransformRow i).1 : ℝ)

/-- All scale intervals and both absolute-height rays follow from these four scalar points. -/
theorem kadiriSix_chain_of_four_points_from {T R : ℝ}
    (hT : 25000000 ≤ T) (hR₀ : 8 ≤ R) (hR₁ : R ≤ 69)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient T R 6 := by
  have h₀ := hpoints 0
  have h₁ := hpoints 1
  have h₂ := hpoints 2
  have h₃ := hpoints 3
  norm_num [kadiriSixTransformRow] at h₀ h₁ h₂ h₃
  have first : kadiriSixRow.Valid R 8 T 16 mossinghoffTrudgianCoefficient :=
    kadiriSix_valid_of_rational_points hT (l := 9 / 100) (b := 18)
      (by linarith) (by norm_num) hR₀ (by
        have hp : 0 < R := by linarith
        have hq : (8 / 69 : ℝ) ≤ 8 / R :=
          div_le_div_of_nonneg_left (by norm_num) hp hR₁
        nlinarith only [hq]) (by norm_num)
      hg hm hd he (by norm_num at h₀ ⊢; exact h₀) ((by norm_num : (18 : ℝ) ≤ 23).trans h₃)
  have middle : kadiriSixRow.Valid 8 (13 / 2) T 16
      mossinghoffTrudgianCoefficient :=
    kadiriSix_valid_of_rational_points hT (l := 69 / 100) (b := 22)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hg hm hd he (by simpa using h₁) ((by norm_num : (22 : ℝ) ≤ 23).trans h₃)
  have last : kadiriSixRow.Valid (13 / 2) 6 T 16
      mossinghoffTrudgianCoefficient :=
    kadiriSix_valid_of_rational_points hT (l := 79 / 100) (b := 23)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hg hm hd he (by simpa using h₂) h₃
  exact (first.chain.append middle.chain).append last.chain


/-- The original billion-height interface uses the common four-point assembler. -/
theorem kadiriSix_chain_of_four_points
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6 :=
  kadiriSix_chain_of_four_points_from (by norm_num) (by norm_num) (by norm_num)
    hg hm hd he hpoints

/-- The same four points also assemble the entire reduced-height chain. -/
theorem kadiriSix_reduced_chain_of_four_points
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 25000000 69 6 :=
  kadiriSix_chain_of_four_points_from (by norm_num) (by norm_num) (by norm_num)
    hg hm hd he hpoints

end

end PrimeFactorUnimodality
