import PrimeFactorUnimodality.Helpers.Analytic.KadiriCorrectionSign
import PrimeFactorUnimodality.Helpers.Analytic.KadiriRegionMaster
import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformMinimum

/-! # The numerical-bootstrap inequality for the actual xi divisor

Combine the established region, actual explicit formula, exact transform
gap, and normalized error budget. The leading coefficient omits the zero
harmonic; its pole has been incorporated into the gap. An explicit margin
then yields an improved zero-free gap. Its numerical verification, the
low-height input, and admissibility checks remain distinct obligations.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

variable {θ η η₀ σ₀ σ δ κ z H A R T : ℝ}
    (hR : 0 < R) (hT : 1 < T)
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 1 / 2 ≤ δ)
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    (hc : 0 < σ₀ - η₀ + δ) (hz : z ≤ (σ - 1) / η) (hH : 0 < H)
    (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
    (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
      (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (h₁ : 1 ∈ S) (a : ℕ → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (p : RiemannXiDivisorZeroIndex)
    (hβ : 1 / 2 < (riemannXiDivisorZeroValue p).re)
    (hηρ : η = 1 - (riemannXiDivisorZeroValue p).re)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos ((i : ℝ) * u))
    (hσA : 1 - 1 / (R * Real.log A) ≤ σ)
    (hlow : ∀ q : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue q).im| < T → (riemannXiDivisorZeroValue q).re ≤ σ)
    (hhigh : ∀ q : RiemannXiDivisorZeroIndex,
      T ≤ |(riemannXiDivisorZeroValue q).im| →
        1 / (R * Real.log |(riemannXiDivisorZeroValue q).im|) ≤
          1 - (riemannXiDivisorZeroValue q).re)
    (hharm : ∀ i ∈ S, |(i : ℝ) * (riemannXiDivisorZeroValue p).im| + H ≤ A)
    (ht : 10 ^ 9 ≤ (riemannXiDivisorZeroValue p).im)

include hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut
  h₀ h₁ ha hβ hηρ hpoly hσA hlow hhigh hharm ht

/-- The actual distinguished zero satisfies the normalized bootstrap inequality. -/
theorem kadiri_actual_bootstrap_constraint :
    kadiriTransformGap θ (a 0) (a 1) ((1 - σ) / η) ≤
      kadiriBootstrapLogCoefficient θ κ S a * η * Real.log (riemannXiDivisorZeroValue p).im +
      kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H
        (riemannXiDivisorZeroValue p).im S a := by
  have htpos : 0 < (riemannXiDivisorZeroValue p).im := by linarith
  have hA : ∀ i ∈ S, (i : ℝ) * (riemannXiDivisorZeroValue p).im ≠ 0 →
      10 ^ 9 ≤ |(i : ℝ) * (riemannXiDivisorZeroValue p).im| + H := by
    intro i _ hi
    have hi₀ : i ≠ 0 := by intro he; subst i; simp at hi
    have hi₁ : (1 : ℝ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi₀
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg i) htpos.le)]
    nlinarith [mul_le_mul_of_nonneg_right hi₁ htpos.le]
  have hm := kadiriWeight_region_master_nonneg hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut S a (fun i : ℕ => (i : ℝ)) ha
    1 h₁ (by norm_num) p hβ hηρ hpoly hσA hlow hhigh hharm hA
  have hg := kadiriTransformGap_le_budget_of_master hθ hη hηρ htpos.ne' S h₀ a hm
  rwa [kadiriBootstrapBudget_eq_log_add_correction hθ hη htpos S h₀ a] at hg

/-- Once the explicit margin is verified, the actual zero obeys the improved region. -/
theorem xi_zero_gap_of_bootstrap_margin {Rnext : ℝ} (hRnext : 0 < Rnext)
    (hκstrict : κ < 1) (ha₁ : 0 < a 1)
    (hmargin : kadiriBootstrapLogCoefficient θ κ S a / Rnext ≤
      kadiriTransformGap θ (a 0) (a 1) ((1 - σ) / η) -
        kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H
          (riemannXiDivisorZeroValue p).im S a) :
    1 / (Rnext * Real.log (riemannXiDivisorZeroValue p).im) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  have hm := kadiri_actual_bootstrap_constraint hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut
    S h₀ h₁ a ha p hβ hηρ hpoly hσA hlow hhigh hharm ht
  have hcpos := kadiriBootstrapLogCoefficient_pos hθ hκstrict S h₁ a ha ha₁
  simpa only [hηρ] using
    kadiri_gap_of_bootstrap_margin S a hcpos hRnext (by linarith) hm hmargin

/-- The actual divisor constraint can be evaluated using only the closed real transform formula. -/
theorem kadiri_actual_bootstrap_closed_constraint :
    kadiriTransformGapClosedForm θ (a 0) (a 1) ((1 - σ) / η) ≤
      kadiriBootstrapLogCoefficient θ κ S a * η * Real.log (riemannXiDivisorZeroValue p).im +
      kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H
        (riemannXiDivisorZeroValue p).im S a := by
  rw [← kadiriTransformGap_eq_closedForm hθ]
  exact kadiri_actual_bootstrap_constraint hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut
    S h₀ h₁ a ha p hβ hηρ hpoly hσA hlow hhigh hharm ht

/-- An endpoint margin gives the actual improved zero gap uniformly on a parameter interval. -/
theorem xi_zero_gap_of_endpoint_bootstrap_margin {Rnext l r : ℝ} (hRnext : 0 < Rnext)
    (hκstrict : κ < 1) (ha₁ : 0 < a 1) (hw : (1 - σ) / η ∈ Set.Icc l r)
    (hmargin : kadiriBootstrapLogCoefficient θ κ S a / Rnext ≤
      a 1 * kadiriKernelExpIntegral θ (l - 1) - a 0 * kadiriKernelExpIntegral θ r -
        kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H
          (riemannXiDivisorZeroValue p).im S a) :
    1 / (Rnext * Real.log (riemannXiDivisorZeroValue p).im) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  apply xi_zero_gap_of_bootstrap_margin hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut
    S h₀ h₁ a ha p hβ hηρ hpoly hσA hlow hhigh hharm ht hRnext hκstrict ha₁
  exact hmargin.trans (sub_le_sub_right
    (kadiriTransformGap_lower_of_mem_Icc hθ (ha 0 h₀) (ha 1 h₁) hw) _)

/-- A scale-band budget retains the negative correction with the actual transform value. -/
theorem xi_zero_gap_of_moment_transform_budget {Rnext T₀ y B₀ B₁ B₂ B₃ η₁ : ℝ}
    (hRnext : 0 < Rnext) (hκstrict : κ < 1) (ha₁ : 0 < a 1)
    (hT₀ : 2 ≤ T₀) (hT₀t : T₀ ≤ (riemannXiDivisorZeroValue p).im) (hH₄ : 4 ≤ H)
    (hy : 0 < y) (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (hB₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (hB₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (hB₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (hB₃ : kadiriDerivativeMoment θ 3 ≤ B₃)
    (hη₁ : η₁ ≤ η)
    (hbudget : kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ z H T₀
      B₀ B₁ B₂ B₃ (1 / Rnext) S a ≤ 0)
    (hmargin : kadiriBootstrapLogCoefficient θ κ S a / Rnext ≤
      kadiriTransformGap θ (a 0) (a 1) ((1 - σ) / η) -
        (η₁ / η₀) * kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ z H T₀
          B₀ B₁ B₂ B₃ (1 / Rnext) S a) :
    1 / (Rnext * Real.log (riemannXiDivisorZeroValue p).im) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  by_cases hdone : 1 / (Rnext * Real.log (riemannXiDivisorZeroValue p).im) ≤
      1 - (riemannXiDivisorZeroValue p).re
  · exact hdone
  have hlog : 0 < Real.log (riemannXiDivisorZeroValue p).im := Real.log_pos (by linarith)
  have hsmall : η < (1 / Rnext) / Real.log (riemannXiDivisorZeroValue p).im := by
    rw [div_div, hηρ]
    exact lt_of_not_ge hdone
  have hq := ((lt_div_iff₀ hlog).mp hsmall).le
  have hz₀ : z ≤ 0 := hz.trans
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hσ₁) hη.le)
  have hTpos : 0 < T₀ := by linarith
  have hM := kadiriDerivativeMass_le_momentMassBound hθ hz₀ hy hzy hend hB₀ hB₁ hB₂ hB₃
  have hM₀ := (kadiriDerivativeMass_nonneg hθ z).trans hM
  have hL₀ := kadiriTailAffineConstant_nonneg hTpos hH S h₀ a ha
  have hL₁ := kadiriTailLogCoefficient_nonneg hTpos hH S a ha
  have hquadratic := kadiriCorrectionQuadratic_nonneg hθ hσ₀ hκ hM₀
    (kadiriPoleCoefficient_nonneg S a ha T₀) hL₀ hL₁ (one_div_nonneg.mpr hRnext.le)
  have hcubic := kadiriCorrectionCubic_nonneg hθ hσ₀ hκ (by linarith) hc hL₀ S h₁ a ha
  have hpolybound : kadiriMomentCorrectionPolynomial θ η η₀ σ₀ κ δ z H T₀
      B₀ B₁ B₂ B₃ (1 / Rnext) S a ≤ (η₁ / η₀) *
        kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ z H T₀
          B₀ B₁ B₂ B₃ (1 / Rnext) S a :=
    kadiriCorrectionPolynomial_le_band_endpoint hη.le (hη.trans_le hη₀) hη₀ hη₁
      hquadratic hcubic hbudget
  have hcorrection := (kadiriBootstrapCorrection_le_momentPolynomial hθ hη.le hσ₀ hσ hκ hκ₁
    hT₀ hT₀t ht hH₄ hz₀ hy hzy hend hB₀ hB₁ hB₂ hB₃ S h₀ a ha hq).trans hpolybound
  apply xi_zero_gap_of_bootstrap_margin hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut
    S h₀ h₁ a ha p hβ hηρ hpoly hσA hlow hhigh hharm ht hRnext hκstrict ha₁
  linarith only [hmargin, hcorrection]

/-- Separate transform endpoints give the original scale-band interface. -/
theorem xi_zero_gap_of_moment_band_budget {Rnext T₀ y B₀ B₁ B₂ B₃ l r η₁ : ℝ}
    (hRnext : 0 < Rnext) (hκstrict : κ < 1) (ha₁ : 0 < a 1)
    (hT₀ : 2 ≤ T₀) (hT₀t : T₀ ≤ (riemannXiDivisorZeroValue p).im) (hH₄ : 4 ≤ H)
    (hy : 0 < y) (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (hB₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (hB₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (hB₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (hB₃ : kadiriDerivativeMoment θ 3 ≤ B₃)
    (hw : (1 - σ) / η ∈ Set.Icc l r) (hη₁ : η₁ ≤ η)
    (hbudget : kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ z H T₀
      B₀ B₁ B₂ B₃ (1 / Rnext) S a ≤ 0)
    (hmargin : kadiriBootstrapLogCoefficient θ κ S a / Rnext ≤
      a 1 * kadiriKernelExpIntegral θ (l - 1) - a 0 * kadiriKernelExpIntegral θ r -
        (η₁ / η₀) * kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ z H T₀
          B₀ B₁ B₂ B₃ (1 / Rnext) S a) :
    1 / (Rnext * Real.log (riemannXiDivisorZeroValue p).im) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  apply xi_zero_gap_of_moment_transform_budget hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut S h₀ h₁ a ha p hβ hηρ hpoly
    hσA hlow hhigh hharm ht hRnext hκstrict ha₁ hT₀ hT₀t hH₄ hy hzy hend
    hB₀ hB₁ hB₂ hB₃ hη₁ hbudget
  exact hmargin.trans (sub_le_sub_right
    (kadiriTransformGap_lower_of_mem_Icc hθ (ha 0 h₀) (ha 1 h₁) hw) _)

/-- Single-crossing endpoint minima retain cancellation in the scale-band bootstrap. -/
theorem xi_zero_gap_of_sharp_moment_band_budget {Rnext T₀ y B₀ B₁ B₂ B₃ l r η₁ : ℝ}
    (hRnext : 0 < Rnext) (hκstrict : κ < 1) (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hT₀ : 2 ≤ T₀) (hT₀t : T₀ ≤ (riemannXiDivisorZeroValue p).im) (hH₄ : 4 ≤ H)
    (hy : 0 < y) (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (hB₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (hB₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (hB₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (hB₃ : kadiriDerivativeMoment θ 3 ≤ B₃)
    (hw : (1 - σ) / η ∈ Set.Icc l r) (hη₁ : η₁ ≤ η)
    (hbudget : kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ z H T₀
      B₀ B₁ B₂ B₃ (1 / Rnext) S a ≤ 0)
    (hmargin : kadiriBootstrapLogCoefficient θ κ S a / Rnext ≤
      min (kadiriTransformGap θ (a 0) (a 1) l) (kadiriTransformGap θ (a 0) (a 1) r) -
        (η₁ / η₀) * kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ z H T₀
          B₀ B₁ B₂ B₃ (1 / Rnext) S a) :
    1 / (Rnext * Real.log (riemannXiDivisorZeroValue p).im) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  apply xi_zero_gap_of_moment_transform_budget hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut S h₀ h₁ a ha p hβ hηρ hpoly
    hσA hlow hhigh hharm ht hRnext hκstrict ha₁ hT₀ hT₀t hH₄ hy hzy hend
    hB₀ hB₁ hB₂ hB₃ hη₁ hbudget
  exact hmargin.trans (sub_le_sub_right (min_kadiriTransformGap_endpoints_le hθ ha₀ ha₁ hw) _)

/-- A nonpositive scale-endpoint budget is the zero-lower-scale case of the band bound. -/
theorem xi_zero_gap_of_moment_budget {Rnext T₀ y B₀ B₁ B₂ B₃ l r : ℝ}
    (hRnext : 0 < Rnext) (hκstrict : κ < 1) (ha₁ : 0 < a 1)
    (hT₀ : 2 ≤ T₀) (hT₀t : T₀ ≤ (riemannXiDivisorZeroValue p).im) (hH₄ : 4 ≤ H)
    (hy : 0 < y) (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (hB₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (hB₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (hB₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (hB₃ : kadiriDerivativeMoment θ 3 ≤ B₃)
    (hw : (1 - σ) / η ∈ Set.Icc l r)
    (hbudget : kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ z H T₀
      B₀ B₁ B₂ B₃ (1 / Rnext) S a ≤ 0)
    (hmargin : kadiriBootstrapLogCoefficient θ κ S a / Rnext ≤
      a 1 * kadiriKernelExpIntegral θ (l - 1) - a 0 * kadiriKernelExpIntegral θ r) :
    1 / (Rnext * Real.log (riemannXiDivisorZeroValue p).im) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  apply xi_zero_gap_of_moment_band_budget hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut S h₀ h₁ a ha p hβ hηρ hpoly
    hσA hlow hhigh hharm ht hRnext hκstrict ha₁ hT₀ hT₀t hH₄ hy hzy hend
    hB₀ hB₁ hB₂ hB₃ hw (show (0 : ℝ) ≤ η from hη.le) hbudget
  simpa only [zero_div, zero_mul, sub_zero] using hmargin

end

end PrimeFactorUnimodality
