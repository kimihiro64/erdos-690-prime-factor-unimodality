import PrimeFactorUnimodality.Helpers.Analytic.XiCountingRectangle
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingAbel
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorConjugation

/-! # Reducing the low reciprocal-norm mass to positive ordinates

There are no real xi zeros. Conjugation pairs every negative ordinate with
the positive one, preserving multiplicity and the reciprocal norm. The
strict low set is contained in the union of the two closed positive-count
copies; using a closed upper endpoint only increases the bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The reciprocal norm is invariant under conjugation of divisor labels. -/
theorem norm_xi_reciprocal_conjugation (p : RiemannXiDivisorZeroIndex) :
    ‖(1 : ℂ) / riemannXiDivisorZeroValue (riemannXiDivisorConjugation p)‖ =
      ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ := by
  simp only [riemannXiDivisorZeroValue_conjugation, norm_div, norm_one, norm_conj]

/-- No zero label has ordinate zero, by the proved real-axis nonvanishing. -/
theorem xi_divisor_im_ne_zero (p : RiemannXiDivisorZeroIndex) :
    (riemannXiDivisorZeroValue p).im ≠ 0 :=
  fun he => riemannXi_ne_zero_of_im_eq_zero he (riemannXiDivisorZeroValue_eq_zero p)

/-- Both ordinate signs contribute at most twice the closed positive-ordinate mass. -/
theorem sum_xi_low_reciprocal_norm_le_twice_positive (T : ℝ) :
    (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      2 * ∑ p ∈ xiPositiveHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ := by
  classical
  let P := xiPositiveHeightIndices T
  let e := riemannXiDivisorConjugation
  have hcover : xiLowHeightIndices T ⊆ P ∪ P.map e.toEmbedding := by
    intro p hp
    have hT := (mem_xiLowHeightIndices T p).mp hp
    by_cases hi : 0 < (riemannXiDivisorZeroValue p).im
    · exact Finset.mem_union_left _ ((mem_xiPositiveHeightIndices T p).mpr
        ⟨hi, (le_abs_self _).trans hT.le⟩)
    · have hi' : (riemannXiDivisorZeroValue p).im < 0 :=
        lt_of_le_of_ne (le_of_not_gt hi) (xi_divisor_im_ne_zero p)
      have hv : (riemannXiDivisorZeroValue (e.symm p)).im =
          -(riemannXiDivisorZeroValue p).im := by
        have hc := congrArg Complex.im (riemannXiDivisorZeroValue_conjugation (e.symm p))
        change (riemannXiDivisorZeroValue (e (e.symm p))).im =
          -(riemannXiDivisorZeroValue (e.symm p)).im at hc
        rw [e.apply_symm_apply] at hc
        linarith
      apply Finset.mem_union_right
      apply Finset.mem_map.mpr
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      rw [mem_xiPositiveHeightIndices, hv]
      exact ⟨by linarith, (neg_le_abs _).trans hT.le⟩
  have hd : Disjoint P (P.map e.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro p hp hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hn
    have hp' := ((mem_xiPositiveHeightIndices T _).mp hp).1
    have hq' := ((mem_xiPositiveHeightIndices T _).mp hq).1
    change 0 < (riemannXiDivisorZeroValue (riemannXiDivisorConjugation q)).im at hp'
    rw [riemannXiDivisorZeroValue_conjugation, conj_im] at hp'
    linarith
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hcover
    (fun p _ _ => norm_nonneg ((1 : ℂ) / riemannXiDivisorZeroValue p))
  rw [Finset.sum_union hd, Finset.sum_map] at hs
  simp only [Equiv.toEmbedding_apply, e, norm_xi_reciprocal_conjugation] at hs
  simpa only [two_mul] using hs

end

end PrimeFactorUnimodality
