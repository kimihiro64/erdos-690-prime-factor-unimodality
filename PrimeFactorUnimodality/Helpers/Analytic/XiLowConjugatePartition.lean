import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalNormSymmetry
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingEndpoints

/-! # Exact positive/conjugate partition of the strict low xi divisor

Real-axis nonvanishing excludes unpaired labels. The same strict upper
cutoff is used in both halves, so zeros at the cutoff remain in the high
tail. All multiplicity labels are preserved by the existing equivalence.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

/-- Positive labels and their conjugates cannot overlap. -/
theorem disjoint_xiStrictPositive_conjugate (T : ℝ) :
    Disjoint (xiStrictPositiveHeightIndices T)
      ((xiStrictPositiveHeightIndices T).map riemannXiDivisorConjugation.toEmbedding) := by
  classical
  rw [disjoint_left]
  intro p hp hn
  obtain ⟨q, hq, rfl⟩ := mem_map.mp hn
  have hp' := ((mem_xiStrictPositiveHeightIndices T _).mp hp).1
  have hq' := ((mem_xiStrictPositiveHeightIndices T _).mp hq).1
  simp only [Equiv.toEmbedding_apply, riemannXiDivisorZeroValue_conjugation, conj_im] at hp'
  linarith

/-- The low set is exactly the disjoint union of the two strict positive-count copies. -/
theorem xiLowHeightIndices_eq_positive_union_conjugate (T : ℝ) :
    xiLowHeightIndices T = xiStrictPositiveHeightIndices T ∪
      (xiStrictPositiveHeightIndices T).map riemannXiDivisorConjugation.toEmbedding := by
  classical
  let e := riemannXiDivisorConjugation
  apply Subset.antisymm
  · intro p hp
    have hT := (mem_xiLowHeightIndices T p).mp hp
    by_cases hi : 0 < (riemannXiDivisorZeroValue p).im
    · exact mem_union_left _ ((mem_xiStrictPositiveHeightIndices T p).mpr
        ⟨hi, (le_abs_self _).trans_lt hT⟩)
    · have hi' : (riemannXiDivisorZeroValue p).im < 0 :=
        lt_of_le_of_ne (le_of_not_gt hi) (xi_divisor_im_ne_zero p)
      have hv : (riemannXiDivisorZeroValue (e.symm p)).im =
          -(riemannXiDivisorZeroValue p).im := by
        have hc := congrArg Complex.im (riemannXiDivisorZeroValue_conjugation (e.symm p))
        change (riemannXiDivisorZeroValue (e (e.symm p))).im =
          -(riemannXiDivisorZeroValue (e.symm p)).im at hc
        rw [e.apply_symm_apply] at hc
        linarith
      apply mem_union_right
      apply mem_map.mpr
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      rw [mem_xiStrictPositiveHeightIndices, hv]
      exact ⟨by linarith, (neg_le_abs _).trans_lt hT⟩
  · intro p hp
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨hi, hT⟩ := (mem_xiStrictPositiveHeightIndices T p).mp hp
      exact (mem_xiLowHeightIndices T p).mpr (by rwa [abs_of_pos hi])
    · obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
      obtain ⟨hi, hT⟩ := (mem_xiStrictPositiveHeightIndices T q).mp hq
      rw [mem_xiLowHeightIndices]
      simpa only [Equiv.toEmbedding_apply, riemannXiDivisorZeroValue_conjugation,
        conj_im, abs_neg, abs_of_pos hi] using hT

/-- Every additive weight can be transported without discarding cancellation or multiplicity. -/
theorem sum_xiLow_eq_positive_conjugate {E : Type*} [AddCommMonoid E]
    (T : ℝ) (f : RiemannXiDivisorZeroIndex → E) :
    (∑ p ∈ xiLowHeightIndices T, f p) =
      ∑ p ∈ xiStrictPositiveHeightIndices T, (f p + f (riemannXiDivisorConjugation p)) := by
  rw [xiLowHeightIndices_eq_positive_union_conjugate,
    sum_union (disjoint_xiStrictPositive_conjugate T), sum_map, sum_add_distrib]
  rfl

end

end PrimeFactorUnimodality
