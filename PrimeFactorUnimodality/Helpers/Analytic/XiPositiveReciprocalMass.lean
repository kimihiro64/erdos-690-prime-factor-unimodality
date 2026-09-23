import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalMass
import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalNormSymmetry

/-! # Half of the real reciprocal mass bounds every positive prefix

The positive finite prefix and its conjugate image are disjoint and have
equal real reciprocal sums. Their union is a finite subset of the actual
divisor, so its mass is at most the unconditional total. All multiplicity
labels and endpoint zeros are preserved, without a critical-line premise.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The closed positive prefix uses at most half the complete real reciprocal mass. -/
theorem sum_xi_positive_reciprocal_le_half_total (a : ℝ) :
    (∑ p ∈ xiPositiveHeightIndices a, (1 / riemannXiDivisorZeroValue p).re) ≤
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 := by
  classical
  let P := xiPositiveHeightIndices a
  let e := riemannXiDivisorConjugation
  have hd : Disjoint P (P.map e.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro p hp hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hn
    have hp' := ((mem_xiPositiveHeightIndices a _).mp hp).1
    have hq' := ((mem_xiPositiveHeightIndices a _).mp hq).1
    change 0 < (riemannXiDivisorZeroValue (riemannXiDivisorConjugation q)).im at hp'
    rw [riemannXiDivisorZeroValue_conjugation, conj_im] at hp'
    linarith
  have hS := (sum_reciprocal_le_xiLowReciprocalMass (a + 1)
    (P ∪ P.map e.toEmbedding) (by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · have hv := (mem_xiPositiveHeightIndices a p).mp hp
        rw [abs_of_pos hv.1]
        linarith [hv.2]
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
        have hv := (mem_xiPositiveHeightIndices a q).mp hq
        change |(riemannXiDivisorZeroValue (riemannXiDivisorConjugation q)).im| < a + 1
        rw [riemannXiDivisorZeroValue_conjugation, conj_im, abs_neg, abs_of_pos hv.1]
        linarith [hv.2])).trans (xiLowReciprocalMass_le_total (a + 1))
  rw [Finset.sum_union hd, Finset.sum_map] at hS
  simp only [Equiv.toEmbedding_apply, e, riemannXiDivisorZeroValue_conjugation,
    one_div, ← map_inv₀, conj_re] at hS
  dsimp only [P] at hS
  simp only [one_div]
  linarith only [hS]

end

end PrimeFactorUnimodality
