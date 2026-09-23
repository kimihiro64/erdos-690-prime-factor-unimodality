import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalNormSymmetry
import PrimeFactorUnimodality.Helpers.Analytic.XiSignRows
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingEndpoints

/-! # Exhausting the actual low xi divisor by critical-line witnesses

An injective family of witnessed critical-line zeros gives a lower bound
for the total multiplicity count. A matching upper bound forces every
divisor label into that family, ruling out unlisted and multiple zeros.
Conjugation and real-axis nonvanishing then cover both ordinate signs.
Endpoint signs and the total-count upper bound remain separate inputs.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset

/-- Saturating the multiplicity count proves that no positive-height label was omitted. -/
theorem xiStrict_criticalLine_of_index_family {T : ℝ} {n : ℕ}
    (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ xiStrictPositiveHeightIndices T)
    (hline : ∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2)
    (hcount : xiStrictZeroCount T ≤ n) :
    ∀ p ∈ xiStrictPositiveHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  classical
  have hsub : univ.image f ⊆ xiStrictPositiveHeightIndices T := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact hmem i
  have hcard : (univ.image f).card = n := by
    rw [card_image_of_injective _ hf]
    simp
  have heq := eq_of_subset_of_card_le hsub (hcount.trans_eq hcard.symm)
  intro p hp
  rw [← heq] at hp
  obtain ⟨i, _, rfl⟩ := mem_image.mp hp
  exact hline i

/-- Positive-height verification covers the entire strict low set via actual conjugation. -/
theorem xiLow_criticalLine_of_positive {T : ℝ}
    (hline : ∀ p ∈ xiStrictPositiveHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2) :
    ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  intro p hp
  have hT := (mem_xiLowHeightIndices T p).mp hp
  by_cases hi : 0 < (riemannXiDivisorZeroValue p).im
  · exact hline p ((mem_xiStrictPositiveHeightIndices T p).mpr
      ⟨hi, (le_abs_self _).trans_lt hT⟩)
  · have hi' : (riemannXiDivisorZeroValue p).im < 0 :=
      lt_of_le_of_ne (le_of_not_gt hi) (xi_divisor_im_ne_zero p)
    have hmem : riemannXiDivisorConjugation p ∈ xiStrictPositiveHeightIndices T := by
      rw [mem_xiStrictPositiveHeightIndices, riemannXiDivisorZeroValue_conjugation, conj_im]
      exact ⟨by linarith, by simpa only [abs_of_neg hi'] using hT⟩
    simpa only [riemannXiDivisorZeroValue_conjugation, conj_re] using
      hline (riemannXiDivisorConjugation p) hmem

namespace XiSignRows

/-- An ordered sign block within the positive cutoff gives distinct labels in the strict count. -/
theorem Valid.exists_strict_indices {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T) :
    ∃ f : Fin n → RiemannXiDivisorZeroIndex, Function.Injective f ∧
      (∀ i, f i ∈ xiStrictPositiveHeightIndices T) ∧
      ∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 := by
  obtain ⟨f, hf, hi⟩ := h.exists_indices
  refine ⟨f, hf, ?_, fun i => (hi i).1⟩
  intro i
  rw [mem_xiStrictPositiveHeightIndices]
  have hl : (0 : ℝ) ≤ (rows i).lower := by exact_mod_cast ha.trans (h.lower i)
  have hu' : ((rows i).upper : ℝ) ≤ (b : ℝ) := by exact_mod_cast h.upper i
  have hu := hu'.trans hb
  exact ⟨hl.trans_lt (hi i).2.1, (hi i).2.2.trans_le hu⟩

/-- The witnessed rows cannot outnumber the complete positive-height divisor count. -/
theorem Valid.le_strict_count {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T) : n ≤ xiStrictZeroCount T := by
  classical
  obtain ⟨f, hf, hmem, _⟩ := h.exists_strict_indices ha hb
  have hsub : univ.image f ⊆ xiStrictPositiveHeightIndices T := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact hmem i
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hf] at hc
  simpa only [card_univ, Fintype.card_fin, xiStrictZeroCount] using hc

/-- A matching count bound turns local signs into complete finite critical-line verification. -/
theorem Valid.low_criticalLine {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T) (hcount : xiStrictZeroCount T ≤ n) :
    ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  obtain ⟨f, hf, hmem, hline⟩ := h.exists_strict_indices ha hb
  exact xiLow_criticalLine_of_positive
    (xiStrict_criticalLine_of_index_family f hf hmem hline hcount)

end XiSignRows

end

end PrimeFactorUnimodality
