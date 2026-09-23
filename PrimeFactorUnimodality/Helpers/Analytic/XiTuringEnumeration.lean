import PrimeFactorUnimodality.Helpers.Analytic.XiTuringVerification
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroRowEnumeration

/-! # Turing padding supplies exact row-count saturation

The rows below the cutoff and the padding rows above it share a rational
boundary. The proved integral budget covers every actual label below that
boundary; none can belong to a padding row. Thus padding certifies the
prefix's total multiplicity count, not merely its critical-line property.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset

namespace XiSignRows

/-- An integral budget for a padded block bounds the actual strict prefix count. -/
theorem Valid.strictCount_le_of_padded_integral {n k : ℕ}
    {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : Valid rows 0 a) (hpad : Valid padding a b)
    (hbudget : (∫ t in (a : ℝ)..(b : ℝ), (xiZeroCount t : ℝ)) <
      (b : ℝ) - a + completedArea (Fin.append rows padding) a b) :
    xiStrictZeroCount (a : ℝ) ≤ n := by
  classical
  have hab : (a : ℝ) ≤ b := by exact_mod_cast hpad.bounds
  obtain ⟨f, hf, hi, hc⟩ := (h.append hpad).exists_cover_of_count_integral hab hbudget
  have hsub : xiStrictPositiveHeightIndices (a : ℝ) ⊆
      univ.image (fun i : Fin n => f (i.castAdd k)) := by
    intro p hp
    have hm := (mem_xiStrictPositiveHeightIndices (a : ℝ) p).mp hp
    obtain ⟨j, _, rfl⟩ := mem_map.mp (hc ((mem_xiPositiveHeightIndices (a : ℝ) p).mpr
      ⟨hm.1, hm.2.le⟩))
    revert hm
    refine Fin.addCases ?_ ?_ j
    · intro i hi'
      exact mem_image.mpr ⟨i, mem_univ i, rfl⟩
    · intro i hi'
      have hlow : (a : ℝ) ≤ (padding i).lower := by exact_mod_cast hpad.lower i
      have hzero := (hi (i.natAdd n)).2.1
      simp only [Fin.append_right] at hzero
      exact (not_lt_of_ge (hlow.trans hzero.le) hi'.2).elim
  exact (card_le_card hsub).trans ((card_image_le).trans_eq (card_fin n))

/-- A rational Turing margin closes the exact count premise for the unpadded prefix. -/
theorem Valid.strictCount_le_of_turing_padding {n k : ℕ}
    {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : Valid rows 0 a) (hpad : Valid padding a b) (ha : 32 ≤ a)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b <
        (b : ℝ) - a + (completedAreaRat (Fin.append rows padding) a b : ℝ)) :
    xiStrictZeroCount (a : ℝ) ≤ n := by
  have har : (32 : ℝ) ≤ a := by exact_mod_cast ha
  have hab : (a : ℝ) ≤ b := by exact_mod_cast hpad.bounds
  have he := integral_xiZeroCountingRemainder (by linarith : (0 : ℝ) < a) hab
  have hb := integral_xiZeroCountingRemainder_le_turingBudget har hab
  apply h.strictCount_le_of_padded_integral hpad
  rw [← cast_completedAreaRat]
  linarith only [he, hb, hmargin]

/-- The Turing margin supplies an exact enclosed enumeration usable by every weight. -/
theorem Valid.exists_weighted_enumeration_of_turing_padding {n k : ℕ}
    {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : Valid rows 0 a) (hpad : Valid padding a b) (ha : 32 ≤ a)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b <
        (b : ℝ) - a + (completedAreaRat (Fin.append rows padding) a b : ℝ)) :
    ∃ f : Fin n → RiemannXiDivisorZeroIndex,
      (∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 ∧
        (riemannXiDivisorZeroValue (f i)).im ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) ∧
      ∀ F : RiemannXiDivisorZeroIndex → ℂ,
        (∑ p ∈ xiLowHeightIndices (a : ℝ), F p) =
          ∑ i, (F (f i) + F (riemannXiDivisorConjugation (f i))) :=
  h.exists_weighted_enumeration le_rfl le_rfl
    (h.strictCount_le_of_turing_padding hpad ha hmargin)

end XiSignRows

end

end PrimeFactorUnimodality
