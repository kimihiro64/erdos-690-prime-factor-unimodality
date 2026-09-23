import PrimeFactorUnimodality.Helpers.Analytic.XiCompletedRows
import PrimeFactorUnimodality.Helpers.Analytic.XiCountingIntegral

/-! # Integral count budgets prove completeness of critical-line rows

Unknown interior zero positions are replaced by rational upper endpoints.
The exact completed-row integral bounds the observed count from below;
the missing-count theorem then excludes any omitted lower-cutoff label.
The error-budget form allows an explicitly integrated smooth counting model.
Both forms retain their analytic integral estimate as an unproved input.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset MeasureTheory

local instance xiIntegralVerificationDecidableEq : DecidableEq RiemannXiDivisorZeroIndex :=
  Classical.decEq _

namespace XiSignRows

/-- An integral budget covers every lower-cutoff label by the same enclosed row family. -/
theorem Valid.exists_cover_of_count_integral {n : ℕ} {rows : Fin n → XiSignRow}
    {a : ℝ} {b : ℚ} (h : Valid rows 0 b) (hab : a ≤ (b : ℝ))
    (hbudget : (∫ t in a..(b : ℝ), (xiZeroCount t : ℝ)) <
      (b : ℝ) - a + completedArea rows a b) :
    ∃ (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f),
      (∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 ∧
        (riemannXiDivisorZeroValue (f i)).im ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) ∧
      xiPositiveHeightIndices a ⊆ univ.map ⟨f, hf⟩ := by
  classical
  obtain ⟨f, hf, hv⟩ := h.exists_indices
  let S := univ.image f
  have hpos (i : Fin n) : 0 < (riemannXiDivisorZeroValue (f i)).im := by
    have hl : (0 : ℝ) ≤ (rows i).lower := by exact_mod_cast h.lower i
    exact hl.trans_lt (hv i).2.1
  have hupper (i : Fin n) : (riemannXiDivisorZeroValue (f i)).im ≤ (rows i).upper :=
    (hv i).2.2.le
  have hbound (t : ℝ) : (xiMissingCount S t : ℝ) ≤
      (xiZeroCount t : ℝ) - completedCount rows t := by
    have hn := missing_add_completed_le rows f hf hpos hupper t
    have hr : (xiMissingCount S t : ℝ) + completedCount rows t ≤ (xiZeroCount t : ℝ) := by
      dsimp only [S]
      exact_mod_cast hn
    linarith only [hr]
  have hN := intervalIntegrable_xiZeroCount a (b : ℝ)
  have hC : IntervalIntegrable (fun t => (completedCount rows t : ℝ)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (integrableOn_completedCount rows a b)
  have hcomp := intervalIntegral.integral_mono_on hab
    (xiMissingCount_intervalIntegrable S a b) (hN.sub hC) (fun t _ => hbound t)
  rw [intervalIntegral.integral_sub hN hC,
    integral_completedCount rows hab (fun i => by exact_mod_cast h.upper i)] at hcomp
  have hcover := (xiMissingCount_eq_zero_iff S a).mp
    (xiMissingCount_zero_of_integral_lt S hab (by linarith only [hcomp, hbudget]))
  refine ⟨f, hf, hv, ?_⟩
  intro p hp
  obtain ⟨i, hi, rfl⟩ := mem_image.mp (hcover hp)
  exact mem_map.mpr ⟨i, hi, rfl⟩

/-- A full-count integral budget and ordered signs imply finite critical-line completeness. -/
theorem Valid.low_criticalLine_of_count_integral {n : ℕ} {rows : Fin n → XiSignRow}
    {a : ℝ} {b : ℚ} (h : Valid rows 0 b) (hab : a ≤ (b : ℝ))
    (hbudget : (∫ t in a..(b : ℝ), (xiZeroCount t : ℝ)) <
      (b : ℝ) - a + completedArea rows a b) :
    ∀ p ∈ xiLowHeightIndices a, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  obtain ⟨f, hf, hi, hc⟩ := h.exists_cover_of_count_integral hab hbudget
  apply xiLow_criticalLine_of_positive
  intro p hp
  have hm := (mem_xiStrictPositiveHeightIndices a p).mp hp
  obtain ⟨i, _, rfl⟩ := mem_map.mp (hc ((mem_xiPositiveHeightIndices a p).mpr
    ⟨hm.1, hm.2.le⟩))
  exact (hi i).1

/-- A bound for the discrepancy from any integrable counting model supplies the full-count budget. -/
theorem Valid.low_criticalLine_of_error_integral {n : ℕ} {rows : Fin n → XiSignRow}
    {a E : ℝ} {b : ℚ} (h : Valid rows 0 b) (hab : a ≤ (b : ℝ))
    (F : ℝ → ℝ) (hF : IntervalIntegrable F volume a b)
    (herror : (∫ t in a..(b : ℝ), ((xiZeroCount t : ℝ) - F t)) ≤ E)
    (hmargin : (∫ t in a..(b : ℝ), F t) + E < (b : ℝ) - a + completedArea rows a b) :
    ∀ p ∈ xiLowHeightIndices a, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  apply h.low_criticalLine_of_count_integral hab
  rw [intervalIntegral.integral_sub (intervalIntegrable_xiZeroCount a b) hF] at herror
  linarith only [herror, hmargin]

/-- The actual counting discrepancy and a rational endpoint sum give a completeness test. -/
theorem Valid.low_criticalLine_of_remainder_integral {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} {E : ℝ} (h : Valid rows 0 b) (ha : 0 < a) (hab : a ≤ b)
    (herror : (∫ t in (a : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a + E <
      (b : ℝ) - a + (completedAreaRat rows a b : ℝ)) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
  apply h.low_criticalLine_of_error_integral habr xiZeroCountingMainTerm
    (intervalIntegrable_xiZeroCountingMainTerm har habr) herror
  rw [integral_xiZeroCountingMainTerm har habr, ← cast_completedAreaRat]
  exact hmargin

end XiSignRows

end

end PrimeFactorUnimodality
