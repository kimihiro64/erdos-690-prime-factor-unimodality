import PrimeFactorUnimodality.Helpers.Analytic.XiMissingCount

/-! # Explicit endpoint sums bound the integrated witnessed count

A row whose upper endpoint has been passed has already contributed its
interior zero. These completed rows give a lower count without representing
the unknown zero locations. Their integral is a finite clipped endpoint sum,
retaining each row once and including rows ending before the integration range.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset MeasureTheory

local instance xiCompletedRowsDecidableEq : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

namespace XiSignRows

/-- Rows whose entire ordinate interval has been passed by height `t`. -/
def completedCount {n : ℕ} (rows : Fin n → XiSignRow) (t : ℝ) : ℕ :=
  (univ.filter (fun i => ((rows i).upper : ℝ) ≤ t)).card

/-- Each completed row contributes its remaining interval length, clipped at the lower cutoff. -/
def completedArea {n : ℕ} (rows : Fin n → XiSignRow) (a b : ℝ) : ℝ :=
  ∑ i : Fin n, (b - max a ((rows i).upper : ℝ))

/-- Rational cutoffs make the complete endpoint sum rational as well. -/
def completedAreaRat {n : ℕ} (rows : Fin n → XiSignRow) (a b : ℚ) : ℚ :=
  ∑ i : Fin n, (b - max a (rows i).upper)

/-- Casting the rational sum gives the actual real integral budget exactly. -/
theorem cast_completedAreaRat {n : ℕ} (rows : Fin n → XiSignRow) (a b : ℚ) :
    (completedAreaRat rows a b : ℝ) = completedArea rows a b := by
  simp [completedAreaRat, completedArea, Rat.cast_max]

/-- Independently checked blocks combine their rational budgets without replaying their signs. -/
theorem completedAreaRat_append {n m : ℕ} (rows : Fin n → XiSignRow) (next : Fin m → XiSignRow)
    (a b : ℚ) : completedAreaRat (Fin.append rows next) a b =
      completedAreaRat rows a b + completedAreaRat next a b := by
  simp [completedAreaRat, Fin.sum_univ_add]
  ring

/-- The completed-row count is integrable on any compact interval. -/
theorem integrableOn_completedCount {n : ℕ} (rows : Fin n → XiSignRow) (a b : ℝ) :
    IntegrableOn (fun t => (completedCount rows t : ℝ)) (Set.Icc a b) :=
  Finset.integrableOn_count_le univ (fun i => ((rows i).upper : ℝ))

/-- The integrated row count is exactly its clipped endpoint sum. -/
theorem integral_completedCount {n : ℕ} (rows : Fin n → XiSignRow) {a b : ℝ} (hab : a ≤ b)
    (hr : ∀ i, ((rows i).upper : ℝ) ≤ b) :
    (∫ t in a..b, (completedCount rows t : ℝ)) = completedArea rows a b := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact Finset.integral_count_le_eq_sum_sub_max univ (fun i => ((rows i).upper : ℝ)) hab
    (fun i _ => hr i)

/-- Distinct positive-height witnesses give at least one observed label per completed row. -/
theorem missing_add_completed_le {n : ℕ} (rows : Fin n → XiSignRow)
    (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f)
    (hpos : ∀ i, 0 < (riemannXiDivisorZeroValue (f i)).im)
    (hupper : ∀ i, (riemannXiDivisorZeroValue (f i)).im ≤ (rows i).upper) (t : ℝ) :
    xiMissingCount (univ.image f) t + completedCount rows t ≤ xiZeroCount t := by
  classical
  have hsub : (univ.filter (fun i => ((rows i).upper : ℝ) ≤ t)).image f ⊆
      xiPositiveHeightIndices t ∩ univ.image f := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact mem_inter.mpr
      ⟨(mem_xiPositiveHeightIndices t (f i)).mpr
        ⟨hpos i, (hupper i).trans (mem_filter.mp hi).2⟩,
        mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hf] at hc
  exact (Nat.add_le_add_left hc _).trans_eq (xiMissingCount_add_observed (univ.image f) t)

end XiSignRows

end

end PrimeFactorUnimodality
