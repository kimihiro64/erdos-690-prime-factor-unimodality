import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiCompletedRows

/-! # Exact interfaces and endpoint regressions for integrated zero verification -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset MeasureTheory

open XiSignRows

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

example {n : ℕ} (rows : Fin n → XiSignRow) (a b : ℚ) :
    (completedAreaRat rows a b : ℝ) = completedArea rows a b := by
  exact PrimeFactorUnimodality.XiSignRows.cast_completedAreaRat rows a b

example {n m : ℕ} (rows : Fin n → XiSignRow) (next : Fin m → XiSignRow)
    (a b : ℚ) : completedAreaRat (Fin.append rows next) a b =
      completedAreaRat rows a b + completedAreaRat next a b := by
  exact PrimeFactorUnimodality.XiSignRows.completedAreaRat_append rows next a b

example {n : ℕ} (rows : Fin n → XiSignRow) (a b : ℝ) :
    IntegrableOn (fun t => (completedCount rows t : ℝ)) (Set.Icc a b) := by
  exact PrimeFactorUnimodality.XiSignRows.integrableOn_completedCount rows a b

example {n : ℕ} (rows : Fin n → XiSignRow) {a b : ℝ} (hab : a ≤ b)
    (hr : ∀ i, ((rows i).upper : ℝ) ≤ b) :
    (∫ t in a..b, (completedCount rows t : ℝ)) = completedArea rows a b := by
  exact PrimeFactorUnimodality.XiSignRows.integral_completedCount rows hab hr

example {n : ℕ} (rows : Fin n → XiSignRow)
    (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f)
    (hpos : ∀ i, 0 < (riemannXiDivisorZeroValue (f i)).im)
    (hupper : ∀ i, (riemannXiDivisorZeroValue (f i)).im ≤ (rows i).upper) (t : ℝ) :
    xiMissingCount (univ.image f) t + completedCount rows t ≤ xiZeroCount t := by
  exact PrimeFactorUnimodality.XiSignRows.missing_add_completed_le rows f hf hpos hupper t


example (a b t : ℝ) :
    completedCount (fun i : Fin 0 => Fin.elim0 i) t = 0 ∧
      completedArea (fun i : Fin 0 => Fin.elim0 i) a b = 0 := by
  simp [completedCount, completedArea]

example : completedCount (fun _ : Fin 1 => (⟨1, 2⟩ : XiSignRow)) (2 : ℝ) = 1 := by
  norm_num [completedCount]

example : completedAreaRat (fun _ : Fin 2 => (⟨0, 1⟩ : XiSignRow)) 2 4 = 4 := by
  norm_num [completedAreaRat]

example : completedAreaRat (fun _ : Fin 1 => (⟨2, 4⟩ : XiSignRow)) 2 4 = 0 := by
  norm_num [completedAreaRat]

example : (∫ t in (3 : ℝ)..1,
    (completedCount (fun _ : Fin 1 => (⟨1, 2⟩ : XiSignRow)) t : ℝ)) = -1 := by
  rw [intervalIntegral.integral_symm,
    integral_completedCount _ (by norm_num) (by norm_num)]
  norm_num [completedArea]

end

end PrimeFactorUnimodality.Tests
