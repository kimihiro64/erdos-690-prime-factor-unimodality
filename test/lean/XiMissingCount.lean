import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiMissingCount

/-! # Exact interfaces and endpoint regressions for integrated zero verification -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset MeasureTheory

open XiSignRows

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

example (S : Finset RiemannXiDivisorZeroIndex) :
    Monotone (xiMissingCount S) := by
  exact PrimeFactorUnimodality.xiMissingCount_mono S

example (S : Finset RiemannXiDivisorZeroIndex) (t : ℝ) :
    xiMissingCount S t + ((xiPositiveHeightIndices t) ∩ S).card = xiZeroCount t := by
  exact PrimeFactorUnimodality.xiMissingCount_add_observed S t

example (a b : ℝ) :
    IntervalIntegrable (fun t => (xiZeroCount t : ℝ)) volume a b := by
  exact PrimeFactorUnimodality.intervalIntegrable_xiZeroCount a b

example (S : Finset RiemannXiDivisorZeroIndex) (a b : ℝ) :
    IntervalIntegrable (fun t => (xiMissingCount S t : ℝ)) volume a b := by
  exact PrimeFactorUnimodality.xiMissingCount_intervalIntegrable S a b

example (S : Finset RiemannXiDivisorZeroIndex)
    {a b : ℝ} (hab : a ≤ b)
    (hbudget : (∫ t in a..b, (xiMissingCount S t : ℝ)) < b - a) : xiMissingCount S a = 0 := by
  exact PrimeFactorUnimodality.xiMissingCount_zero_of_integral_lt S hab hbudget

example (S : Finset RiemannXiDivisorZeroIndex) (t : ℝ) :
    xiMissingCount S t = 0 ↔ xiPositiveHeightIndices t ⊆ S := by
  exact PrimeFactorUnimodality.xiMissingCount_eq_zero_iff S t

example {S : Finset RiemannXiDivisorZeroIndex}
    {a b : ℝ} (hab : a ≤ b)
    (hline : ∀ p ∈ S, (riemannXiDivisorZeroValue p).re = 1 / 2)
    (hbudget : (∫ t in a..b, (xiMissingCount S t : ℝ)) < b - a) :
    ∀ p ∈ xiLowHeightIndices a, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact PrimeFactorUnimodality.xiLow_criticalLine_of_missing_integral hab hline hbudget


example (t : ℝ) : xiMissingCount (xiPositiveHeightIndices t) t = 0 := by
  exact (xiMissingCount_eq_zero_iff _ _).mpr (Finset.Subset.refl _)

example (S : Finset RiemannXiDivisorZeroIndex) {a b : ℝ} (hab : a ≤ b)
    (hpos : xiMissingCount S a ≠ 0) :
    b - a ≤ ∫ t in a..b, (xiMissingCount S t : ℝ) := by
  exact le_of_not_gt (fun h => hpos (xiMissingCount_zero_of_integral_lt S hab h))

example (S : Finset RiemannXiDivisorZeroIndex) (a : ℝ) :
    ¬ ((∫ t in a..a, (xiMissingCount S t : ℝ)) < a - a) := by simp

example (S : Finset RiemannXiDivisorZeroIndex) {t : ℝ} (ht : t ≤ 0) :
    xiMissingCount S t = 0 := by
  apply (xiMissingCount_eq_zero_iff S t).mpr
  intro p hp
  have hm := (mem_xiPositiveHeightIndices t p).mp hp
  exact False.elim (not_lt_of_ge ht (hm.1.trans_le hm.2))

end

end PrimeFactorUnimodality.Tests
