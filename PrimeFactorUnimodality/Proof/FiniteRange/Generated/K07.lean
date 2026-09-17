import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row73
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row79
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 7`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive73_79 : ConsecutivePrimes 73 79 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive79_83 : ConsecutivePrimes 79 83 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 7`. -/
def k7ExplicitRatioValley : ExplicitRatioValleyCertificate 5 where
  descentPrime := 73
  descentNext := 79
  ascentPrime := 79
  ascentNext := 83
  descentConsecutive := consecutive73_79
  ascentConsecutive := consecutive79_83
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 6 ≤ Nat.primeCounting' 14 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 6 ≤ Nat.primeCounting' 14 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow73_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix73
        primePrefix73_gt_one 6,
      ← selectionRowBounded_getD 6 primePrefix73 (6 - 1) (by omega),
      ← selectionRowBounded_getD 6 primePrefix73 6 (by omega),
      numericalRow73]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow79_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix79
        primePrefix79_gt_one 6,
      ← selectionRowBounded_getD 6 primePrefix79 (6 - 1) (by omega),
      ← selectionRowBounded_getD 6 primePrefix79 6 (by omega),
      numericalRow79]
    norm_num

theorem k7PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 7) := by
  simpa using k7ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
