import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row31
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row37
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 6`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive31_37 : ConsecutivePrimes 31 37 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive37_41 : ConsecutivePrimes 37 41 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 6`. -/
def k6ExplicitRatioValley : ExplicitRatioValleyCertificate 4 where
  descentPrime := 31
  descentNext := 37
  ascentPrime := 37
  ascentNext := 41
  descentConsecutive := consecutive31_37
  ascentConsecutive := consecutive37_41
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 5 ≤ Nat.primeCounting' 12 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 5 ≤ Nat.primeCounting' 12 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow31_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix31
        primePrefix31_gt_one 5,
      ← selectionRowBounded_getD 5 primePrefix31 (5 - 1) (by omega),
      ← selectionRowBounded_getD 5 primePrefix31 5 (by omega),
      numericalRow31]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow37_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix37
        primePrefix37_gt_one 5,
      ← selectionRowBounded_getD 5 primePrefix37 (5 - 1) (by omega),
      ← selectionRowBounded_getD 5 primePrefix37 5 (by omega),
      numericalRow37]
    norm_num

theorem k6PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 6) := by
  simpa using k6ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
