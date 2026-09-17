import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row523
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row541
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 15`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive523_541 : ConsecutivePrimes 523 541 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive541_547 : ConsecutivePrimes 541 547 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 15`. -/
def k15ExplicitRatioValley : ExplicitRatioValleyCertificate 13 where
  descentPrime := 523
  descentNext := 541
  ascentPrime := 541
  ascentNext := 547
  descentConsecutive := consecutive523_541
  ascentConsecutive := consecutive541_547
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 14 ≤ Nat.primeCounting' 44 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 14 ≤ Nat.primeCounting' 44 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow523_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix523
        primePrefix523_gt_one 14,
      ← selectionRowBounded_getD 15 primePrefix523 (14 - 1) (by omega),
      ← selectionRowBounded_getD 15 primePrefix523 14 (by omega),
      numericalRow523]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow541_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix541
        primePrefix541_gt_one 14,
      ← selectionRowBounded_getD 15 primePrefix541 (14 - 1) (by omega),
      ← selectionRowBounded_getD 15 primePrefix541 14 (by omega),
      numericalRow541]
    norm_num

theorem k15PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 15) := by
  simpa using k15ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
