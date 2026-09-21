import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row23
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row29
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate
import PrimeFactorUnimodality.Proof.FiniteRange.Generated.K04

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 5`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive23_29 : ConsecutivePrimes 23 29 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive29_31 : ConsecutivePrimes 29 31 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 5`. -/
def k5ExplicitRatioValley : ExplicitRatioValleyCertificate 3 where
  descentPrime := 23
  descentNext := 29
  ascentPrime := 29
  ascentNext := 31
  descentConsecutive := consecutive23_29
  ascentConsecutive := consecutive29_31
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 4 ≤ Nat.primeCounting' 8 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 4 ≤ Nat.primeCounting' 8 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow23_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix23
        primePrefix23_gt_one 4,
      ← selectionRowBounded_getD 4 primePrefix23 (4 - 1) (by omega),
      ← selectionRowBounded_getD 4 primePrefix23 4 (by omega),
      numericalRow23]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow29_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix29
        primePrefix29_gt_one 4,
      ← selectionRowBounded_getD 4 primePrefix29 (4 - 1) (by omega),
      ← selectionRowBounded_getD 4 primePrefix29 4 (by omega),
      numericalRow29]
    norm_num

theorem k5PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 5) := by
  simpa using k5ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
