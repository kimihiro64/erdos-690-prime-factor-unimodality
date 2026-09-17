import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row113
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row127
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 9`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive113_127 : ConsecutivePrimes 113 127 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive127_131 : ConsecutivePrimes 127 131 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 9`. -/
def k9ExplicitRatioValley : ExplicitRatioValleyCertificate 7 where
  descentPrime := 113
  descentNext := 127
  ascentPrime := 127
  ascentNext := 131
  descentConsecutive := consecutive113_127
  ascentConsecutive := consecutive127_131
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 8 ≤ Nat.primeCounting' 20 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 8 ≤ Nat.primeCounting' 20 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow113_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix113
        primePrefix113_gt_one 8,
      ← selectionRowBounded_getD 10 primePrefix113 (8 - 1) (by omega),
      ← selectionRowBounded_getD 10 primePrefix113 8 (by omega),
      numericalRow113]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow127_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix127
        primePrefix127_gt_one 8,
      ← selectionRowBounded_getD 10 primePrefix127 (8 - 1) (by omega),
      ← selectionRowBounded_getD 10 primePrefix127 8 (by omega),
      numericalRow127]
    norm_num

theorem k9PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 9) := by
  simpa using k9ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
