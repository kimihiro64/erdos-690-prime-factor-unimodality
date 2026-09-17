import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row113
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row127
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 11`. -/

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
/-- Exact strict-valley data proving non-unimodality for `k = 11`. -/
def k11ExplicitRatioValley : ExplicitRatioValleyCertificate 9 where
  descentPrime := 113
  descentNext := 127
  ascentPrime := 127
  ascentNext := 131
  descentConsecutive := consecutive113_127
  ascentConsecutive := consecutive127_131
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 10 ≤ Nat.primeCounting' 30 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 10 ≤ Nat.primeCounting' 30 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow113_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix113
        primePrefix113_gt_one 10,
      ← selectionRowBounded_getD 10 primePrefix113 (10 - 1) (by omega),
      ← selectionRowBounded_getD 10 primePrefix113 10 (by omega),
      numericalRow113]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow127_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix127
        primePrefix127_gt_one 10,
      ← selectionRowBounded_getD 10 primePrefix127 (10 - 1) (by omega),
      ← selectionRowBounded_getD 10 primePrefix127 10 (by omega),
      numericalRow127]
    norm_num

theorem k11PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 11) := by
  simpa using k11ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
