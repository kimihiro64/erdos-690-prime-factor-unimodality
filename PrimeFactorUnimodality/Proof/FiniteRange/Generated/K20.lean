import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row1129
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row1151
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate
import PrimeFactorUnimodality.Proof.FiniteRange.Generated.K19

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 20`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1129_1151 : ConsecutivePrimes 1129 1151 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1151_1153 : ConsecutivePrimes 1151 1153 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 20`. -/
def k20ExplicitRatioValley : ExplicitRatioValleyCertificate 18 where
  descentPrime := 1129
  descentNext := 1151
  ascentPrime := 1151
  ascentNext := 1153
  descentConsecutive := consecutive1129_1151
  ascentConsecutive := consecutive1151_1153
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 19 ≤ Nat.primeCounting' 68 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 19 ≤ Nat.primeCounting' 68 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow1129_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix1129
        primePrefix1129_gt_one 19,
      ← selectionRowBounded_getD 19 primePrefix1129 (19 - 1) (by omega),
      ← selectionRowBounded_getD 19 primePrefix1129 19 (by omega),
      numericalRow1129]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow1151_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix1151
        primePrefix1151_gt_one 19,
      ← selectionRowBounded_getD 19 primePrefix1151 (19 - 1) (by omega),
      ← selectionRowBounded_getD 19 primePrefix1151 19 (by omega),
      numericalRow1151]
    norm_num

theorem k20PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 20) := by
  simpa using k20ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
