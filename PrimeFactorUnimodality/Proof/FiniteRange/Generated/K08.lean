import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row89
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row97
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate
import PrimeFactorUnimodality.Proof.FiniteRange.Generated.K07

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 8`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive89_97 : ConsecutivePrimes 89 97 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive97_101 : ConsecutivePrimes 97 101 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 8`. -/
def k8ExplicitRatioValley : ExplicitRatioValleyCertificate 6 where
  descentPrime := 89
  descentNext := 97
  ascentPrime := 97
  ascentNext := 101
  descentConsecutive := consecutive89_97
  ascentConsecutive := consecutive97_101
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 7 ≤ Nat.primeCounting' 18 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 7 ≤ Nat.primeCounting' 18 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow89_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix89
        primePrefix89_gt_one 7,
      ← selectionRowBounded_getD 7 primePrefix89 (7 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix89 7 (by omega),
      numericalRow89]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow97_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix97
        primePrefix97_gt_one 7,
      ← selectionRowBounded_getD 7 primePrefix97 (7 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix97 7 (by omega),
      numericalRow97]
    norm_num

theorem k8PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 8) := by
  simpa using k8ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
