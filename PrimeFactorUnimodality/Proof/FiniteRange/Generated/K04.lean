import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row13
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row17
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 4`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive13_17 : ConsecutivePrimes 13 17 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive17_19 : ConsecutivePrimes 17 19 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 4`. -/
def k4ExplicitRatioValley : ExplicitRatioValleyCertificate 2 where
  descentPrime := 13
  descentNext := 17
  ascentPrime := 17
  ascentNext := 19
  descentConsecutive := consecutive13_17
  ascentConsecutive := consecutive17_19
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 3 ≤ Nat.primeCounting' 6 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 3 ≤ Nat.primeCounting' 6 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow13_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix13
        primePrefix13_gt_one 3,
      ← selectionRowBounded_getD 3 primePrefix13 (3 - 1) (by omega),
      ← selectionRowBounded_getD 3 primePrefix13 3 (by omega),
      numericalRow13]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow17_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix17
        primePrefix17_gt_one 3,
      ← selectionRowBounded_getD 3 primePrefix17 (3 - 1) (by omega),
      ← selectionRowBounded_getD 3 primePrefix17 3 (by omega),
      numericalRow17]
    norm_num

theorem k4PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 4) := by
  simpa using k4ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
