import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row887
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row907
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 19`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive887_907 : ConsecutivePrimes 887 907 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive907_911 : ConsecutivePrimes 907 911 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 19`. -/
def k19ExplicitRatioValley : ExplicitRatioValleyCertificate 17 where
  descentPrime := 887
  descentNext := 907
  ascentPrime := 907
  ascentNext := 911
  descentConsecutive := consecutive887_907
  ascentConsecutive := consecutive907_911
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 18 ≤ Nat.primeCounting' 62 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 18 ≤ Nat.primeCounting' 62 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow887_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix887
        primePrefix887_gt_one 18,
      ← selectionRowBounded_getD 18 primePrefix887 (18 - 1) (by omega),
      ← selectionRowBounded_getD 18 primePrefix887 18 (by omega),
      numericalRow887]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow907_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix907
        primePrefix907_gt_one 18,
      ← selectionRowBounded_getD 18 primePrefix907 (18 - 1) (by omega),
      ← selectionRowBounded_getD 18 primePrefix907 18 (by omega),
      numericalRow907]
    norm_num

theorem k19PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 19) := by
  simpa using k19ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
