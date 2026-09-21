import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row293
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row307
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate
import PrimeFactorUnimodality.Proof.FiniteRange.Generated.K11

set_option autoImplicit false
/-! Generated exact certificate for non-unimodality at `k = 12`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive293_307 : ConsecutivePrimes 293 307 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive307_311 : ConsecutivePrimes 307 311 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Exact trial division and coefficient evaluation require an enlarged deterministic budget.
/-- Exact strict-valley data proving non-unimodality for `k = 12`. -/
def k12ExplicitRatioValley : ExplicitRatioValleyCertificate 10 where
  descentPrime := 293
  descentNext := 307
  ascentPrime := 307
  ascentNext := 311
  descentConsecutive := consecutive293_307
  ascentConsecutive := consecutive307_311
  descentBeforeAscent := by norm_num
  ratioDefinedAtDescent := by
    apply le_trans (show 11 ≤ Nat.primeCounting' 32 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  ratioDefinedAtAscent := by
    apply le_trans (show 11 ≤ Nat.primeCounting' 32 by decide)
    exact Nat.monotone_primeCounting' (by norm_num)
  descentRatio := by
    rw [densityRatio_perm primesBelow293_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix293
        primePrefix293_gt_one 11,
      ← selectionRowBounded_getD 12 primePrefix293 (11 - 1) (by omega),
      ← selectionRowBounded_getD 12 primePrefix293 11 (by omega),
      numericalRow293]
    norm_num
  ascentRatio := by
    rw [densityRatio_perm primesBelow307_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix307
        primePrefix307_gt_one 11,
      ← selectionRowBounded_getD 12 primePrefix307 (11 - 1) (by omega),
      ← selectionRowBounded_getD 12 primePrefix307 11 (by omega),
      numericalRow307]
    norm_num

theorem k12PrimeFactorDensity_not_isUnimodal :
    ¬ IsUnimodal (primeFactorDensity 12) := by
  simpa using k12ExplicitRatioValley.not_isUnimodal

end PrimeFactorUnimodality
