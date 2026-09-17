import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive

set_option autoImplicit false

/-! # Exact prime-gap certificates for the medium finite range -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
theorem consecutive15683_15727 : ConsecutivePrimes 15683 15727 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> norm_num

set_option maxRecDepth 10000 in
theorem consecutive15727_15731 : ConsecutivePrimes 15727 15731 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> norm_num

set_option maxRecDepth 10000 in
theorem consecutive31397_31469 : ConsecutivePrimes 31397 31469 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> norm_num

set_option maxRecDepth 10000 in
theorem consecutive31469_31477 : ConsecutivePrimes 31469 31477 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> norm_num

end PrimeFactorUnimodality
