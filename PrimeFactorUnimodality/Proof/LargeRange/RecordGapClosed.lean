import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapFermatFast
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapConsequence
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverage

set_option autoImplicit false

/-!
# Closed record-gap block

This module combines the divisor certificates with the single independently
replayed Fermat witness.  The result is the complete interval statement used
by the large-range density argument.
-/

namespace PrimeFactorUnimodality

/-- Every one of the `4,751` consecutive offsets in the certified block gives
a composite integer. -/
theorem recordGapBlock_not_prime (d : Nat) (lower : 81649 ≤ d)
    (upper : d ≤ 86399) : ¬(recordGapCenter - d).Prime := by
  by_cases exceptional : d = 84672
  · subst d
    exact recordGapExceptional_not_prime_fast
  · exact recordGapCoverage d lower upper exceptional

/-- The closed block forces an adjacent-prime gap of at least `4,752`. -/
theorem recordGap_primeGap_ge :
    4752 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 86399) - 1) :=
  recordGap_primeGap_ge_of_block recordGapBlock_not_prime

/-- The prime immediately before the certified composite block is still at
least half the block's enormous location.  This supplies a convenient lower
endpoint for later reciprocal-prime estimates without certifying either
historical record-gap endpoint. -/
theorem recordGap_predecessor_gt_half :
    (recordGapCenter - 86399) / 2 <
      primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1) := by
  exact recordGap_predecessor_gt_half_of_block recordGapBlock_not_prime

end PrimeFactorUnimodality
