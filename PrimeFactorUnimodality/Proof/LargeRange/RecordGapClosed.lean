import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapKernelValue
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapConsequence
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverage

set_option autoImplicit false

/-!
# Closed record-gap block

This module combines the divisor certificates with a compact kernel-checked
Fermat witness. The result is the complete interval statement used
by the large-range density argument.
-/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- Match the factored record-gap integer to the fixed computational input. -/
theorem recordGapExceptional_eq_kernelValue :
    recordGapExceptional = recordGapCompactProbeValue := by
  rfl

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The binary algorithm computes the same fixed Fermat witness in the kernel.
Its correctness theorem supplies the mathematical compositeness proof. -/
theorem recordGapExceptional_not_prime_compact :
    Not (Nat.Prime recordGapExceptional) := by
  rw [recordGapExceptional_eq_kernelValue]
  exact recordGapCompactProbeValue_not_prime

/-- Every one of the `4,751` consecutive offsets in the certified block gives
a composite integer. -/
theorem recordGapBlock_not_prime (d : Nat) (lower : 81649 <= d)
    (upper : d <= 86399) : Not ((recordGapCenter - d).Prime) := by
  by_cases exceptional : d = 84672
  case pos =>
    subst d
    exact recordGapExceptional_not_prime_compact
  case neg =>
    exact recordGapCoverage d lower upper exceptional

/-- The closed block forces an adjacent-prime gap of at least `4,752`. -/
theorem recordGap_primeGap_ge :
    4752 <= primeGap (Nat.primeCounting' (recordGapCenter - 86399) - 1) :=
  recordGap_primeGap_ge_of_block recordGapBlock_not_prime

/-- The prime immediately before the certified composite block is still at
least half the block's enormous location. This supplies a convenient lower
endpoint for later reciprocal-prime estimates without certifying either
historical record-gap endpoint. -/
theorem recordGap_predecessor_gt_half :
    (recordGapCenter - 86399) / 2 <
      primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1) := by
  exact recordGap_predecessor_gt_half_of_block recordGapBlock_not_prime

end PrimeFactorUnimodality
