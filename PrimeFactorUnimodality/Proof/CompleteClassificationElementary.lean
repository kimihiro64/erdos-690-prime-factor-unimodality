import PrimeFactorUnimodality.Proof.ClassificationThrough48
import PrimeFactorUnimodality.Proof.LargeRange.ElementaryDensityTail
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapClosed
import PrimeFactorUnimodality.Proof.LargeRange.RecordRangeElementary
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinClosed

set_option autoImplicit false

/-! # The unconditional all-k classification

The infinite range follows from the elementary factorial and Mertens argument.
The finite range reuses the existing fixed gap, twin and small-case witnesses.
-/

namespace PrimeFactorUnimodality

theorem completeClassification_elementary : CompleteClassification := by
  intro k hk
  by_cases hsmall : k <= 48
  next => exact completeClassification_through48 k hk hsmall
  next =>
    constructor
    next =>
      intro hu
      by_cases hfinite : k <= 38000
      next =>
        exact False.elim ((recordRange_not_isUnimodal_elementary
          recordGap_primeGap_ge recordGap_predecessor_gt_half recordTwin_consecutive
          k (by omega) hfinite) hu)
      next =>
        exact False.elim ((elementary_tail_not_isUnimodal k (by omega)) hu)
    next =>
      intro hk3
      omega

end PrimeFactorUnimodality
