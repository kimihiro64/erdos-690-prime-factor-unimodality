import PrimeFactorUnimodality.Proof.ClassificationThrough38000Closed
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction
import PrimeFactorUnimodality.Proof.LargeRange.UniformTail

set_option autoImplicit false

/-! # Complete classification from the explicit analytic inputs -/

namespace PrimeFactorUnimodality

noncomputable section

theorem completeClassification
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate Mertens.M)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime)
    (k : Nat) (hk : 1 ≤ k) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 := by
  by_cases hkFinite : k ≤ 38000
  · exact completeClassification_through38000_closed k hk hkFinite
  · constructor
    · intro unimodal
      exact (uniformTail_not_isUnimodal primeCountingBounds reciprocalEstimate
        mertensConstant_lt_two_thirds.le thetaBounds shortInterval
        (k := k) (by omega)) unimodal
    · intro hkThree
      omega

end

end PrimeFactorUnimodality
