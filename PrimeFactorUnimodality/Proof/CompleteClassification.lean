import PrimeFactorUnimodality.Proof.ClassificationThrough38000Closed
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordRange
import PrimeFactorUnimodality.Proof.LargeRange.UniformTail

set_option autoImplicit false

/-! # Complete classification from the explicit analytic inputs -/

namespace PrimeFactorUnimodality

noncomputable section

theorem completeClassification_with_explicit_inputs
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

/-- The same classification packaged as the project's exact universal target.
This wrapper is intentionally parameterized only by the explicit analytic
providers still used by the pointwise assembly theorem. -/
theorem completeClassification_of_explicit_inputs
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate Mertens.M)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    CompleteClassification := by
  intro k hk
    exact completeClassification_with_explicit_inputs primeCountingBounds reciprocalEstimate
    thetaBounds shortInterval k hk

/-! The exact all-`k` reduction after the full published record-gap range is
available.  This is the final finite/tail assembly; only the analytic tail
providers remain parameters here. -/

theorem completeClassification_of_full_record_inputs
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair) :
    CompleteClassification := by
  exact completeClassification_of_finite_range_and_tail
    7430000 (by omega)
    (fun k hk hkRecord => by
      by_cases hkSmall : k ≤ 38000
      · exact completeClassification_through38000_closed k hk hkSmall
      · constructor
        · intro unimodal
          exact ((fullRecordRange_not_isUnimodal_closed k (by omega) hkRecord)
            unimodal).elim
        · intro hkThree
          omega)
    (fun k hkTail => uniformTail_not_isUnimodal_closed_mertens
      primeCountingBounds thetaBounds tailPair (k := k) (by omega))

end

end PrimeFactorUnimodality
