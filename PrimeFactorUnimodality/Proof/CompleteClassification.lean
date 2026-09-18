import PrimeFactorUnimodality.Proof.ClassificationThrough38000Closed
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordRange
import PrimeFactorUnimodality.Proof.LargeRange.UniformTail
import PrimeFactorUnimodality.Proof.LargeRange.TailErrorBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime

set_option autoImplicit false

/-! # Complete classification from the explicit analytic inputs -/

namespace PrimeFactorUnimodality

noncomputable section

theorem completeClassification_with_explicit_inputs
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate Mertens.M)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair)
    (k : Nat) (hk : 1 ≤ k) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 := by
  by_cases hkFinite : k ≤ 38000
  · exact completeClassification_through38000_closed k hk hkFinite
  · constructor
    · intro unimodal
      exact (uniformTail_not_isUnimodal primeCountingBounds reciprocalEstimate
        mertensConstant_lt_two_thirds.le thetaBounds tailPair
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
    (tailPair : HasUniformTailPrimePair) :
    CompleteClassification := by
  intro k hk
    exact completeClassification_with_explicit_inputs primeCountingBounds reciprocalEstimate
    thetaBounds tailPair k hk

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

/-! This is the public all-`k` assembly in the analytic forms used by the
published estimates: real-variable prime counting, symmetric theta error,
and a logarithm-cubed prime interval. -/
theorem completeClassification_of_full_record_logCubed_inputs
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    (shortInterval : HasLogCubedShortIntervalPrime) :
    CompleteClassification := by
  exact completeClassification_of_full_record_inputs
    (hasDusartPrimeCountingBounds_of_real primeCountingBounds)
    (hasDusartThetaBounds_of_symmetric thetaBounds)
    (hasUniformTailPrimePair_of_logCubedShortInterval shortInterval)

/-! The finite-row presentation is the concrete form needed by the eventual
analytic provider: it keeps the medium range as one bounded cover and uses
the proved theta-error implication above the cutoff. -/
theorem completeClassification_of_full_record_bounded_rows
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    {rows : List LogCubedPrimeRow}
    (X : Real) (hX : (4e18 : Real) ≤ X)
    (cover : LogCubedPrimeRowsCoverUpTo rows X)
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_logCubed_inputs
    primeCountingBounds thetaBounds
    (hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
      X hX cover thetaError)

end

end PrimeFactorUnimodality
