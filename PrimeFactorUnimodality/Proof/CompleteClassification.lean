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
theorem completeClassification_of_full_record_short_interval_inputs
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    CompleteClassification := by
  exact completeClassification_of_full_record_inputs
    (hasDusartPrimeCountingBounds_of_real primeCountingBounds)
    (hasDusartThetaBounds_of_symmetric thetaBounds)
    (hasUniformTailPrimePair_of_shortInterval shortInterval)

theorem completeClassification_of_full_record_interval_certificates
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_short_interval_inputs
    primeCountingBounds thetaBounds
    (hasDusartShortIntervalPrime_of_rows_and_thetaError
      dusartCover logCover thetaError)

theorem completeClassification_of_full_record_fourth_theta_error
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {A : Real}
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (4e18 : Real) ≤ 12167 / 500000)
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogFourthError A (4e18 : Real)) :
    CompleteClassification := by
  have cubic : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real) :=
    hasThetaLogCubedError_of_logFourthError
      (A := A) (X := (4e18 : Real)) (by norm_num) hA_nonneg thetaError
  exact completeClassification_of_full_record_interval_certificates
    primeCountingBounds
    (hasDusartSymmetricThetaBounds_of_below_and_logFourth
      finiteTheta hA_nonneg hA thetaError)
    dusartCover logCover cubic

theorem completeClassification_of_full_record_unit_fourth_theta_error
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogFourthError 1 (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_fourth_theta_error
    primeCountingBounds finiteTheta (by norm_num) (by norm_num)
    dusartCover logCover thetaError

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
  have shortInterval : HasDusartShortIntervalPrime :=
    hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
      rows X hX cover thetaError
  exact completeClassification_of_full_record_short_interval_inputs
    primeCountingBounds thetaBounds shortInterval

theorem completeClassification_of_full_record_rows_at_large_cutoff
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real))
    CompleteClassification := by
  exact completeClassification_of_full_record_bounded_rows
    primeCountingBounds thetaBounds (4e18 : Real) le_rfl cover thetaError

theorem completeClassification_of_full_record_rows_and_finite_theta
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real))
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_at_large_cutoff
    primeCountingBounds
    (hasDusartSymmetricThetaBounds_of_below_and_logCubed finiteTheta thetaError)
    cover thetaError

theorem completeClassification_of_full_record_split_analytic_inputs
    {X : Real}
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (tailPrimeCounting : HasDusartRealPrimeCountingBoundsAbove X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real))
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_below_and_above
      finitePrimeCounting tailPrimeCounting)
    finiteTheta cover thetaError

theorem completeClassification_of_full_record_cutoff_split_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (tailPrimeCounting : HasDusartRealPrimeCountingBoundsAbove (4e18 : Real))
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_split_analytic_inputs
    finitePrimeCounting tailPrimeCounting finiteTheta cover thetaError

/-! The tail prime-counting obligation can equivalently be supplied in the
published asymptotic form.  The adapter is proved in the analytic helper, so
this theorem exposes the exact provider boundary without hiding a new axiom
inside the all-`k` assembly. -/
theorem completeClassification_of_full_record_asymptotic_tail_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real))
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_finite_and_asymptotic
      finitePrimeCounting asymptotic)
    finiteTheta cover thetaError

/-! The tail can be supplied directly by the kernel-checked Abel argument.
This is the all-cutoff boundary used by the eventual explicit provider: no
pre-packaged Dusart asymptotic is assumed here. -/
theorem completeClassification_of_full_record_core_theta_error_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    {A C X : Real} (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hXcutoff : X ≤ (4e18 : Real))
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (coreThetaError : HasThetaLogFourthError A X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_finite_and_core_and_theta_error
      finitePrimeCounting hXpos h2X hXcutoff hA0 hA hC0 hC hlog hcore
      coreThetaError)
    finiteTheta cover thetaError

/-! Once the finite theta and interval rows are supplied, every analytic
interface is now discharged by the explicit proofs above. -/
theorem completeClassification_of_full_record_explicit_dusart_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    {A C X : Real} (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hXcutoff : X ≤ (4e18 : Real))
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (coreThetaError : HasThetaLogFourthError A X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_short_interval_inputs
    (hasDusartRealPrimeCountingBounds_of_finite_and_core_and_theta_error
      finitePrimeCounting hXpos h2X hXcutoff hA0 hA hC0 hC hlog hcore
      coreThetaError)
    (hasDusartThetaBounds_of_symmetric
      (hasDusartSymmetricThetaBounds_of_below_and_logCubed
        finiteTheta thetaError))
    (hasDusartShortIntervalPrime_of_rows_and_thetaError
      dusartCover logCover thetaError)

/-! At the paper's stated cutoff, the same log-fourth theta estimate feeds all
three Dusart interfaces: theta bounds, prime counting, and short intervals. -/
theorem completeClassification_of_full_record_unit_logFourth_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {A C : Real} (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : |primeCountingCore (4e18 : Real)| ≤
      C * (4e18 : Real) / Real.log (4e18 : Real) ^ 4)
    (thetaError : HasThetaLogFourthError A (4e18 : Real))
    (hA_log : A / Real.log (4e18 : Real) ≤ 12167 / 500000)
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)) :
    CompleteClassification := by
  have hlog42 : (42 : Real) ≤ Real.log (4e18 : Real) :=
    forty_two_lt_log_four_e18.le
  have cubic : HasThetaLogCubedError
      (12167 / 500000 : Real) (4e18 : Real) :=
    hasThetaLogCubedError_of_logFourthError
      (by norm_num) hA0 thetaError
  exact completeClassification_of_full_record_short_interval_inputs
    (hasDusartRealPrimeCountingBounds_of_finite_and_core_and_theta_error
      finitePrimeCounting (by norm_num) (by norm_num) le_rfl
      hA0 hA hC0 hC hlog42 hcore thetaError)
    (hasDusartThetaBounds_of_finite_and_logFourth_from
      (by norm_num) (log_large_x_gt_ten le_rfl) finiteTheta hA0 hA_log
      thetaError)
    (hasDusartShortIntervalPrime_of_rows_and_thetaError
      dusartCover logCover cubic)

theorem completeClassification_of_full_record_finite_published_asymptotic_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (finitePublished : HasDusartPublishedPrimeCountingBoundsBelow (4e9 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real))
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_finite_published_and_asymptotic
      finitePrimeCounting finitePublished asymptotic)
    finiteTheta cover thetaError

/-! The same assembly can consume the denominator-form estimates stated in
the Wang--Crapis paper directly.  The conversion to the comparison functions
used by the tail is proved in `ExplicitPrimeCounting`; it is not an
additional analytic hypothesis. -/
theorem completeClassification_of_full_record_published_prime_counting_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (published : HasDusartPublishedPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_below_and_above
      finitePrimeCounting
      (hasDusartRealPrimeCountingBoundsAbove_of_published published))
    finiteTheta cover thetaError

/-! Public assembly with the analytic inputs in the form used by the paper:
the finite prime-counting check is combined with the published tail estimate,
while the theta and short-interval estimates are supplied globally. -/
theorem completeClassification_of_published_analytic_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (published : HasDusartPublishedPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    CompleteClassification := by
  exact completeClassification_of_full_record_short_interval_inputs
    (hasDusartRealPrimeCountingBounds_of_below_and_above
      finitePrimeCounting
      (hasDusartRealPrimeCountingBoundsAbove_of_published published))
    thetaBounds shortInterval

/-! The four inputs in the preceding theorem are exactly the explicit
analytic facts used by the published all-`k` argument.  Bundling them makes
the remaining provider obligation explicit at the public theorem boundary;
none of these fields is synthesized by a project axiom. -/
structure WangCrapisAnalyticInputs : Prop where
  finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real)
  publishedPrimeCounting : HasDusartPublishedPrimeCountingBounds
  thetaBounds : HasDusartSymmetricThetaBounds
  shortInterval : HasDusartShortIntervalPrime

theorem completeClassification_of_wangCrapis_analytic_inputs
    (inputs : WangCrapisAnalyticInputs) :
    CompleteClassification := by
  exact completeClassification_of_published_analytic_inputs
    inputs.finitePrimeCounting inputs.publishedPrimeCounting
    inputs.thetaBounds inputs.shortInterval

/-! The direct paper-facing boundary.  Wang--Crapis state the tail argument
using the prime-counting, Chebyshev-theta, and short-interval estimates
themselves.  This theorem keeps those three statements visible and uses only
the proved structural assembly below them. -/
structure WangCrapisPaperInputs : Prop where
  primeCounting : HasDusartPrimeCountingBounds
  thetaBounds : HasDusartThetaBounds
  shortInterval : HasDusartShortIntervalPrime

theorem completeClassification_of_wangCrapis_paper_inputs
    (inputs : WangCrapisPaperInputs) :
    CompleteClassification := by
  exact completeClassification_of_full_record_inputs
    inputs.primeCounting inputs.thetaBounds
    (hasUniformTailPrimePair_of_shortInterval inputs.shortInterval)

end

end PrimeFactorUnimodality
