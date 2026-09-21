import PrimeFactorUnimodality.Proof.CompleteClassificationIntegerProviders

set_option autoImplicit false

/-! # Complete classification certificate interfaces

This module is a source-level split of the complete all-k classification assembly.
-/

namespace PrimeFactorUnimodality

noncomputable section

structure DusartSplitFiniteCertificate (A C x₀ R : Real) : Prop where
  primeCountingRows : List DusartPrimeCountingEndpointRow
  primeCountingCover :
    DusartPrimeCountingEndpointRowsCoverFrom599
      primeCountingRows (4e18 : Real)
  thetaRows : List DusartThetaEndpointRow
  thetaCover :
    DusartThetaEndpointRowsCoverUpTo thetaRows (4e18 : Real)
  logRows : List LogCubedPrimeRow
  logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)
  thetaErrorRows : List (ThetaLogFourthEndpointRow A)
  thetaErrorCover :
    ThetaLogFourthEndpointRowsCoverFrom thetaErrorRows x₀ (4e18 : Real)
  thetaTail : HasThetaLogFourthErrorAbove A (4e18 : Real)
  h2x₀ : (2 : Real) ≤ x₀
  hx₀ : x₀ ≤ (4e18 : Real)
  smallRemainder :
    |∫ t in (2 : Real)..x₀,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R
  hA0 : 0 ≤ A
  hA1 : A ≤ 1
  hC0 : 0 ≤ C
  hC : C ≤ 3 / 5
  integralCoreBound :
    4000 + 720 * (∫ t in (2 : Real)..(4e18 : Real),
        1 / Real.log t ^ 7) + R +
        A * (∫ t in x₀..(4e18 : Real), 1 / Real.log t ^ 6) ≤
      C * (4e18 : Real) / Real.log (4e18 : Real) ^ 4

theorem completeClassification_of_dusart_split_finite_certificate
    {A C x₀ : Real}
    (certificate : DusartSplitFiniteCertificate A C x₀) :
    CompleteClassification := by
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow (4e18 : Real) :=
    hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      certificate.primeCountingCover dusartSmallUpperIntervalRows_provide
  have finiteTheta :
      HasDusartSymmetricThetaBoundsBelow (4e18 : Real) :=
    hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      certificate.thetaCover
  have finiteShortInterval :
      HasLogCubedShortIntervalPrimeBelow (4e18 : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_rows certificate.logCover
  have thetaErrorAbove : HasThetaLogFourthErrorAbove A x₀ :=
    hasThetaLogFourthErrorAbove_of_endpoint_rows_from_and_tail
      certificate.hA0 certificate.thetaErrorCover certificate.thetaTail
  exact completeClassification_of_split_theta_error_and_integral_core
    (by norm_num) certificate.h2x₀ certificate.hx₀ finitePrimeCounting
    finiteTheta finiteShortInterval certificate.hA0 certificate.hA1
    certificate.hC0 certificate.hC certificate.smallRemainder thetaErrorAbove
    certificate.integralCoreBound

structure Dusart599SplitFiniteCertificate (A C : Real) : Prop where
  primeCountingRows : List DusartPrimeCountingEndpointRow
  primeCountingCover :
    DusartPrimeCountingEndpointRowsCoverFrom599
      primeCountingRows (4e18 : Real)
  thetaRows : List DusartThetaEndpointRow
  thetaCover :
    DusartThetaEndpointRowsCoverUpTo thetaRows (4e18 : Real)
  logRows : List LogCubedPrimeRow
  logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)
  thetaErrorRows : List (ThetaLogFourthEndpointRow A)
  thetaErrorCover :
    ThetaLogFourthEndpointRowsCoverFrom thetaErrorRows 599 (4e18 : Real)
  thetaTail : HasThetaLogFourthErrorAbove A (4e18 : Real)
  hA0 : 0 ≤ A
  hA1 : A ≤ 1
  hC0 : 0 ≤ C
  hC : C ≤ 3 / 5
  integralCoreBound :
    4000 + 720 * (∫ t in (2 : Real)..(4e18 : Real),
        1 / Real.log t ^ 7) + 10000 +
        A * (∫ t in (599 : Real)..(4e18 : Real),
          1 / Real.log t ^ 6) ≤
      C * (4e18 : Real) / Real.log (4e18 : Real) ^ 4

theorem completeClassification_of_dusart_599_split_finite_certificate
    {A C : Real}
    (certificate : Dusart599SplitFiniteCertificate A C) :
    CompleteClassification := by
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow (4e18 : Real) :=
    hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      certificate.primeCountingCover dusartSmallUpperIntervalRows_provide
  have finiteTheta :
      HasDusartSymmetricThetaBoundsBelow (4e18 : Real) :=
    hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      certificate.thetaCover
  have finiteShortInterval :
      HasLogCubedShortIntervalPrimeBelow (4e18 : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_rows certificate.logCover
  have thetaErrorAbove : HasThetaLogFourthErrorAbove A (599 : Real) :=
    hasThetaLogFourthErrorAbove_of_endpoint_rows_from_and_tail
      certificate.hA0 certificate.thetaErrorCover certificate.thetaTail
  apply completeClassification_of_split_theta_error_and_reserved_integral_core
    (x₀ := (599 : Real)) (R := 10 * (599 : Real))
  · norm_num
  · norm_num
  · exact finitePrimeCounting
  · exact finiteTheta
  · exact finiteShortInterval
  · exact certificate.hA0
  · exact certificate.hA1
  · exact certificate.hC0
  · exact certificate.hC
  · exact small_integral_remainder_le_5990
  · norm_num
  · exact thetaErrorAbove
  · exact certificate.integralCoreBound

/-! Fixed-cutoff certificate boundary with the analytic core discharged by
the explicit Abel estimate.  The remaining fields are exactly the finite
Dusart rows and the eventual theta-error tail. -/
structure Dusart599FiniteCertificate (A : Real) : Prop where
  primeCountingRows : List DusartPrimeCountingEndpointRow
  primeCountingCover :
    DusartPrimeCountingEndpointRowsCoverFrom599
      primeCountingRows (4e18 : Real)
  thetaRows : List DusartThetaEndpointRow
  thetaCover :
    DusartThetaEndpointRowsCoverUpTo thetaRows (4e18 : Real)
  logRows : List LogCubedPrimeRow
  logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)
  thetaErrorRows : List (ThetaLogFourthEndpointRow A)
  thetaErrorCover :
    ThetaLogFourthEndpointRowsCoverFrom thetaErrorRows 599 (4e18 : Real)
  thetaTail : HasThetaLogFourthErrorAbove A (4e18 : Real)
  hA0 : 0 ≤ A
  hA1 : A ≤ 1

theorem completeClassification_of_dusart_599_finite_certificate
    {A : Real} (certificate : Dusart599FiniteCertificate A) :
    CompleteClassification := by
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow (4e18 : Real) :=
    hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      certificate.primeCountingCover dusartSmallUpperIntervalRows_provide
  have finiteTheta :
      HasDusartSymmetricThetaBoundsBelow (4e18 : Real) :=
    hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      certificate.thetaCover
  have finiteShortInterval :
      HasLogCubedShortIntervalPrimeBelow (4e18 : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_rows certificate.logCover
  have thetaErrorAbove : HasThetaLogFourthErrorAbove A (599 : Real) :=
    hasThetaLogFourthErrorAbove_of_endpoint_rows_from_and_tail
      certificate.hA0 certificate.thetaErrorCover certificate.thetaTail
  exact completeClassification_of_split_theta_error_and_reserved_integral_core
    (by norm_num) (by norm_num) (by norm_num)
    finitePrimeCounting finiteTheta finiteShortInterval certificate.hA0
    certificate.hA1 (by norm_num) (by norm_num)
    small_integral_remainder_le_5990 (by norm_num) thetaErrorAbove
    (explicit_reserved_integral_core_at_599 (by norm_num)
      certificate.hA0 certificate.hA1)

/-! The same fixed-cutoff certificate with indexed finite families.  This is
the compact representation intended for large computational tables: the
kernel checks one finite index type and one coverage theorem per estimate. -/
structure Dusart599IndexedFiniteCertificate : Prop where
  primeCountingRows :
    ∃ n : Nat, ∃ rows : Fin n → DusartPrimeCountingEndpointRow,
      DusartPrimeCountingEndpointIndexedCoverFrom599 rows (4e18 : Real)
  thetaRows :
    ∃ n : Nat, ∃ rows : Fin n → DusartThetaEndpointRow,
      DusartThetaEndpointIndexedCoverUpTo rows (4e18 : Real)
  logRows :
    ∃ n : Nat, ∃ rows : Fin n → LogCubedPrimeRow,
      LogCubedPrimeIndexedCoverUpTo rows (4e18 : Real)
  thetaErrorRows :
    ∃ n : Nat, ∃ rows : Fin n → ThetaLogFourthEndpointRow (648 / 1000 : Real),
      ThetaLogFourthEndpointIndexedCoverFrom rows 599 (4e18 : Real)
  thetaTail : HasThetaLogFourthErrorAbove (648 / 1000 : Real) (4e18 : Real)

theorem Dusart599FiniteCertificate.toIndexed
    (certificate : Dusart599FiniteCertificate (648 / 1000 : Real)) :
    Dusart599IndexedFiniteCertificate := by
  refine {
    primeCountingRows := ⟨certificate.primeCountingRows.length,
      (fun i => certificate.primeCountingRows.get i),
      dusartPrimeCountingEndpointIndexedCover_of_list
        certificate.primeCountingCover⟩
    thetaRows := ⟨certificate.thetaRows.length,
      (fun i => certificate.thetaRows.get i),
      dusartThetaEndpointIndexedCover_of_list certificate.thetaCover⟩
    logRows := ⟨certificate.logRows.length,
      (fun i => certificate.logRows.get i),
      logCubedPrimeIndexedCover_of_list certificate.logCover⟩
    thetaErrorRows := ⟨certificate.thetaErrorRows.length,
      (fun i => certificate.thetaErrorRows.get i),
      thetaLogFourthEndpointIndexedCover_of_list certificate.thetaErrorCover⟩
    thetaTail := certificate.thetaTail }

theorem completeClassification_of_dusart_599_indexed_finite_certificate
    (certificate : Dusart599IndexedFiniteCertificate) :
    CompleteClassification := by
  obtain ⟨nPrime, primeRows, primeCover⟩ := certificate.primeCountingRows
  obtain ⟨nTheta, thetaRows, thetaCover⟩ := certificate.thetaRows
  obtain ⟨nLog, logRows, logCover⟩ := certificate.logRows
  obtain ⟨nError, errorRows, errorCover⟩ := certificate.thetaErrorRows
  have finitePrimeCounting :
    HasDusartRealPrimeCountingBoundsBelow (4e18 : Real) :=
    hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
      primeCover
      dusartSmallUpperIntervalRows_provide
  have finiteTheta :
    HasDusartSymmetricThetaBoundsBelow (4e18 : Real) :=
    hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows
      thetaCover
  have finiteShortInterval :
    HasLogCubedShortIntervalPrimeBelow (4e18 : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_indexed_rows
      logCover
  have thetaErrorAbove :
    HasThetaLogFourthErrorAbove (648 / 1000 : Real) (599 : Real) :=
    hasThetaLogFourthErrorAbove_of_indexed_endpoint_rows_from_and_tail
      (by norm_num) errorCover
      certificate.thetaTail
  exact completeClassification_of_split_theta_error_and_reserved_integral_core
    (by norm_num) (by norm_num) (by norm_num) finitePrimeCounting
    finiteTheta finiteShortInterval (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) small_integral_remainder_le_5990
    (by norm_num) thetaErrorAbove
    (explicit_reserved_integral_core_at_599 (by norm_num)
      (by norm_num) (by norm_num))

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
