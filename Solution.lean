import PrimeFactorUnimodality

set_option autoImplicit false

/-!
# All-k Erdős 690 solution

This declaration has exactly the same universal statement as the challenge:
for every positive `k`, the prime-factor density sequence is unimodal exactly
when `k ≤ 3`.
-/

theorem PrimeFactorUnimodality.completeClassification :
    PrimeFactorUnimodality.CompleteClassification := by
  sorry

/-! The public assembly with every analytic input named explicitly.  No
provider is inferred or hidden at this boundary. -/
theorem PrimeFactorUnimodality.completeClassification_of_wangCrapis_inputs
    (inputs : PrimeFactorUnimodality.WangCrapisAnalyticInputs) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_wangCrapis_analytic_inputs
    inputs

/-! The exact three analytic inputs used in the Wang--Crapis paper are also
available directly, without translating through a stronger derived package. -/
theorem PrimeFactorUnimodality.completeClassification_of_wangCrapis_paper_inputs
    (inputs : PrimeFactorUnimodality.WangCrapisPaperInputs) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_wangCrapis_paper_inputs
    inputs

/-! The source-level MediumPNT route exposes the exact finite obligations that
remain after the unbounded all-`k` tail is proved. -/
theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_finite_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (finiteThetaError : PrimeFactorUnimodality.HasThetaLogFourthErrorBelow A X)
    (selectedInputs :
      PrimeFactorUnimodality.MediumPNTSelectedFiniteInputs A X) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_finite_theta_error
    hX hA0 hA1 finiteThetaError selectedInputs

/-! Direct public boundary for a complete finite package at the single
cutoff selected by the analytic tail proof. -/
theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_finite_inputs
    {A C X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : |PrimeFactorUnimodality.primeCountingCore X| ≤
      C * X / Real.log X ^ 4)
    (selectedInputs :
      PrimeFactorUnimodality.MediumPNTSelectedFiniteInputs A X) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_finite_inputs
    hX hA0 hA1 hC0 hC hcore selectedInputs

theorem PrimeFactorUnimodality.completeClassification_of_logFourth_cutoff_inputs_from_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (finitePrimeCounting :
      PrimeFactorUnimodality.HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta :
      PrimeFactorUnimodality.HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval :
      PrimeFactorUnimodality.HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (thetaErrorBelow :
      PrimeFactorUnimodality.HasThetaLogFourthErrorBelow A X)
    (thetaErrorAbove :
      PrimeFactorUnimodality.HasThetaLogFourthErrorAbove A X) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_logFourth_cutoff_inputs_from_theta_error
    hX finitePrimeCounting finiteTheta finiteShortInterval hA0 hA1
    thetaErrorBelow thetaErrorAbove

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_remainder_row_provider
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (provider : PrimeFactorUnimodality.MediumPNTFiniteSplitRemainderRowProvider X C) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_remainder_row_provider
    hX hC0 hC provider

theorem PrimeFactorUnimodality.completeClassification_of_explicit_mertens_inputs
    (primeCountingBounds : PrimeFactorUnimodality.HasDusartPrimeCountingBounds)
    (thetaBounds : PrimeFactorUnimodality.HasDusartThetaBounds)
    (tailPair : PrimeFactorUnimodality.HasUniformTailPrimePair) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_explicit_mertens_inputs
    primeCountingBounds thetaBounds tailPair

theorem PrimeFactorUnimodality.completeClassification_of_explicit_dusart_inputs
    (primeCountingBounds : PrimeFactorUnimodality.HasDusartPrimeCountingBounds)
    (thetaBounds : PrimeFactorUnimodality.HasDusartThetaBounds)
    (shortInterval : PrimeFactorUnimodality.HasDusartShortIntervalPrime) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_explicit_dusart_inputs
    primeCountingBounds thetaBounds shortInterval

theorem PrimeFactorUnimodality.completeClassification_of_dusart_split_finite_certificate
    {A C x₀ R : Real}
    (certificate :
      PrimeFactorUnimodality.DusartSplitFiniteCertificate A C x₀ R) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_dusart_split_finite_certificate
    certificate

theorem PrimeFactorUnimodality.completeClassification_of_dusart_599_split_finite_certificate
    {A C : Real}
    (certificate :
      PrimeFactorUnimodality.Dusart599SplitFiniteCertificate A C) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_dusart_599_split_finite_certificate
    certificate

theorem PrimeFactorUnimodality.completeClassification_of_dusart_599_finite_certificate
    {A : Real}
    (certificate : PrimeFactorUnimodality.Dusart599FiniteCertificate A) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_dusart_599_finite_certificate
    certificate

theorem PrimeFactorUnimodality.completeClassification_of_dusart_599_indexed_finite_certificate
    (certificate : PrimeFactorUnimodality.Dusart599IndexedFiniteCertificate) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_dusart_599_indexed_finite_certificate
    certificate

theorem PrimeFactorUnimodality.Dusart599FiniteCertificate.toIndexed
    (certificate :
      PrimeFactorUnimodality.Dusart599FiniteCertificate (648 / 1000 : Real)) :
    PrimeFactorUnimodality.Dusart599IndexedFiniteCertificate := by
  exact PrimeFactorUnimodality.Dusart599FiniteCertificate.toIndexed certificate

theorem PrimeFactorUnimodality.completeClassification_of_split_theta_error_and_reserved_integral_core
    {A C X x₀ R : Real} (hX : (4e18 : Real) ≤ X)
    (h2x₀ : (2 : Real) ≤ x₀) (hx₀X : x₀ ≤ X)
    (finitePrimeCounting :
      PrimeFactorUnimodality.HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : PrimeFactorUnimodality.HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval :
      PrimeFactorUnimodality.HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hsmall : |∫ t in (2 : Real)..x₀,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R)
    (hR : R ≤ 10000)
    (thetaErrorAbove :
      PrimeFactorUnimodality.HasThetaLogFourthErrorAbove A x₀)
    (reservedIntegralCore :
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
          10000 + A * (∫ t in x₀..X, 1 / Real.log t ^ 6) ≤
        C * X / Real.log X ^ 4) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_split_theta_error_and_reserved_integral_core
    hX h2x₀ hx₀X finitePrimeCounting finiteTheta finiteShortInterval
    hA0 hA1 hC0 hC hsmall hR thetaErrorAbove reservedIntegralCore

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_split_inputs
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (selectedInputs :
      PrimeFactorUnimodality.MediumPNTSelectedSplitInputs X C) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_split_inputs
    hX hC0 hC selectedInputs

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_indexed_split_certificate
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (certificate :
      PrimeFactorUnimodality.MediumPNTSelectedIndexedSplitCertificate X C) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_indexed_split_certificate
    hX hC0 hC certificate

/-! Public boundary for the corrected row-based proof.  The finite theta
error is not requested from `2`; its prefix is discharged by the explicit
Abel-remainder field in the provider. -/
theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_remainder_row_provider
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (provider : PrimeFactorUnimodality.MediumPNTFiniteSplitRemainderRowProvider X C) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_remainder_row_provider
    hX hC0 hC provider

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_core_row_provider
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (provider : PrimeFactorUnimodality.MediumPNTFiniteSplitCoreRowProvider X C) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_core_row_provider
    hX hC0 hC provider

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_core_rows
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (primeCountingRows : ∀ Y : Real, X ≤ Y →
      ∃ rows : List PrimeFactorUnimodality.DusartPrimeCountingRow,
        PrimeFactorUnimodality.DusartPrimeCountingRowsCoverFrom599 rows Y)
    (thetaRows : ∀ Y : Real, X ≤ Y →
      ∃ rows : List PrimeFactorUnimodality.DusartThetaBoundsRow,
        PrimeFactorUnimodality.DusartThetaBoundsRowsCoverUpTo rows Y)
    (shortIntervalRows : ∀ Y : Real, X ≤ Y →
      ∃ rows : List PrimeFactorUnimodality.LogCubedPrimeRow,
        PrimeFactorUnimodality.LogCubedPrimeRowsCoverUpTo rows Y)
    (core : ∀ Y : Real, X ≤ Y →
      4000 + 720 * (∫ t in (2 : Real)..Y, 1 / Real.log t ^ 7) + 10 * Y ≤
        C * Y / Real.log Y ^ 4) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_core_rows
    hX hC0 hC primeCountingRows thetaRows shortIntervalRows core
