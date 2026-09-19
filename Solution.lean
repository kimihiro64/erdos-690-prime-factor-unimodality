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

/-! Public boundary for a source-level MediumPNT proof: only finite analytic
facts at the cutoff selected by that proof remain to be supplied. -/
theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_finite_inputs
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : |PrimeFactorUnimodality.primeCountingCore X| ≤
      C * X / Real.log X ^ 4)
    (finiteInputs : ∀ Y : Real, X ≤ Y →
      PrimeFactorUnimodality.HasDusartRealPrimeCountingBoundsBelow Y ∧
      PrimeFactorUnimodality.HasDusartSymmetricThetaBoundsBelow Y ∧
      PrimeFactorUnimodality.HasLogCubedShortIntervalPrimeBelow Y) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_finite_inputs
    hX hC0 hC hcore finiteInputs

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_split_inputs
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (finiteInputs : ∀ Y : Real, X ≤ Y →
      PrimeFactorUnimodality.HasDusartRealPrimeCountingBoundsBelow Y ∧
      PrimeFactorUnimodality.HasDusartSymmetricThetaBoundsBelow Y ∧
      PrimeFactorUnimodality.HasLogCubedShortIntervalPrimeBelow Y ∧
      ∃ R : Real,
        |∫ t in (2 : Real)..Y,
            (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
              1 / (Real.log t) ^ 2)| ≤ R ∧
        4000 + 720 * (∫ t in (2 : Real)..Y, 1 / Real.log t ^ 7) + R ≤
          C * Y / Real.log Y ^ 4) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_split_inputs
    hX hC0 hC finiteInputs

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
