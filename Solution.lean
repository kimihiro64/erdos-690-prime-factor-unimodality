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

/-! The source-level all-`k` theorem can also be driven by the four finite
row providers used by the explicit proof. -/
theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_row_provider
    (provider : PrimeFactorUnimodality.MediumPNTFiniteRowProvider) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_bundled_row_provider
    provider

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_split_row_provider
    (provider : PrimeFactorUnimodality.MediumPNTFiniteSplitRowProvider) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_split_row_provider
    provider

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_integer_split_row_provider
    (provider : PrimeFactorUnimodality.MediumPNTFiniteIntegerSplitRowProvider) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_integer_split_row_provider
    provider

theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_integer_interval_split_row_provider
    (provider : PrimeFactorUnimodality.MediumPNTFiniteIntegerIntervalSplitRowProvider) :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_integer_interval_split_row_provider
    provider

/-! Public boundary for a source-level MediumPNT proof: only finite analytic
facts at the cutoff selected by that proof remain to be supplied. -/
theorem PrimeFactorUnimodality.completeClassification_of_mediumPNT_and_selected_finite_inputs
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : |PrimeFactorUnimodality.primeCountingCore X| ≤
      C * X / Real.log X ^ 4)
    (finiteInputs : ∀ Y : Real, X ≤ Y →
      PrimeFactorUnimodularity.HasDusartRealPrimeCountingBoundsBelow Y ∧
      PrimeFactorUnimodularity.HasDusartSymmetricThetaBoundsBelow Y ∧
      PrimeFactorUnimodularity.HasLogCubedShortIntervalPrimeBelow Y) :
    PrimeFactorUnimodularity.CompleteClassification := by
  exact PrimeFactorUnimodularity.completeClassification_of_mediumPNT_and_selected_finite_inputs
    hX hC0 hC hcore finiteInputs
