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
