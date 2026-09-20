import PrimeFactorUnimodality.Helpers.Analytic.DusartPrimeCountingClosed
import PrimeFactorUnimodality.Helpers.Analytic.DusartShortIntervalClosed
import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosed
import PrimeFactorUnimodality.Proof.CompleteClassification

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! The finite endpoint obligations are kept together so the computational
layer has one stable interface to the analytic assembly. -/
/-! A certificate package is needed only at the cutoff selected by the
source-level MediumPNT argument.  Quantifying the finite fields over every
possible cutoff would impose a stronger obligation than the analytic proof
uses and would obscure the actual all-`k` boundary. -/
abbrev WangCrapisFiniteProviders : Prop :=
  MediumPNTFiniteIntegerIntervalBundledListPrefixProvider

abbrev WangCrapisSelectedFiniteProviders : Prop :=
  MediumPNTSelectedSplitInputs (4e18 : Real) (3 / 5 : Real)

theorem wangCrapis_thetaBounds_of_finite_providers
    (providers : WangCrapisSelectedFiniteProviders) :
    HasDusartThetaBounds := by
  have hXpos : 0 < providers.cutoff := by linarith [providers.lower]
  have hlogX : (42 : Real) ≤ Real.log providers.cutoff := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) providers.lower)
  have hA : (648 / 1000 : Real) / Real.log providers.cutoff ≤
      (12167 / 500000 : Real) := by
    have hlog_pos : 0 < Real.log providers.cutoff := by linarith
    apply (div_le_iff₀ hlog_pos).2
    nlinarith
  exact wangCrapis_thetaBounds_of_selected_cutoff providers.theta
    hXpos (by linarith) (by norm_num) hA providers.thetaError

theorem wangCrapis_shortInterval_of_finite_providers
    (providers : WangCrapisSelectedFiniteProviders) :
    HasDusartShortIntervalPrime := by
  have hXpos : 0 < providers.cutoff := by linarith [providers.lower]
  have hlogX : (10 : Real) < Real.log providers.cutoff := by
    have hlog := forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) providers.lower)
    linarith
  have hA : (648 / 1000 : Real) / Real.log providers.cutoff ≤
      (12167 / 500000 : Real) := by
    have hlog_pos : 0 < Real.log providers.cutoff := by linarith
    apply (div_le_iff₀ hlog_pos).2
    nlinarith
  exact wangCrapis_shortInterval_of_selected_cutoff
    (by linarith [providers.lower]) providers.shortInterval
    hXpos (by linarith) hlogX (by norm_num) hA providers.thetaError

theorem wangCrapis_primeCounting_of_finite_providers
    (providers : WangCrapisSelectedFiniteProviders) :
    HasDusartPrimeCountingBounds := by
  obtain ⟨R, hR, hcoreR⟩ := providers.remainder
  have hcore0 : |primeCountingCore providers.cutoff| ≤
      4000 + 720 * (∫ t in (2 : Real)..providers.cutoff,
        1 / Real.log t ^ 7) + R :=
    primeCountingCore_abs_le_of_integral_remainder
      (by linarith [providers.lower]) hR
  have hcore : |primeCountingCore providers.cutoff| ≤
      (3 / 5 : Real) * providers.cutoff / Real.log providers.cutoff ^ 4 :=
    hcore0.trans hcoreR
  have hXpos : 0 < providers.cutoff := by linarith [providers.lower]
  have hlogX : (42 : Real) ≤ Real.log providers.cutoff := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) providers.lower)
  exact wangCrapis_primeCounting_of_selected_cutoff providers.primeCounting
    providers.lower hXpos (by linarith) (by norm_num) (by norm_num)
    (by norm_num) le_rfl hlogX hcore providers.thetaError

theorem wangCrapisPaperInputs_of_finite_providers
    (providers : WangCrapisSelectedFiniteProviders) :
    WangCrapisPaperInputs := by
  exact wangCrapisPaperInputs_of_providers
    (wangCrapis_primeCounting_of_finite_providers providers)
    (wangCrapis_thetaBounds_of_finite_providers providers)
    (wangCrapis_shortInterval_of_finite_providers providers)

theorem wangCrapisSelectedFiniteProviders_of_indexed_split_certificate
    (certificate :
      MediumPNTSelectedIndexedSplitCertificate
        (4e18 : Real) (3 / 5 : Real)) :
    WangCrapisSelectedFiniteProviders := by
  obtain ⟨nPrime, primeRows, primeCover⟩ := certificate.primeCountingRows
  obtain ⟨nTheta, thetaRows, thetaCover⟩ := certificate.thetaRows
  obtain ⟨nLog, logRows, logCover⟩ := certificate.logRows
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow certificate.cutoff :=
    hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
      primeCover dusartSmallUpperIntervalRows_provide
  have finiteTheta :
      HasDusartSymmetricThetaBoundsBelow certificate.cutoff :=
    hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows thetaCover
  have finiteShortInterval :
      HasLogCubedShortIntervalPrimeBelow certificate.cutoff :=
    hasLogCubedShortIntervalPrimeBelow_of_indexed_rows logCover
  exact {
    cutoff := certificate.cutoff
    lower := certificate.lower
    large := certificate.large
    thetaError := certificate.thetaError
    primeCounting := finitePrimeCounting
    theta := finiteTheta
    shortInterval := finiteShortInterval
    remainder := certificate.remainder }

/-!
# Closed Wang--Crapis analytic package

Implementation owner: Luna.

After the three analytic provider modules elaborate, this module must define
`PrimeFactorUnimodality.wangCrapisPaperInputs : WangCrapisPaperInputs` and prove
`PrimeFactorUnimodality.completeClassification_closed : CompleteClassification`.
The latter is the sole theorem that `Challenge.lean` and `Solution.lean` should
use for their public all-`k` declarations.

The exact proof obligations and final readiness gate are recorded in
`LEAN_COMPLETION_HANDOFF.md`.  This file intentionally contains no provisional
declaration: a `sorry`, axiom, or bodyless constant would hide the live gap.
-/

/-! The public package boundary is fully structural: callers must provide the
three explicit analytic facts, and the classification theorem consumes only
that package.  Keeping this constructor here makes the final missing finite
provider visible to CI and to future certificate modules. -/
theorem wangCrapisPaperInputs_of_providers
    (primeCounting : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    WangCrapisPaperInputs := by
  exact { primeCounting := primeCounting
          thetaBounds := thetaBounds
          shortInterval := shortInterval }

theorem completeClassification_closed_of_providers
    (primeCounting : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    CompleteClassification := by
  exact completeClassification_of_wangCrapis_paper_inputs
    (wangCrapisPaperInputs_of_providers primeCounting thetaBounds shortInterval)

theorem completeClassification_closed_of_finite_providers
    (providers : WangCrapisFiniteProviders) :
    CompleteClassification := by
  exact completeClassification_of_mediumPNT_and_integer_interval_bundled_list_prefix_provider
    providers

theorem completeClassification_closed_of_selected_finite_providers
    (providers : WangCrapisSelectedFiniteProviders) :
    CompleteClassification := by
  exact completeClassification_of_wangCrapis_paper_inputs
    (wangCrapisPaperInputs_of_finite_providers providers)

/-! Direct all-`k` consumer for the selected split package.  This keeps the
finite Abel remainder and the common analytic cutoff visible at the final
classification boundary. -/
theorem completeClassification_closed_of_selected_split_inputs
    (providers : WangCrapisSelectedFiniteProviders) :
    CompleteClassification := by
  exact completeClassification_of_mediumPNT_and_selected_split_inputs
    (by norm_num) (by norm_num) (by norm_num) providers

/-! Stable consumer for the compact indexed certificate boundary. -/
theorem completeClassification_closed_of_indexed_split_certificate
    (certificate :
      MediumPNTSelectedIndexedSplitCertificate
        (4e18 : Real) (3 / 5 : Real)) :
    CompleteClassification := by
  exact completeClassification_closed_of_selected_finite_providers
    (wangCrapisSelectedFiniteProviders_of_indexed_split_certificate certificate)

end

end PrimeFactorUnimodality
