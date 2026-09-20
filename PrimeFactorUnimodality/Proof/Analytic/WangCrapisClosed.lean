import PrimeFactorUnimodality.Helpers.Analytic.DusartPrimeCountingClosed
import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosed
import PrimeFactorUnimodality.Helpers.Analytic.DusartShortIntervalClosed
import PrimeFactorUnimodality.Proof.CompleteClassification

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! The finite endpoint obligations are kept together so the computational
layer has one stable interface to the analytic assembly. -/
structure WangCrapisFiniteProviders where
  thetaBounds : ∀ Y : Real, (4e18 : Real) ≤ Y →
    HasDusartSymmetricThetaBoundsBelow Y
  thetaError : ∀ Y : Real, (4e18 : Real) ≤ Y →
    HasThetaLogFourthErrorBelow (648 / 1000 : Real) Y
  primeCounting : ∀ Y : Real, (4e18 : Real) ≤ Y →
    HasDusartRealPrimeCountingBoundsBelow Y
  logCubed : ∀ Y : Real, (89693 : Real) ≤ Y →
    HasLogCubedShortIntervalPrimeBelow Y

/-! A certificate package is needed only at the cutoff selected by the
source-level MediumPNT argument.  Quantifying the finite fields over every
possible cutoff would impose a stronger obligation than the analytic proof
uses and would obscure the actual all-`k` boundary. -/
structure WangCrapisSelectedFiniteProviders where
  cutoff : Real
  lower : (4e18 : Real) ≤ cutoff
  thetaErrorBelow :
    HasThetaLogFourthErrorBelow (648 / 1000 : Real) (4e18 : Real)
  thetaError : HasThetaLogFourthError (648 / 1000 : Real) cutoff
  primeCounting : HasDusartRealPrimeCountingBoundsBelow cutoff
  theta : HasDusartSymmetricThetaBoundsBelow cutoff
  shortInterval : HasLogCubedShortIntervalPrimeBelow cutoff

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

/-! The paper-facing package can now be assembled directly from the three
finite endpoint providers.  The medium-PNT tail is proved in the analytic
helpers; only the bounded rows remain to be supplied by the certificate
layer. -/
theorem wangCrapisPaperInputs_of_mediumPNT_finite_providers
    (finiteThetaBounds : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartSymmetricThetaBoundsBelow Y)
    (finiteThetaError : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasThetaLogFourthErrorBelow (648 / 1000 : Real) Y)
    (finitePrimeCounting : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartRealPrimeCountingBoundsBelow Y)
    (finiteLogCubed : ∀ Y : Real, (89693 : Real) ≤ Y →
      HasLogCubedShortIntervalPrimeBelow Y) :
    WangCrapisPaperInputs := by
  exact wangCrapisPaperInputs_of_providers
    (wangCrapis_primeCounting_of_mediumPNT
      finiteThetaError finitePrimeCounting)
    (wangCrapis_thetaBounds_of_mediumPNT_via_decay finiteThetaBounds)
    (wangCrapis_shortInterval_of_mediumPNT finiteLogCubed)

theorem completeClassification_closed_of_mediumPNT_finite_providers
    (finiteThetaBounds : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartSymmetricThetaBoundsBelow Y)
    (finiteThetaError : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasThetaLogFourthErrorBelow (648 / 1000 : Real) Y)
    (finitePrimeCounting : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartRealPrimeCountingBoundsBelow Y)
    (finiteLogCubed : ∀ Y : Real, (89693 : Real) ≤ Y →
      HasLogCubedShortIntervalPrimeBelow Y) :
    CompleteClassification := by
  exact completeClassification_of_wangCrapis_paper_inputs
    (wangCrapisPaperInputs_of_mediumPNT_finite_providers
      finiteThetaBounds finiteThetaError finitePrimeCounting finiteLogCubed)

theorem completeClassification_closed_of_finite_providers
    (providers : WangCrapisFiniteProviders) :
    CompleteClassification := by
  exact completeClassification_closed_of_mediumPNT_finite_providers
    providers.thetaBounds providers.thetaError providers.primeCounting
    providers.logCubed

theorem completeClassification_closed_of_selected_finite_providers
    (providers : WangCrapisSelectedFiniteProviders) :
    CompleteClassification := by
  have finiteThetaError :
      HasThetaLogFourthErrorBelow (648 / 1000 : Real) (4e18 : Real) :=
    providers.thetaErrorBelow
  exact completeClassification_of_mediumPNT_and_selected_finite_theta_error
    (X := (4e18 : Real)) (A := (648 / 1000 : Real))
    le_rfl (by norm_num) (by norm_num) finiteThetaError
    { cutoff := providers.cutoff
      lower := providers.lower
      large := providers.lower
      thetaError := providers.thetaError
      primeCounting := providers.primeCounting
      theta := providers.theta
      shortInterval := providers.shortInterval }

theorem wangCrapisPaperInputs_of_finite_providers
    (providers : WangCrapisFiniteProviders) :
    WangCrapisPaperInputs := by
  exact wangCrapisPaperInputs_of_mediumPNT_finite_providers
    providers.thetaBounds providers.thetaError providers.primeCounting
    providers.logCubed

end

end PrimeFactorUnimodality
