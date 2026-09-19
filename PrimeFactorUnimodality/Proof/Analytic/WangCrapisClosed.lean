import PrimeFactorUnimodality.Helpers.Analytic.DusartPrimeCountingClosed
import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosed
import PrimeFactorUnimodality.Helpers.Analytic.DusartShortIntervalClosed
import PrimeFactorUnimodality.Proof.CompleteClassification

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

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
    (wangCrapis_thetaBounds_of_mediumPNT finiteThetaBounds)
    (wangCrapis_shortInterval_of_mediumPNT finiteLogCubed)

end

end PrimeFactorUnimodality
