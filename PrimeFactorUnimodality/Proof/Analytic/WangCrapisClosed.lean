import PrimeFactorUnimodality.Helpers.Analytic.DusartPrimeCountingClosed
import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosed
import PrimeFactorUnimodality.Helpers.Analytic.DusartShortIntervalClosed
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
structure WangCrapisFiniteProviders where
  cutoff : Real
  lower : (4e18 : Real) ≤ cutoff
  thetaError : HasThetaLogFourthErrorAbove (648 / 1000 : Real) cutoff
  primeCounting : HasDusartRealPrimeCountingBoundsBelow cutoff
  theta : HasDusartSymmetricThetaBoundsBelow cutoff
  shortInterval : HasLogCubedShortIntervalPrimeBelow cutoff
  remainder : ∃ R : Real,
    |∫ t in (2 : Real)..cutoff,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R ∧
      4000 + 720 * (∫ t in (2 : Real)..cutoff, 1 / Real.log t ^ 7) + R ≤
        (3 / 5 : Real) * cutoff / Real.log cutoff ^ 4

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
  exact completeClassification_of_mediumPNT_and_selected_split_inputs
    (X := (4e18 : Real)) (C := (3 / 5 : Real)) le_rfl
    (by norm_num)
    { cutoff := providers.cutoff
      lower := providers.lower
      large := providers.lower
      thetaError := providers.thetaError
      primeCounting := providers.primeCounting
      theta := providers.theta
      shortInterval := providers.shortInterval
      remainder := providers.remainder }

end

end PrimeFactorUnimodality
