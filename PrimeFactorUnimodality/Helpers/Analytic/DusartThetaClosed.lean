import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-!
# Closed explicit theta estimates

Implementation owner: Luna.

This module must prove and export
`PrimeFactorUnimodality.wangCrapis_thetaBounds : HasDusartThetaBounds`
from the repository's sorry-free zero-free-region, Chebyshev, logarithm-envelope,
and compact finite low-endpoint machinery.  It must not import a prepackaged
Dusart theorem or add an assumption-backed provider.

The exact proof obligations and dependency order are recorded in
`LEAN_COMPLETION_HANDOFF.md`.  The finite singleton seed below is closed; it
does not claim to be the global provider.
-/

/-! Closed singleton seed for the finite theta assembler. -/
theorem wangCrapis_thetaPrefix :
    HasDusartSymmetricThetaBoundsBelow (2 : Real) := by
  exact hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
    dusartThetaEndpointRow_two_cover

/-! Exact assembly boundary for the theta provider.  The finite endpoint
proof and the explicit log-fourth tail remain separate inputs until both are
proved from their underlying arguments. -/
theorem wangCrapis_thetaBounds_of_logFourthTail
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact hasDusartThetaBounds_of_finite_and_logFourth_from
    hXpos hlogX finite hA_nonneg hA thetaError

/-! A source-level decay adapter.  This is deliberately stated in terms of
the underlying r-power decay estimate rather than a prepackaged Dusart
theorem.  The decay-to-log-fourth conversion chooses an eventual cutoff;
the caller supplies the finite theta verification up to that same cutoff.
The numerical hypothesis is exactly the margin required by the published
theta assembly. -/
theorem wangCrapis_thetaBounds_of_rpowDecay
    {C c α X : Real}
    (hXpos : 0 < X)
    (hlogX : (500000 : Real) / 12167 < Real.log X)
    (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α)
    (decay : HasThetaLogRpowDecay C c α X)
    (finite : ∀ Y : Real, X ≤ Y →
      HasDusartSymmetricThetaBoundsBelow Y) :
    HasDusartThetaBounds := by
  obtain ⟨Y, hXY, thetaError⟩ :=
    exists_hasThetaLogFourthError_of_logRpowDecay_of_pos_coefficient
      (C := C) (D := (1 : Real)) hC (by norm_num) hc hα decay
  have hYpos : 0 < Y := hXpos.trans hXY
  have hlogY : (10 : Real) < Real.log Y := by
    have hlog_mono : Real.log X ≤ Real.log Y :=
      Real.log_le_log hXpos hXY
    have hmargin : (10 : Real) < (500000 : Real) / 12167 := by
      norm_num
    linarith
  have hA : (1 : Real) / Real.log Y ≤ 12167 / 500000 := by
    have hlogY_pos : 0 < Real.log Y := Real.log_pos (by linarith)
    apply (div_le_iff₀ hlogY_pos).2
    nlinarith
  exact wangCrapis_thetaBounds_of_logFourthTail
    hYpos hlogY (finite Y hXY) (by norm_num) hA thetaError

end

end PrimeFactorUnimodality
