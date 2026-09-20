import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.DusartProof

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-!
# Closed explicit theta estimates

Implementation owner: Luna.

This module must prove and export
`PrimeFactorUnimodality.wangCrapis_thetaBounds : HasDusartThetaBounds`
from the repository's proved zero-free-region, Chebyshev, logarithm-envelope,
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

theorem wangCrapis_theta_upper_e28_from_paper_inputs
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi_error : |Chebyshev.psi x - x| ≤
      (2841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  exact dusart_theta_upper_e28_from_absolute_psi_error
    hx hx_exp hpsi_error hgap

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

/-! Selected-cutoff form used by the split all-`k` assembly. -/
theorem wangCrapis_thetaBounds_of_selected_cutoff
    {A X : Real} (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A X) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_logFourthTail
    hXpos hlogX finite hA_nonneg hA
  intro x hx
  exact thetaError x hx

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

/-! The same assembly specialized to the project's medium-PNT
adapter.  The only remaining input is the bounded endpoint verification;
the unbounded analytic tail is supplied by the proved source-level PNT
argument, not by a Dusart theorem imported as an assumption. -/
theorem wangCrapis_thetaBounds_of_mediumPNT
    (finite : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartSymmetricThetaBoundsBelow Y) :
    HasDusartThetaBounds := by
  obtain ⟨Y, hY, h4Y, hlogY, thetaError⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_at_large_cutoff
  have hYpos : 0 < Y := by linarith
  have hA : (648 / 1000 : Real) / Real.log Y ≤
      12167 / 500000 := by
    have hlogYpos : 0 < Real.log Y := by linarith
    apply (div_le_iff₀ hlogYpos).2
    nlinarith
  exact wangCrapis_thetaBounds_of_logFourthTail
    hYpos (by linarith) (finite Y h4Y) (by norm_num) hA thetaError

/-! The source-level decay route can also provide the theta provider directly.
The finite endpoint argument is the only bounded input: the arbitrary
coefficient delivered by the PNT is absorbed by raising the selected cutoff
to an explicit exponential threshold. -/
theorem wangCrapis_thetaBounds_of_mediumPNT_via_decay
    (finite : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartSymmetricThetaBoundsBelow Y) :
    HasDusartThetaBounds := by
  obtain ⟨C, Y₀, hC, h4Y₀, thetaError₀⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_via_decay
  let L : Real := max 100 (((C + 1) * 500000 / 12167) + 1)
  let Y : Real := max Y₀ (Real.exp L)
  have hY₀ : Y₀ ≤ Y := le_max_left _ _
  have hexpY : Real.exp L ≤ Y := le_max_right _ _
  have hYpos : 0 < Y := by
    exact (Real.exp_pos L).trans_le hexpY
  have h4Y : (4e18 : Real) ≤ Y := h4Y₀.trans hY₀
  have hlogY : (10 : Real) < Real.log Y := by
    have hL100 : (100 : Real) ≤ L := le_max_left _ _
    have hlog : L ≤ Real.log Y :=
      (Real.le_log_iff_exp_le hYpos).2 hexpY
    linarith
  have thetaError : HasThetaLogFourthError (C + 1) Y := by
    intro x hx
    exact thetaError₀ x (hY₀.trans hx)
  have hA0 : 0 ≤ C + 1 := by linarith
  have hA : (C + 1) / Real.log Y ≤ 12167 / 500000 := by
    have hlogYpos : 0 < Real.log Y := by linarith
    apply (div_le_iff₀ hlogYpos).2
    have hLcoef : ((C + 1) * 500000 / 12167) + 1 ≤ L :=
      le_max_right _ _
    have hLlog : L ≤ Real.log Y :=
      (Real.le_log_iff_exp_le hYpos).2 hexpY
    nlinarith
  exact wangCrapis_thetaBounds_of_logFourthTail
    hYpos hlogY (finite Y h4Y) hA0 hA thetaError

end

end PrimeFactorUnimodality
