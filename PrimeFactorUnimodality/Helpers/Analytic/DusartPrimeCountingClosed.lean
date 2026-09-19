import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT
import PrimeFactorUnimodality.Helpers.FiniteCertificates.SmallPrimeCountingIntervals

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-!
# Closed explicit prime-counting estimates

Implementation owner: Luna.

This module must prove and export
`PrimeFactorUnimodality.wangCrapis_primeCounting : HasDusartPrimeCountingBounds`
by applying the repository's proved Abel conversion to the closed theta error
and discharging the compact finite low-endpoint range.  It must not import or
assume a prepackaged Dusart theorem.

The exact proof obligations and dependency order are recorded in
`LEAN_COMPLETION_HANDOFF.md`.  The closed finite prefix below is an input to
the eventual global provider; it does not claim to discharge the analytic
tail.
-/

/-! Closed finite prime-counting prefix assembled from endpoint rows and the
compact small-range upper-bound rows. -/
theorem wangCrapis_primeCountingPrefix :
    HasDusartRealPrimeCountingBoundsBelow (1000 : Real) := by
  exact hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
    dusartPrimeCountingEndpointRow_1000_cover
    dusartSmallUpperIntervalRows_provide

/-! Direct Abel assembly for the prime-counting provider.  The finite
prime-counting rows are kept separate from the theta remainder: the latter
supplies the finite core at `X`, while the source-level asymptotic conversion
supplies the unbounded tail above the same cutoff. -/
theorem wangCrapis_primeCounting_of_finite_and_thetaTail
    {A X Y : Real}
    (finite : HasDusartRealPrimeCountingBoundsBelow Y)
    (h4X : (4e18 : Real) ≤ X)
    (hXpos : 0 < X) (h2X : 2 ≤ X) (hXY : X ≤ Y)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hlog : (42 : Real) ≤ Real.log X)
    (thetaBelow : HasThetaLogFourthErrorBelow A X)
    (thetaAbove : HasThetaLogFourthErrorAbove A X) :
    HasDusartPrimeCountingBounds := by
  have thetaError : HasThetaLogFourthError A X := by
    intro x hx
    exact thetaAbove x hx
  have hcore : |primeCountingCore X| ≤
    (3 / 5 : Real) * X / Real.log X ^ 4 :=
    primeCountingCore_abs_le_at_large_cutoff_of_theta_error
      h4X hA0 hA thetaBelow
  exact hasDusartPrimeCountingBounds_of_finite_and_core_and_theta_error
    finite hXpos h2X hXY hA0 hA (by norm_num) (by norm_num) hlog hcore
    thetaError

/-! Complete source-level assembly.  The medium-PNT theorem chooses one
eventual cutoff after the finite theta-error provider has established the
Abel core; the finite prime-counting provider is then consumed at exactly
that cutoff. -/
theorem wangCrapis_primeCounting_of_mediumPNT
    (finiteTheta : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasThetaLogFourthErrorBelow (648 / 1000 : Real) Y)
    (finitePrimeCounting : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartRealPrimeCountingBoundsBelow Y) :
    HasDusartPrimeCountingBounds := by
  obtain ⟨Y, hXY, htail, _, _⟩ :=
    exists_mediumPNT_all_real_dusart_tail_inputs_of_finite_theta_error
      (A := (648 / 1000 : Real)) (X := (4e18 : Real))
      le_rfl (by norm_num) (by norm_num) finiteTheta
  exact hasDusartPrimeCountingBounds_of_real
    (hasDusartRealPrimeCountingBounds_of_below_and_above
      (finitePrimeCounting Y hXY) htail)

end

end PrimeFactorUnimodality
