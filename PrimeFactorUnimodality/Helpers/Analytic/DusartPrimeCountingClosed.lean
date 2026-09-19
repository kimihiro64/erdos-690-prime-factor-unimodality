import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
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

end

end PrimeFactorUnimodality
