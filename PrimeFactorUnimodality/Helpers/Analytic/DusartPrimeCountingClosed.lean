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
  constructor
  · intro x hx hX
    exact (dusartPrimeCounting_599_1000 x hx hX).1
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact dusartSmallUpperIntervalRows_provide x hx hsmall
    · exact (dusartPrimeCounting_599_1000 x (le_of_not_gt hsmall) hX).2


end

end PrimeFactorUnimodality
