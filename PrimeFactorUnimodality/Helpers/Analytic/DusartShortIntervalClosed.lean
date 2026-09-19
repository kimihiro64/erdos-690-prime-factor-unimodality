import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-!
# Closed explicit short-interval estimate

Implementation owner: Luna.

This module must prove and export
`PrimeFactorUnimodality.wangCrapis_shortInterval : HasDusartShortIntervalPrime`.
Use the compact, kernel-checked prefix through `89693` and the closed explicit
theta estimate above that point.  Any additional bounded data must use indexed
rows and reusable assemblers, never one generated theorem file per witness.

The exact proof obligations and dependency order are recorded in
`LEAN_COMPLETION_HANDOFF.md`.  The finite prefix below is closed now; the
remaining global provider still needs the independently proved tail estimate.
-/

/-! This is the reusable finite prefix, not the global provider.  Its proof
comes from the compact row assembler in `FinitePrimeIntervalRows`, so it does
not introduce an assumption or a hidden theorem. -/
theorem wangCrapis_shortIntervalPrefix :
    HasDusartShortIntervalPrimeBelow (89693 : Real) := by
  exact hasDusartShortIntervalPrimeBelow_3275_89693

/-! Once the log-cubed tail is proved directly, this is the exact final
short-interval assembly.  Keeping the tail as an explicit argument makes the
remaining analytic obligation visible rather than smuggling it in through a
Dusart theorem with hidden axioms. -/
theorem wangCrapis_shortInterval_of_logCubedTail
    (tail : HasLogCubedShortIntervalPrime) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_below_and_logCubed
    wangCrapis_shortIntervalPrefix tail

end

end PrimeFactorUnimodality
