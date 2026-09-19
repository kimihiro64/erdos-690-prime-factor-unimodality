/-!
# Closed explicit prime-counting estimates

Implementation owner: Luna.

This module must prove and export
`PrimeFactorUnimodality.wangCrapis_primeCounting : HasDusartPrimeCountingBounds`
by applying the repository's proved Abel conversion to the closed theta error
and discharging the compact finite low-endpoint range.  It must not import or
assume a prepackaged Dusart theorem.

The exact proof obligations and dependency order are recorded in
`LEAN_COMPLETION_HANDOFF.md`.  This file intentionally contains no provisional
declaration: a `sorry`, axiom, or bodyless constant would hide the live gap.
-/
