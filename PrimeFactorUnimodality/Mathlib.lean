import PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerChunk
import PrimeFactorUnimodality.Mathlib.Algebra.Group.PowerStep
import PrimeFactorUnimodality.Mathlib.Data.Nat.CoprimePeriodicCount
import PrimeFactorUnimodality.Mathlib.Data.Nat.Periodic
import PrimeFactorUnimodality.Mathlib.NumberTheory.BLSPrimality
import PrimeFactorUnimodality.Mathlib.NumberTheory.Pocklington
import PrimeFactorUnimodality.Mathlib.NumberTheory.PrimalityCongruence

/-!
# Mathlib candidate facade

This facade imports only reusable modules that are being maintained for eventual
upstreaming to Mathlib. Candidate source belongs under `PrimeFactorUnimodality/Mathlib/`
and must remain independent of every project-specific definition, proof branch,
assembly module, and statement surface.

Candidate modules are recorded in `MATHLIB_PORTING.md`.
-/
