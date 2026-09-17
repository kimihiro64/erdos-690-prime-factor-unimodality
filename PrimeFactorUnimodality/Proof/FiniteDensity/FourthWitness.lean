import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.FiniteDensity

set_option autoImplicit false

/-!
# The first strict valley for the fourth prime-factor density

This module checks Cambie's first non-unimodality certificate using the exact
finite recursion. It does not yet identify `prescribedFactorDensity` with a
natural density; that analytic bridge remains a separate obligation.
-/

namespace PrimeFactorUnimodality

theorem fourthDensityAt13 : prescribedFactorDensity primesBefore13 4 13 = 31 / 5005 := by
  norm_num [prescribedFactorDensity, primesBefore13, finiteDensity]

theorem fourthDensityAt17 : prescribedFactorDensity primesBefore17 4 17 = 206 / 36465 := by
  norm_num [prescribedFactorDensity, primesBefore17, finiteDensity]

theorem fourthDensityAt19 : prescribedFactorDensity primesBefore19 4 19 = 1308 / 230945 := by
  norm_num [prescribedFactorDensity, primesBefore19, finiteDensity]

/-- The finite density formula for `k = 4` has a strict valley at 17. -/
theorem fourthDensityStrictValleyProof :
    prescribedFactorDensity primesBefore17 4 17 <
        prescribedFactorDensity primesBefore13 4 13 ∧
      prescribedFactorDensity primesBefore17 4 17 <
        prescribedFactorDensity primesBefore19 4 19 := by
  rw [fourthDensityAt13, fourthDensityAt17, fourthDensityAt19]
  norm_num

end PrimeFactorUnimodality
