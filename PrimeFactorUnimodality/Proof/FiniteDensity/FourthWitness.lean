import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.DivisibilityPredicate
import PrimeFactorUnimodality.Definitions.FiniteDensity

set_option autoImplicit false

/-!
# The first strict valley for the fourth prime-factor density

This module checks Cambie's first non-unimodality certificate using the exact
finite recursion and records the corresponding natural-density statements.
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

theorem fourthNaturalDensityAt13 :
    HasNaturalDensity (fun n => IsKthDistinctPrimeFactor n 4 13)
      (31 / 5005 : Rat) := by
  have h := hasNaturalDensity_isKthDistinctPrimeFactor_eq_prescribed
    4 (p := 13) (by decide)
  have hp : primesBelow 13 = primesBefore13 := by
    decide
  rw [hp, fourthDensityAt13] at h
  exact h

theorem fourthNaturalDensityAt17 :
    HasNaturalDensity (fun n => IsKthDistinctPrimeFactor n 4 17)
      (206 / 36465 : Rat) := by
  have h := hasNaturalDensity_isKthDistinctPrimeFactor_eq_prescribed
    4 (p := 17) (by decide)
  have hp : primesBelow 17 = primesBefore17 := by
    decide
  rw [hp, fourthDensityAt17] at h
  exact h

theorem fourthNaturalDensityAt19 :
    HasNaturalDensity (fun n => IsKthDistinctPrimeFactor n 4 19)
      (1308 / 230945 : Rat) := by
  have h := hasNaturalDensity_isKthDistinctPrimeFactor_eq_prescribed
    4 (p := 19) (by decide)
  have hp : primesBelow 19 = primesBefore19 := by
    decide
  rw [hp, fourthDensityAt19] at h
  exact h

end PrimeFactorUnimodality
