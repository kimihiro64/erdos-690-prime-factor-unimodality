import PrimeFactorUnimodality

set_option autoImplicit false

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

theorem PrimeFactorUnimodality.fourthDensityStrictValley :
    PrimeFactorUnimodality.prescribedFactorDensity
          PrimeFactorUnimodality.primesBefore17 4 17 <
        PrimeFactorUnimodality.prescribedFactorDensity
          PrimeFactorUnimodality.primesBefore13 4 13 ∧
      PrimeFactorUnimodality.prescribedFactorDensity
          PrimeFactorUnimodality.primesBefore17 4 17 <
        PrimeFactorUnimodality.prescribedFactorDensity
          PrimeFactorUnimodality.primesBefore19 4 19 :=
  PrimeFactorUnimodality.assembledFourthDensityStrictValley
