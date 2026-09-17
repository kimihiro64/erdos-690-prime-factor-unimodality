import PrimeFactorUnimodality.Proof.FiniteDensity.FourthWitness

set_option autoImplicit false

/-!
# Fourth-density witness assembly
-/

namespace PrimeFactorUnimodality

/-- Public assembly of the exact `k = 4` strict-valley certificate. -/
theorem assembledFourthDensityStrictValley :
    prescribedFactorDensity primesBefore17 4 17 <
        prescribedFactorDensity primesBefore13 4 13 ∧
      prescribedFactorDensity primesBefore17 4 17 <
        prescribedFactorDensity primesBefore19 4 19 :=
  fourthDensityStrictValleyProof

end PrimeFactorUnimodality
