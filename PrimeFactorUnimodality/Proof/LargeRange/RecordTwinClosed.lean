import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerResidues
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperResidues
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwin

set_option autoImplicit false

/-!
# Closed record twin-prime certificate

This module assembles the separately replayed binary-power computations into
the mathematical certificate interface and derives primality of both members
of the published pair.
-/

namespace PrimeFactorUnimodality

/-- The closed computation package for the published record twin prime. -/
def recordTwinCertificate : RecordTwinCertificate where
  lowerMain := recordLower_main_kernel
  lowerProper2 := recordLower_proper_2_kernel
  lowerProper3 := recordLower_proper_3_kernel
  lowerProper17 := recordLower_proper_17_kernel
  lowerProper4950817 := recordLower_proper_4950817_kernel
  upperBase := recordUpperWitnessBase
  upperMain := recordUpper_main_kernel
  upperProper2 := recordUpper_proper_2_kernel
  upperProper3 := recordUpper_proper_3_kernel
  upperProper17 := recordUpper_proper_17_kernel
  upperProper4950817 := recordUpper_proper_4950817_kernel

/-- Kernel-checked primality of both members of the 71,298-digit pair. -/
theorem recordTwin_isTwinPrime : recordLower.Prime ∧ recordUpper.Prime :=
  recordTwin_isTwinPrime_of_certificate recordTwinCertificate

/-- The closed pair is consecutive, not merely a pair of primes two apart. -/
theorem recordTwin_consecutive : ConsecutivePrimes recordLower recordUpper :=
  recordTwin_consecutive_of_certificate recordTwinCertificate

end PrimeFactorUnimodality
