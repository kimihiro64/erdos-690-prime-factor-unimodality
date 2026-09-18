import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive
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
theorem recordTwin_consecutive : ConsecutivePrimes recordLower recordUpper := by
  have lower_gt_two : 2 < recordLower := by
    by_contra not_gt
    have lower_eq : recordLower = 2 := by omega
    have upper_eq : recordUpper = 4 := by omega
    have upper_prime := recordTwin_isTwinPrime.2
    rw [upper_eq] at upper_prime
    norm_num at upper_prime
  rw [recordUpper_eq_lower_add_two]
  exact consecutivePrimes_of_add_two recordTwin_isTwinPrime.1
    (by simpa [recordUpper_eq_lower_add_two] using recordTwin_isTwinPrime.2)
    lower_gt_two

end PrimeFactorUnimodality
