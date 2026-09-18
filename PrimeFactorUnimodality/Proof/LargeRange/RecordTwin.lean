import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinStructure

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# Replay interface for the record twin-prime certificate

The only fields below are closed modular computations. All mathematical
reasoning from those computations to primality is proved in the kernel by the
general BLS and Pocklington criteria.
-/

namespace PrimeFactorUnimodality

/-- The ten independently computable residues needed for the two primality
certificates. -/
structure RecordTwinCertificate where
  lowerMain :
    (BLSPrimality.alpha recordLower ^ (recordLower + 1)).im = 0
  lowerProper2 :
    IsUnit ((BLSPrimality.alpha recordLower ^ ((recordLower + 1) / 2)).im)
  lowerProper3 :
    IsUnit ((BLSPrimality.alpha recordLower ^ ((recordLower + 1) / 3)).im)
  lowerProper17 :
    IsUnit ((BLSPrimality.alpha recordLower ^ ((recordLower + 1) / 17)).im)
  lowerProper4950817 :
    IsUnit ((BLSPrimality.alpha recordLower ^ ((recordLower + 1) / 4950817)).im)
  upperBase : ℕ
  upperMain :
    (upperBase : ZMod recordUpper) ^ (recordUpper - 1) = 1
  upperProper2 :
    IsUnit ((upperBase : ZMod recordUpper) ^ ((recordUpper - 1) / 2) - 1)
  upperProper3 :
    IsUnit ((upperBase : ZMod recordUpper) ^ ((recordUpper - 1) / 3) - 1)
  upperProper17 :
    IsUnit ((upperBase : ZMod recordUpper) ^ ((recordUpper - 1) / 17) - 1)
  upperProper4950817 :
    IsUnit ((upperBase : ZMod recordUpper) ^
      ((recordUpper - 1) / 4950817) - 1)

theorem recordLower_prime_of_certificate (certificate : RecordTwinCertificate) :
    recordLower.Prime := by
  apply BLSPrimality.prime_of_bls_n_plus_one recordLower recordFactor
    (recordFactor - 1)
  · exact recordLower_gt_one
  · exact recordLower_add_one
  · exact Nat.zero_lt_of_lt recordFactor_gt_one
  · exact recordLower_lt_factor_sq
  · exact recordLower_isUnit_fortyTwo
  · exact certificate.lowerMain
  · intro q hq hqFactor
    rcases prime_dvd_recordFactor q hq hqFactor with rfl | rfl | rfl | rfl
    · exact certificate.lowerProper2
    · exact certificate.lowerProper3
    · exact certificate.lowerProper17
    · exact certificate.lowerProper4950817
  · exact recordFactor_sub_one_not_dvd_lower

theorem recordUpper_prime_of_certificate (certificate : RecordTwinCertificate) :
    recordUpper.Prime := by
  apply Nat.prime_of_pocklington_factor recordUpper recordFactor
    (recordFactor - 1) certificate.upperBase
  · exact recordUpper_gt_one
  · exact recordUpper_sub_one
  · exact Nat.zero_lt_of_lt recordFactor_gt_one
  · exact recordUpper_lt_factor_sq
  · exact certificate.upperMain
  · intro q hq hqFactor
    rcases prime_dvd_recordFactor q hq hqFactor with rfl | rfl | rfl | rfl
    · exact certificate.upperProper2
    · exact certificate.upperProper3
    · exact certificate.upperProper17
    · exact certificate.upperProper4950817
  · exact recordFactor_sub_one_not_dvd_upper

/-- Kernel-checked primality of both endpoints from the closed computation
certificate. -/
theorem recordTwin_isTwinPrime_of_certificate (certificate : RecordTwinCertificate) :
    recordLower.Prime ∧ recordUpper.Prime :=
  ⟨recordLower_prime_of_certificate certificate,
    recordUpper_prime_of_certificate certificate⟩

end PrimeFactorUnimodality
