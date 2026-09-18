import PrimeFactorUnimodality.Proof.LargeRange.ClosedAnalyticReduction
import PrimeFactorUnimodality.Proof.LargeRange.RecordNumericBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordReciprocalCertificate
import PrimeFactorUnimodality.Proof.LargeRange.RecordSideConditions

set_option autoImplicit false

/-! # The finite record-input range -/

namespace PrimeFactorUnimodality

noncomputable section

theorem recordRange_not_isUnimodal
    (twin : ConsecutivePrimes recordLower recordUpper)
    (k : Nat) (hkLower : 49 ≤ k) (hkUpper : k ≤ 38000) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  by_cases hkCoarse : k ≤ 10372
  · apply recordInputs_not_isUnimodal_of_closed_mertens k (by omega) twin
      (record_descentDefined hkLower hkUpper)
      (record_ascentDefined hkLower hkUpper)
      (record_prefix_le_half hkUpper)
      (record_coarse_descentNumeric hkLower hkCoarse)
      (record_coarse_ascentNumeric hkLower)
  · by_cases hkMid : k ≤ 33314
    · apply recordInputs_not_isUnimodal_of_closed_mertens k (by omega) twin
        (record_descentDefined hkLower hkUpper)
        (record_ascentDefined hkLower hkUpper)
        (record_prefix_le_half hkUpper)
        (record_coarse_descentNumeric_mid (by omega) hkMid)
        (record_coarse_ascentNumeric hkLower)
    · apply recordInputs_not_isUnimodal_of_finite_prefix k (by omega)
        ((71 : Real) / 25) twin
        (record_descentDefined hkLower hkUpper)
        (record_ascentDefined hkLower hkUpper)
        (record_prefix_le_half hkUpper)
      · exact (reciprocalPrimeSumBelow_mono
          (record_prefix_primeAt_le_500000 (k := k) (by omega) |>.trans
            (by norm_num))).trans reciprocalPrimeSumBelow_500001_lt.le
      · exact record_finite_prefix_descentNumeric hkUpper
      · exact record_coarse_ascentNumeric hkLower

end

end PrimeFactorUnimodality
