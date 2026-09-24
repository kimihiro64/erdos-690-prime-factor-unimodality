import PrimeFactorUnimodality.Proof.LargeRange.ClosedAnalyticReduction
import PrimeFactorUnimodality.Proof.LargeRange.RecordNumericBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordPrimeCountingReduction
import PrimeFactorUnimodality.Proof.LargeRange.RecordSideConditions

set_option autoImplicit false

/-! # The finite record-input range -/

namespace PrimeFactorUnimodality

noncomputable section

theorem recordRange_not_isUnimodal
    (bounds : HasDusartPrimeCountingBounds)
    (twin : ConsecutivePrimes recordLower recordUpper)
    (k : Nat) (hkLower : 49 ≤ k) (hkUpper : k ≤ 38000) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  by_cases hkCoarse : k ≤ 10372
  · apply recordInputs_not_isUnimodal_of_closed_mertens k (by omega) twin
      (record_descentDefined bounds hkLower hkUpper)
      (record_ascentDefined bounds hkLower hkUpper)
      (record_prefix_le_half bounds hkUpper)
      (record_coarse_descentNumeric bounds hkLower hkCoarse)
      (record_coarse_ascentNumeric hkLower)
  · exact recordInputs_not_isUnimodal_of_primeCounting bounds k (by omega) hkUpper
      recordGap_primeGap_ge recordGap_predecessor_gt_half twin

end

end PrimeFactorUnimodality
