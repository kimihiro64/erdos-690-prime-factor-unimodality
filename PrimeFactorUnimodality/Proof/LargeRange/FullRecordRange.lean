import PrimeFactorUnimodality.Proof.LargeRange.FullRecordAnalyticReduction
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordGapConsequence
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordNumericBounds

set_option autoImplicit false

/-! # Finite classification from the full published record inputs -/

namespace PrimeFactorUnimodality

noncomputable section

theorem fullRecordRange_not_isUnimodal
    (subBlock : ∀ d, d ≤ 455703 → ¬(recordGapCenter - d).Prime)
    (addBlock : ∀ d, d ≤ 657401 → ¬(recordGapCenter + d).Prime)
    (twin : ConsecutivePrimes recordLower recordUpper)
    (k : Nat) (hkLower : 38001 ≤ k) (hkUpper : k ≤ 7300000) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  apply fullRecordInputs_not_isUnimodal_of_closed_mertens k (by omega)
    (fullRecordGap_primeGap_ge_of_blocks subBlock addBlock)
    (fullRecordGap_predecessor_gt_half_of_subBlock subBlock)
    twin
    (fullRecord_descentDefined hkLower (hkUpper.trans (by norm_num)))
    (fullRecord_ascentDefined hkLower (hkUpper.trans (by norm_num)))
    (fullRecord_prefix_le_half (hkUpper.trans (by norm_num)))
    (fullRecord_descentNumeric hkLower hkUpper)
    (record_coarse_ascentNumeric (by omega))

end

end PrimeFactorUnimodality
