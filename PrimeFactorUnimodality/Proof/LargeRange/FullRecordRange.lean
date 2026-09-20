import PrimeFactorUnimodality.Proof.LargeRange.FullRecordAnalyticReduction
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordGapConsequence
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordNumericBounds
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCompact
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinClosed
import PrimeFactorUnimodality.Proof.LargeRange.UniformTailClosedMertens

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

theorem fullRecordRange_not_isUnimodal_closed
    (k : Nat) (hkLower : 38001 ≤ k) (hkUpper : k ≤ 7300000) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  apply fullRecordRange_not_isUnimodal (subBlock := ?_) (addBlock := ?_)
    (twin := recordTwin_consecutive) k hkLower hkUpper
  · intro d hd
    by_cases hzero : d = 0
    · subst d
      exact recordGap_sub_not_prime_of_tail_owner (q := 13) (by norm_num)
        (by norm_num) (by norm_num) (by decide) (by norm_num)
    · exact fullRecordGapSubBlock d (by omega) hd
  · intro d hd
    by_cases hzero : d = 0
    · subst d
      exact recordGap_add_not_prime_of_tail_owner (q := 13) (by norm_num)
        (by norm_num) (by norm_num) (by decide) (by norm_num)
    · exact fullRecordGapAddBlock d (by omega) hd

/-! The published finite cutoff extends beyond the range covered by the
full-record descent inequality.  The closed Mertens tail is already valid
from `7,300,001`, so it supplies the overlap needed for the remaining
published finite slice without introducing a new certificate boundary. -/
theorem fullRecordRange_not_isUnimodal_closed_through8600001
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair)
    (k : Nat) (hkLower : 38001 ≤ k) (hkUpper : k ≤ 8600001) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  by_cases hkFullRecord : k ≤ 7300000
  · exact fullRecordRange_not_isUnimodal_closed k hkLower hkFullRecord
  · exact uniformTail_not_isUnimodal_closed_mertens
      primeCountingBounds thetaBounds tailPair (k := k) (by omega)

end

end PrimeFactorUnimodality
