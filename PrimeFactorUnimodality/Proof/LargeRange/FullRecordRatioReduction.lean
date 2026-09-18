import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Main
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordValley

set_option autoImplicit false

/-! # Prime-weight reduction for the full record inputs -/

namespace PrimeFactorUnimodality

noncomputable section

theorem fullRecordInputs_not_isUnimodal_of_weight_bounds
    (k : Nat) (hk : 2 ≤ k)
    (gapBound :
      1113106 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 455703) - 1))
    (twin : ConsecutivePrimes recordLower recordUpper)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (recordGapCenter - 455703) - 1)
    (ascentDefined : k - 1 ≤ Nat.primeCounting' recordLower)
    (descentNumeric :
      ((k - 1 : Nat) : Rat) < 1113107 *
        (weightSum
            (primesBelow
              (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1))) -
          leadingWeightSum
            (primesBelow
              (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1)))
            (k - 2)))
    (ascentNumeric :
      3 * weightSum (primesBelow recordLower) < ((k - 1 : Nat) : Rat)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  have descentComplement :
      0 < weightSum
          (primesBelow
            (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1))) -
        leadingWeightSum
          (primesBelow
            (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1)))
          (k - 2) := by
    have degreePositive : (0 : Rat) < ((k - 1 : Nat) : Rat) := by
      exact_mod_cast (show 0 < k - 1 by omega)
    have productPositive : (0 : Rat) < 1113107 *
        (weightSum
            (primesBelow
              (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1))) -
          leadingWeightSum
            (primesBelow
              (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1)))
            (k - 2)) := degreePositive.trans descentNumeric
    rcases (mul_pos_iff.mp productPositive) with positive | negative
    · exact positive.2
    · norm_num at negative
  have ascentEntriesNonempty : primesBelow recordLower ≠ [] := by
    intro entriesEmpty
    have lengthZero : (primesBelow recordLower).length = 0 := by simp [entriesEmpty]
    have lengthEq :
        (primesBelow recordLower).length = Nat.primeCounting' recordLower := by
      rw [primesBelow, Finset.length_sort]
      exact Nat.primesBelow_card_eq_primeCounting' recordLower
    omega
  have ascentSumPositive : 0 < weightSum (primesBelow recordLower) :=
    weightSum_pos_of_ne_nil _ (primesBelow_gt_one _) ascentEntriesNonempty
  apply fullRecordInputs_not_isUnimodal k hk gapBound twin
    descentDefined ascentDefined
  · apply densityRatio_lt_of_degree_lt_bound_mul_complement
    · exact primesBelow_gt_one _
    · exact primesBelow_weights_descending _
    · omega
    · simpa [primesBelow_primeAt_length] using descentDefined
    · simpa only [show k - 1 - 1 = k - 2 by omega] using descentComplement
    · simpa only [show k - 1 - 1 = k - 2 by omega] using descentNumeric
  · apply bound_lt_densityRatio_of_bound_mul_weightSum_lt_degree
    · exact primesBelow_gt_one _
    · rw [← primeAt_primeCounting' recordLower twin.left_prime,
        primesBelow_primeAt_length]
      exact ascentDefined
    · exact ascentSumPositive
    · exact ascentNumeric

theorem fullRecordInputs_not_isUnimodal_of_primeWeightSum_bounds
    (k : Nat) (hk : 2 ≤ k)
    (gapBound :
      1113106 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 455703) - 1))
    (twin : ConsecutivePrimes recordLower recordUpper)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (recordGapCenter - 455703) - 1)
    (ascentDefined : k - 1 ≤ Nat.primeCounting' recordLower)
    (descentNumeric :
      ((k - 1 : Nat) : Real) < 1113107 *
        (primeWeightSumBelow
            (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1)) -
          primeWeightSumBelow (primeAt (k - 2))))
    (ascentNumeric :
      3 * primeWeightSumBelow recordLower < ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  apply fullRecordInputs_not_isUnimodal_of_weight_bounds k hk gapBound twin
    descentDefined ascentDefined
  · have descentReal :
        ((k - 1 : Nat) : Real) < 1113107 *
          (realWeightSum
              (primesBelow
                (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1))) -
            realLeadingWeightSum
              (primesBelow
                (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1)))
              (k - 2)) := by
        rw [realLeadingWeightSum_primesBelow_primeAt]
        · simpa only [primeWeightSumBelow] using descentNumeric
        · omega
    rw [← ratCast_weightSum, ← ratCast_leadingWeightSum] at descentReal
    exact_mod_cast descentReal
  · have ascentReal :
        3 * realWeightSum (primesBelow recordLower) <
          ((k - 1 : Nat) : Real) := by
        simpa only [primeWeightSumBelow] using ascentNumeric
    rw [← ratCast_weightSum] at ascentReal
    exact_mod_cast ascentReal

end

end PrimeFactorUnimodality
