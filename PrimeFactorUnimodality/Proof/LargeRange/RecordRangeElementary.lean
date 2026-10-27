import PrimeFactorUnimodality.Helpers.Analytic.AnalyticDensityWeights
import PrimeFactorUnimodality.Helpers.Analytic.RecordElementaryScalars
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapLogBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinLogBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordValley

set_option autoImplicit false

/-! # The record-input range from elementary reciprocal estimates -/

namespace PrimeFactorUnimodality

noncomputable section

theorem recordRange_not_isUnimodal_elementary
    (gapBound : 4752 <= primeGap (Nat.primeCounting' (recordGapCenter - 86399) - 1))
    (predecessor : (recordGapCenter - 86399) / 2 <
      primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1))
    (twin : ConsecutivePrimes recordLower recordUpper)
    (k : Nat) (hkLower : 49 <= k) (hkUpper : k <= 38000) :
    Not (IsUnimodal (primeFactorDensity k)) := by
  let i := Nat.primeCounting' (recordGapCenter - 86399) - 1
  let Y := (recordGapCenter - 86399) / 2
  have hY : 4752 <= Y := by
    have h := recordGapCenter_large
    dsimp [Y]
    omega
  have hS : (38776 : Real) < 4752 * Mertens.smoothedPrimeSum 4752 Y :=
    record_smoothed_sum_lower Y (by exact_mod_cast hY)
      (by convert log_log_recordGapHalfLower_gt using 1 <;> norm_num)
  have hMean : ((k - 1 : Nat) : Real) <
      tiltedPrimeWeightMean (primesBelow (primeAt i)) 4752 := by
    have hmean := smoothedPrimeSum_mul_le_tiltedMean 4752 Y (primeAt i)
      (by norm_num) (Nat.cast_nonneg Y) (Nat.cast_lt.mpr predecessor)
    have hk : ((k - 1 : Nat) : Real) <= 37999 := by exact_mod_cast (by omega : k - 1 <= 37999)
    linarith
  have hLength : k - 1 <= (primesBelow (primeAt i)).length := by
    have hh := tiltedPrimeWeightMean_le_length (primesBelow (primeAt i))
      (primesBelow_gt_one _) 4752 (by norm_num)
    have hlt : ((k - 1 : Nat) : Real) < (primesBelow (primeAt i)).length := hMean.trans_le hh
    exact (by exact_mod_cast hlt : k - 1 < (primesBelow (primeAt i)).length).le
  have hDefined : k - 1 <= i := by simpa only [primesBelow_primeAt_length] using hLength
  have hAscent : k - 1 <= Nat.primeCounting' recordLower :=
    hDefined.trans recordGapIndex_lt_recordTwinIndex.le
  have hDescentReal := densityRatio_lt_of_lt_tiltedPrimeWeightMean
    (primesBelow (primeAt i)) (primesBelow_gt_one _) (k - 1) (by omega) 4752
      (by norm_num) hMean
  have hDescent : densityRatio (primesBelow (primeAt i)) (k - 1) < 4753 := by
    exact_mod_cast hDescentReal.trans_le (by norm_num : (4752 : Real) <= 4753)
  have hQ : 1000 <= recordLower - 1 := recordLower_sub_one_ge_10372.trans' (by norm_num)
  have hLogQ : (9 : Real) < Real.log ((recordLower - 1 : Nat) : Real) := by
    have hLog : (9 : Real) < Real.log 10372 := by
      have hh := Real.log_lt_log (by positivity : (0 : Real) < 2 ^ (13 : Nat))
        (by norm_num : (2 : Real) ^ (13 : Nat) < 10372)
      rw [Real.log_pow] at hh
      norm_num at hh
      linarith [LogTables.log_2_gt]
    exact hLog.trans_le (Real.log_le_log (by norm_num)
      (by exact_mod_cast recordLower_sub_one_ge_10372))
  have hShift := record_shifted_sum_upper ((recordLower - 1 : Nat) : Real)
    (by exact_mod_cast hQ) hLogQ
      (by convert log_log_recordLower_sub_one_lt using 1 <;> norm_num)
  rw [<- primeWeightSumBelow_eq_shifted recordLower (by have h := recordLower_gt_one; omega),
    <- ratCast_weightSum_primesBelow] at hShift
  have hDegree : (48 : Real) <= ((k - 1 : Nat) : Real) := by exact_mod_cast (by omega : 48 <= k - 1)
  have hAscentNumeric : 3 * weightSum (primesBelow recordLower) < ((k - 1 : Nat) : Rat) := by
    exact_mod_cast hShift.trans_le hDegree
  have hAscentLength : k - 1 <= (primesBelow recordLower).length := by
    rw [<- primeAt_primeCounting' recordLower twin.left_prime, primesBelow_primeAt_length]
    exact hAscent
  have hNonempty : Not (primesBelow recordLower = []) := by
    intro h
    simp only [h, List.length_nil] at hAscentLength
    omega
  have hSum := weightSum_pos_of_ne_nil _ (primesBelow_gt_one _) hNonempty
  have hAscentRatio : 3 < densityRatio (primesBelow recordLower) (k - 1) :=
    bound_lt_densityRatio_of_bound_mul_weightSum_lt_degree _ (primesBelow_gt_one _)
      _ hAscentLength 3 hSum hAscentNumeric
  exact recordInputs_not_isUnimodal k (by omega) gapBound twin hDefined hAscent
    hDescent hAscentRatio

end

end PrimeFactorUnimodality
