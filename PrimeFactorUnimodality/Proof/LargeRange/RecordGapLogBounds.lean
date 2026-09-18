import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapLowerBound

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

/-! # Certified logarithmic size of the record-gap input -/

namespace PrimeFactorUnimodality

noncomputable section

private theorem rational_lt_log_of_two_three_power
    (n a b d : Nat) (c : Real) (_hn : 0 < n) (hd : 0 < d)
    (powerLt : (2 : Real) ^ a * 3 ^ b < n ^ d)
    (linearLt : (d : Real) * c <
      (a : Real) * 0.6931471803 + (b : Real) * 1.0986122885) :
    c < Real.log n := by
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at logged
  have logTwo : (0.6931471803 : Real) < Real.log 2 := Real.log_two_gt_d9
  have logThree : (1.0986122885 : Real) < Real.log 3 := Real.log_three_gt_d9
  have dPos : (0 : Real) < d := by exact_mod_cast hd
  have aNonneg : (0 : Real) ≤ a := by positivity
  have bNonneg : (0 : Real) ≤ b := by positivity
  nlinarith

private theorem log13 : (256 : Real) / 100 < Real.log 13 := by
  apply rational_lt_log_of_two_three_power 13 0 7 3 (256 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log3221 : (807 : Real) / 100 < Real.log 3221 := by
  apply rational_lt_log_of_two_three_power 3221 8 17 3 (807 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log7043 : (885 : Real) / 100 < Real.log 7043 := by
  apply rational_lt_log_of_two_three_power 7043 32 4 3 (885 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log11197 : (932 : Real) / 100 < Real.log 11197 := by
  apply rational_lt_log_of_two_three_power 11197 34 4 3 (932 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log15461 : (964 : Real) / 100 < Real.log 15461 := by
  apply rational_lt_log_of_two_three_power 15461 3 42 5 (964 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log19961 : (990 : Real) / 100 < Real.log 19961 := by
  apply rational_lt_log_of_two_three_power 19961 27 10 3 (990 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log24373 : (1010 : Real) / 100 < Real.log 24373 := by
  apply rational_lt_log_of_two_three_power 24373 70 11 6 (1010 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log29021 : (1027 : Real) / 100 < Real.log 29021 := by
  apply rational_lt_log_of_two_three_power 29021 8 23 3 (1027 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log33641 : (1042 : Real) / 100 < Real.log 33641 := by
  apply rational_lt_log_of_two_three_power 33641 11 31 4 (1042 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log38453 : (1055 : Real) / 100 < Real.log 38453 := by
  apply rational_lt_log_of_two_three_power 38453 33 8 3 (1055 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem log_nat_power_list_prod (l : List (Nat × Nat))
    (h : ∀ factor ∈ l, factor.1 ≠ 0) :
    Real.log (((l.map (fun factor => (factor.1 : Nat) ^ factor.2)).prod : Nat) : Real) =
      (l.map (fun factor => (factor.2 : Real) * Real.log factor.1)).sum := by
  induction l with
  | nil => simp
  | cons factor l ih =>
      have hf : factor.1 ≠ 0 := h factor (by simp)
      have hl : ∀ item ∈ l, item.1 ≠ 0 := by
        intro item hi
        exact h item (by simp [hi])
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul, Real.log_pow, ih hl]
      · exact_mod_cast pow_ne_zero factor.2 hf
      · have prodPos : 0 < (l.map (fun item => item.1 ^ item.2)).prod := by
          apply List.prod_pos
          intro n hn
          simp only [List.mem_map] at hn
          obtain ⟨item, hi, rfl⟩ := hn
          exact pow_pos (Nat.pos_of_ne_zero (hl item hi)) _
        exact_mod_cast prodPos.ne'

theorem log_recordGapLowerProduct_gt :
    (40340 : Real) < Real.log recordGapLowerProduct := by
  have expansion : Real.log recordGapLowerProduct =
      450 * Real.log 13 + 450 * Real.log 3221 + 450 * Real.log 7043 +
      450 * Real.log 11197 + 450 * Real.log 15461 +
      450 * Real.log 19961 + 450 * Real.log 24373 +
      450 * Real.log 29021 + 450 * Real.log 33641 +
      449 * Real.log 38453 := by
    rw [recordGapLowerProduct, log_nat_power_list_prod]
    · simp only [recordGapLowerFactors, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      ring
    · simp [recordGapLowerFactors]
  rw [expansion]
  nlinarith [log13, log3221, log7043, log11197, log15461,
    log19961, log24373, log29021, log33641, log38453]

theorem log_recordGapTailProduct_gt :
    (40340 : Real) < Real.log recordGapTailProduct := by
  have lowerPos : 0 < recordGapLowerProduct := by
    simp [recordGapLowerProduct, recordGapLowerFactors]
  exact log_recordGapLowerProduct_gt.trans_le
    (Real.log_le_log (by exact_mod_cast lowerPos)
      (by exact_mod_cast recordGapLowerProduct_le_tail))

theorem recordGapTailProduct_le_halfLower :
    recordGapTailProduct ≤ (recordGapCenter - 86399) / 2 := by
  have tailLarge : 148 ≤ recordGapTailProduct := by
    apply (show 148 ≤ recordGapLowerProduct by
      rw [recordGapLowerProduct, recordGapLowerFactors]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact (show 148 ≤ 13 ^ 450 by norm_num).trans
        (Nat.le_mul_of_pos_right _ (by positivity))) |>.trans
    exact recordGapLowerProduct_le_tail
  rw [recordGapCenter]
  omega

theorem log_recordGapHalfLower_gt :
    (40340 : Real) <
      Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) := by
  have tailPos : (0 : Real) < recordGapTailProduct := by
    exact_mod_cast (show 0 < recordGapTailProduct by
      have := recordGapTailProduct_le_halfLower
      have lower := recordGapLowerProduct_le_tail
      have lowerPos : 0 < recordGapLowerProduct := by
        simp [recordGapLowerProduct, recordGapLowerFactors]
      omega)
  exact log_recordGapTailProduct_gt.trans_le
    (Real.log_le_log tailPos (by exact_mod_cast recordGapTailProduct_le_halfLower))

private theorem log40340 : (1060 : Real) / 100 < Real.log 40340 := by
  apply rational_lt_log_of_two_three_power 40340 39 14 4 (1060 / 100)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem log_log_recordGapHalfLower_gt :
    (1060 : Real) / 100 <
      Real.log (Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real)) := by
  exact log40340.trans
    (Real.log_lt_log (by norm_num) log_recordGapHalfLower_gt)

end

end PrimeFactorUnimodality
