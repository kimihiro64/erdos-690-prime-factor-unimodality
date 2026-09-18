import PrimeFactorUnimodality.Proof.LargeRange.FullRecordSideConditions
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapLogBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordNumericBounds

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Closed numerical bounds for the full finite record range -/

namespace PrimeFactorUnimodality

noncomputable section

theorem recordGapTailProduct_le_fullRecordHalfLower :
    recordGapTailProduct ≤ (recordGapCenter - 455703) / 2 := by
  have tailLarge : 800000 ≤ recordGapTailProduct := by
    have lower : recordGapLowerProduct ≤ recordGapTailProduct :=
      recordGapLowerProduct_le_tail
    have lowerLarge : 800000 ≤ recordGapLowerProduct := by
      rw [recordGapLowerProduct, recordGapLowerFactors]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact (show 800000 ≤ 13 ^ 450 by norm_num).trans
        (Nat.le_mul_of_pos_right _ (by positivity))
    exact lowerLarge.trans lower
  rw [recordGapCenter]
  omega

theorem log_fullRecordHalfLower_gt :
    (40340 : Real) <
      Real.log (((recordGapCenter - 455703) / 2 : Nat) : Real) := by
  have tailPos : (0 : Real) < recordGapTailProduct := by
    exact_mod_cast (show 0 < recordGapTailProduct by
      have lower := recordGapLowerProduct_le_tail
      have lowerPos : 0 < recordGapLowerProduct := by
        simp [recordGapLowerProduct, recordGapLowerFactors]
      omega)
  exact log_recordGapTailProduct_gt.trans_le
    (Real.log_le_log tailPos
      (by exact_mod_cast recordGapTailProduct_le_fullRecordHalfLower))

theorem log_log_fullRecordHalfLower_gt :
    (1060 : Real) / 100 <
      Real.log (Real.log (((recordGapCenter - 455703) / 2 : Nat) : Real)) := by
  have log40340 : (1060 : Real) / 100 < Real.log 40340 := by
    have powerLt : (2 : Real) ^ 39 * 3 ^ 14 < 40340 ^ (4 : Nat) := by norm_num
    have logged := Real.log_lt_log (by positivity) powerLt
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow, Real.log_pow] at logged
    norm_num at logged ⊢
    nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  exact log40340.trans
    (Real.log_lt_log (by norm_num) log_fullRecordHalfLower_gt)

private theorem log_800000000_lt_21 :
    Real.log 800000000 < (21 : Real) := by
  have powerLt : (800000000 : Real) < 3 ^ (19 : Nat) := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_three_lt_d9]

private theorem log_21_lt_61_div_20 :
    Real.log 21 < (61 : Real) / 20 := by
  have powerLt : (21 : Real) ^ 10 < 2 ^ (28 : Nat) * 3 ^ (10 : Nat) := by
    norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9]

theorem fullRecord_prefix_log_log_lt {k : Nat}
    (hkLower : 38001 ≤ k) (hkUpper : k ≤ 7300000) :
    Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) <
      (78 : Real) / 25 := by
  have prefixLarge : 2 ≤ primeAt (k - 2) - 1 := by
    have primeFive : 5 ≤ primeAt (k - 2) := by
      have indexTwo : 2 ≤ k - 2 := by omega
      have monotone := primeAt_strictMono.monotone indexTwo
      norm_num [primeAt] at monotone ⊢
      exact monotone
    omega
  have prefixLe : primeAt (k - 2) - 1 ≤ 800000000 :=
    (Nat.sub_le _ _).trans
      (fullRecord_primeAt_le_800000000 (by omega))
  have innerPos : 0 < Real.log ((primeAt (k - 2) - 1 : Nat) : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < primeAt (k - 2) - 1 by omega))
  have innerLt :
      Real.log ((primeAt (k - 2) - 1 : Nat) : Real) < 21 :=
    (Real.log_le_log (by exact_mod_cast (show 0 < primeAt (k - 2) - 1 by omega))
      (by exact_mod_cast prefixLe)).trans_lt log_800000000_lt_21
  exact (Real.log_lt_log innerPos innerLt).trans log_21_lt_61_div_20

theorem fullRecordHalf_mertensError_lt :
    mertensErrorConstant /
        Real.log (((recordGapCenter - 455703) / 2 : Nat) : Real) <
      (1 : Real) / 1000 := by
  have logPos : 0 <
      Real.log (((recordGapCenter - 455703) / 2 : Nat) : Real) := by
    linarith [log_fullRecordHalfLower_gt]
  rw [div_lt_iff₀ logPos]
  nlinarith [mertensErrorConstant_lt_901_div_100,
    log_fullRecordHalfLower_gt]

theorem fullRecord_prefix_mertensError_lt {k : Nat} (hk : 38001 ≤ k) :
    mertensErrorConstant /
        Real.log ((primeAt (k - 2) - 1 : Nat) : Real) <
      (9 : Real) / 10 := by
  have indexEq : k - 2 + 2 = k := by omega
  have lower := Nat.add_two_le_nth_prime (k - 2)
  rw [indexEq] at lower
  have prefixLower : 32768 ≤ primeAt (k - 2) - 1 := by omega
  have log32768 : (1035 : Real) / 100 < Real.log 32768 := by
    rw [show (32768 : Real) = 2 ^ (15 : Nat) by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  have logLower : (1035 : Real) / 100 <
      Real.log ((primeAt (k - 2) - 1 : Nat) : Real) :=
    log32768.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast prefixLower))
  have logPos : 0 < Real.log ((primeAt (k - 2) - 1 : Nat) : Real) := by linarith
  rw [div_lt_iff₀ logPos]
  nlinarith [mertensErrorConstant_lt_901_div_100]

theorem fullRecord_descentNumeric {k : Nat}
    (hkLower : 38001 ≤ k) (hkUpper : k ≤ 7300000) :
    ((k - 1 : Nat) : Real) < 1113107 *
      (Real.log (Real.log (((recordGapCenter - 455703) / 2 : Nat) : Real)) -
        Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
        mertensErrorConstant /
          Real.log (((recordGapCenter - 455703) / 2 : Nat) : Real) -
        mertensErrorConstant /
          Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) := by
  have kBound : ((k - 1 : Nat) : Real) ≤ 7299999 := by
    exact_mod_cast (show k - 1 ≤ 7299999 by omega)
  nlinarith [log_log_fullRecordHalfLower_gt,
    fullRecord_prefix_log_log_lt hkLower hkUpper,
    fullRecordHalf_mertensError_lt,
    fullRecord_prefix_mertensError_lt hkLower]

end

end PrimeFactorUnimodality
