import PrimeFactorUnimodality.Helpers.Analytic.MertensProvider
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapLogBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.RecordPrefixBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinLogBounds

set_option autoImplicit false

/-! # Closed numerical inequalities for the record-input range -/

namespace PrimeFactorUnimodality

noncomputable section

theorem record_ascentNumeric {k : Nat} (hk : 49 ≤ k) :
    3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) +
        Mertens.M +
          dusartReciprocalError (((recordLower - 1 : Nat) : Real)) + 1) <
      ((k - 1 : Nat) : Real) := by
  have kBound : (48 : Real) ≤ ((k - 1 : Nat) : Real) := by
    exact_mod_cast (show 48 ≤ k - 1 by omega)
  nlinarith [log_log_recordLower_sub_one_lt,
    mertensConstant_lt_two_thirds,
    recordLower_dusartReciprocalError_lt]

theorem recordLower_mertensError_lt :
    mertensErrorConstant / Real.log ((recordLower - 1 : Nat) : Real) <
      (101 : Real) / 100 := by
  have logLower : (9 : Real) < Real.log ((recordLower - 1 : Nat) : Real) := by
    have log10372 : (9 : Real) < Real.log 10372 := by
      have powerLt : (2 : Real) ^ 13 < 10372 := by norm_num
      have logged := Real.log_lt_log (by positivity) powerLt
      rw [Real.log_pow] at logged
      norm_num at logged ⊢
      nlinarith [Real.log_two_gt_d9]
    exact log10372.trans_le
      (Real.log_le_log (by norm_num)
        (by exact_mod_cast recordLower_sub_one_ge_10372))
  have logPos : 0 < Real.log ((recordLower - 1 : Nat) : Real) := by linarith
  rw [div_lt_iff₀ logPos]
  nlinarith [mertensErrorConstant_lt_901_div_100]

theorem record_coarse_ascentNumeric {k : Nat} (hk : 49 ≤ k) :
    3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) +
        (2 : Real) / 3 +
          mertensErrorConstant / Real.log ((recordLower - 1 : Nat) : Real) + 1) <
      ((k - 1 : Nat) : Real) := by
  have kBound : (48 : Real) ≤ ((k - 1 : Nat) : Real) := by
    exact_mod_cast (show 48 ≤ k - 1 by omega)
  nlinarith [log_log_recordLower_sub_one_lt, recordLower_mertensError_lt]

theorem record_prefixThreshold {k : Nat} (hk : 10372 ≤ k) :
    10372 ≤ primeAt (k - 2) - 1 := by
  have lower := primeAt_strictMono.add_le_nat (k - 4) 2
  have indexEq : k - 4 + 2 = k - 2 := by omega
  have baseValue : primeAt 2 = 5 := Nat.nth_prime_two_eq_five
  have stronger : k + 1 ≤ primeAt (k - 2) := by
    calc
      k + 1 = (k - 4) + primeAt 2 := by rw [baseValue]; omega
      _ ≤ primeAt ((k - 4) + 2) := lower
      _ = primeAt (k - 2) := by rw [indexEq]
  omega

theorem record_halfLower_ge_10372 :
    10372 ≤ (recordGapCenter - 86399) / 2 := by
  have := recordGapCenter_large
  omega

theorem record_descentNumeric
    {k : Nat} (hkLower : 10372 ≤ k) (hkUpper : k ≤ 38000) :
    ((k - 1 : Nat) : Real) < 4753 *
      (Real.log (Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real)) -
        Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
        dusartReciprocalError
          ((((recordGapCenter - 86399) / 2 : Nat) : Real)) -
        dusartReciprocalError (((primeAt (k - 2) - 1 : Nat) : Real))) := by
  have kBound : ((k - 1 : Nat) : Real) ≤ 37999 := by
    exact_mod_cast (show k - 1 ≤ 37999 by omega)
  have prefixLog := record_prefix_log_log_lt
    (show 49 ≤ k by omega) hkUpper
  have yError := dusartReciprocalError_lt_one_div_100_of_ge_10372
    record_halfLower_ge_10372
  have xError := dusartReciprocalError_lt_one_div_100_of_ge_10372
    (record_prefixThreshold hkLower)
  nlinarith [log_log_recordGapHalfLower_gt]

private theorem log_48_gt : (38 : Real) / 10 < Real.log 48 := by
  have powerLt : (2 : Real) ^ 11 < 48 ^ 2 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_gt_d9]

theorem record_prefix_log_gt_38_div_10 {k : Nat} (hk : 49 ≤ k) :
    (38 : Real) / 10 < Real.log ((primeAt (k - 2) - 1 : Nat) : Real) := by
  have indexEq : k - 2 + 2 = k := by omega
  have lower := Nat.add_two_le_nth_prime (k - 2)
  rw [indexEq] at lower
  change k ≤ primeAt (k - 2) at lower
  have fortyEight : 48 ≤ primeAt (k - 2) - 1 := by omega
  exact log_48_gt.trans_le
    (Real.log_le_log (by norm_num) (by exact_mod_cast fortyEight))

theorem record_halfLower_mertensError_lt :
    mertensErrorConstant /
        Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) <
      (1 : Real) / 1000 := by
  have logPos : 0 <
      Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) := by
    linarith [log_recordGapHalfLower_gt]
  rw [div_lt_iff₀ logPos]
  nlinarith [mertensErrorConstant_lt_901_div_100,
    log_recordGapHalfLower_gt]

theorem record_prefix_mertensError_lt {k : Nat} (hk : 49 ≤ k) :
    mertensErrorConstant /
        Real.log ((primeAt (k - 2) - 1 : Nat) : Real) <
      (2372 : Real) / 1000 := by
  have logLower := record_prefix_log_gt_38_div_10 hk
  have logPos : 0 < Real.log ((primeAt (k - 2) - 1 : Nat) : Real) := by
    linarith
  rw [div_lt_iff₀ logPos]
  nlinarith [mertensErrorConstant_lt_901_div_100]

theorem record_prefix_mertensError_lt_101_div_100
    {k : Nat} (hk : 10372 ≤ k) :
    mertensErrorConstant /
        Real.log ((primeAt (k - 2) - 1 : Nat) : Real) <
      (101 : Real) / 100 := by
  have threshold := record_prefixThreshold hk
  have log10372 : (9 : Real) < Real.log 10372 := by
    have powerLt : (2 : Real) ^ 13 < 10372 := by norm_num
    have logged := Real.log_lt_log (by positivity) powerLt
    rw [Real.log_pow] at logged
    norm_num at logged ⊢
    nlinarith [Real.log_two_gt_d9]
  have logLower : (9 : Real) <
      Real.log ((primeAt (k - 2) - 1 : Nat) : Real) :=
    log10372.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast threshold))
  have logPos : 0 <
      Real.log ((primeAt (k - 2) - 1 : Nat) : Real) := by linarith
  rw [div_lt_iff₀ logPos]
  nlinarith [mertensErrorConstant_lt_901_div_100]

theorem record_coarse_descentNumeric
    {k : Nat} (hkLower : 49 ≤ k) (hkUpper : k ≤ 10372) :
    ((k - 1 : Nat) : Real) < 4753 *
      (Real.log (Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real)) -
        Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
        mertensErrorConstant /
          Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) -
        mertensErrorConstant /
          Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) := by
  have kBound : ((k - 1 : Nat) : Real) ≤ 10371 := by
    exact_mod_cast (show k - 1 ≤ 10371 by omega)
  have prefixLog := record_prefix_log_log_lt hkLower
    (hkUpper.trans (by norm_num))
  nlinarith [log_log_recordGapHalfLower_gt,
    record_halfLower_mertensError_lt,
    record_prefix_mertensError_lt hkLower]

/-- The sharper elementary lower bound on the prime prefix extends the proved
Mertens estimate through most of the record range. -/
theorem record_coarse_descentNumeric_mid
    {k : Nat} (hkLower : 10372 ≤ k) (hkUpper : k ≤ 33314) :
    ((k - 1 : Nat) : Real) < 4753 *
      (Real.log (Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real)) -
        Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
        mertensErrorConstant /
          Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) -
        mertensErrorConstant /
          Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) := by
  have kBound : ((k - 1 : Nat) : Real) ≤ 33313 := by
    exact_mod_cast (show k - 1 ≤ 33313 by omega)
  have prefixLog := record_prefix_log_log_lt
    (show 49 ≤ k by omega) (hkUpper.trans (by norm_num))
  nlinarith [log_log_recordGapHalfLower_gt,
    record_halfLower_mertensError_lt,
    record_prefix_mertensError_lt_101_div_100 hkLower]

/-- Numerical margin for the finite-prefix certificate.  The rounded
reciprocal sum stays just below `71/25`, leaving enough room through the full
record cutoff. -/
theorem record_finite_prefix_descentNumeric
    {k : Nat} (hkUpper : k ≤ 38000) :
    ((k - 1 : Nat) : Real) < 4753 *
      (Real.log (Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real)) +
        Mertens.M - mertensErrorConstant /
          Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) -
        (71 : Real) / 25) := by
  have kBound : ((k - 1 : Nat) : Real) ≤ 37999 := by
    exact_mod_cast (show k - 1 ≤ 37999 by omega)
  nlinarith [log_log_recordGapHalfLower_gt,
    mertensConstant_gt_six_twenty_fifths,
    record_halfLower_mertensError_lt]

end

end PrimeFactorUnimodality
