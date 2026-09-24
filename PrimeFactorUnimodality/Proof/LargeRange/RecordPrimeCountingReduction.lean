import PrimeFactorUnimodality.Helpers.Analytic.PrimeCountingReciprocalShell
import PrimeFactorUnimodality.Proof.LargeRange.RecordNumericBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordRatioReduction
import PrimeFactorUnimodality.Proof.LargeRange.RecordSideConditions

set_option autoImplicit false

/-! # The record descent from the existing prime-counting shell

Finite Abel summation bounds the weight difference directly. For the upper
record range its endpoint error is less than `1/50`, so the logarithmic bounds
leave a shell greater than eight. This avoids a separate enumeration of the
reciprocal primes below 500,001 without strengthening the analytic hypotheses.
-/

namespace PrimeFactorUnimodality

noncomputable section

private theorem record_prefix_shell_error_lt {k : Nat} (hk : 10372 ≤ k) :
    (6381 / 5000 : Real) /
        (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) ^ 2 +
        1 / ((primeAt (k - 2) - 1 : Nat) : Real) < 1 / 50 := by
  have threshold := record_prefixThreshold hk
  have xLower : (10372 : Real) ≤ ((primeAt (k - 2) - 1 : Nat) : Real) := by
    exact_mod_cast threshold
  have log10372 : (9 : Real) < Real.log 10372 := by
    have powerLt : (2 : Real) ^ 13 < 10372 := by norm_num
    have logged := Real.log_lt_log (by positivity) powerLt
    rw [Real.log_pow] at logged
    norm_num at logged ⊢
    nlinarith [Real.log_two_gt_d9]
  have logLower : (9 : Real) <
      Real.log ((primeAt (k - 2) - 1 : Nat) : Real) :=
    log10372.trans_le (Real.log_le_log (by norm_num) xLower)
  have squareLower : (81 : Real) ≤
      (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) ^ 2 := by
    nlinarith
  have first := div_le_div_of_nonneg_left
    (by norm_num : (0 : Real) ≤ 6381 / 5000)
    (by norm_num : (0 : Real) < 81) squareLower
  have second := one_div_le_one_div_of_le
    (by norm_num : (0 : Real) < 10372) xLower
  calc
    _ ≤ (6381 / 5000 : Real) / 81 + 1 / 10372 := add_le_add first second
    _ < 1 / 50 := by norm_num

theorem record_primeCounting_descentNumeric
    (bounds : HasDusartPrimeCountingBounds)
    {k : Nat} (hkLower : 10372 ≤ k) (hkUpper : k ≤ 38000) :
    ((k - 1 : Nat) : Real) < 4753 *
      (Real.log (Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real)) -
        Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
        (6381 / 5000 : Real) /
          (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) ^ 2 -
        1 / ((primeAt (k - 2) - 1 : Nat) : Real)) := by
  have kBound : ((k - 1 : Nat) : Real) ≤ 37999 := by
    exact_mod_cast (show k - 1 ≤ 37999 by omega)
  have prefixLog := record_prefix_log_log_lt bounds (by omega) hkUpper
  have errorBound := record_prefix_shell_error_lt hkLower
  linarith [log_log_recordGapHalfLower_gt]

/-- The two record inputs and the same prime-counting bounds used in the
infinite tail suffice for the upper part of the finite record range. -/
theorem recordInputs_not_isUnimodal_of_primeCounting
    (bounds : HasDusartPrimeCountingBounds)
    (k : Nat) (hkLower : 10372 ≤ k) (hkUpper : k ≤ 38000)
    (gapBound :
      4752 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 86399) - 1))
    (predecessorHalf :
      (recordGapCenter - 86399) / 2 <
        primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1))
    (twin : ConsecutivePrimes recordLower recordUpper) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let y := (recordGapCenter - 86399) / 2
  have prefixLarge : 600 ≤ primeAt (k - 2) - 1 :=
    (by norm_num : 600 ≤ 10372).trans (record_prefixThreshold hkLower)
  have shell := primeWeightSumBelow_sub_lower_of_primeCounting bounds
    prefixLarge (record_prefix_le_half bounds hkUpper)
  have cutoff : primeAt (k - 2) - 1 + 1 = primeAt (k - 2) := by
    have := one_lt_primeAt (k - 2)
    omega
  rw [cutoff] at shell
  have yCutoff : y + 1 ≤
      primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1) :=
    Nat.add_one_le_iff.mpr predecessorHalf
  have fullLower := primeWeightSumBelow_mono yCutoff
  have numeric := record_primeCounting_descentNumeric bounds hkLower hkUpper
  have descent : ((k - 1 : Nat) : Real) < 4753 *
      (primeWeightSumBelow
          (primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1)) -
        primeWeightSumBelow (primeAt (k - 2))) := by
    dsimp only [y] at fullLower
    linarith
  have recordPredTwo : 2 ≤ recordLower - 1 :=
    (by norm_num : 2 ≤ 10372).trans recordLower_sub_one_ge_10372
  have ascentUpper := primeWeightSumBelow_upper_of_estimate
    hasMertensReciprocalPrimeEstimate recordPredTwo
  rw [Nat.sub_add_cancel recordLower_gt_one.le] at ascentUpper
  have ascentNumeric := record_coarse_ascentNumeric (k := k) (by omega)
  have ascent : 3 * primeWeightSumBelow recordLower < ((k - 1 : Nat) : Real) := by
    linarith [mertensConstant_lt_two_thirds]
  exact recordInputs_not_isUnimodal_of_primeWeightSum_bounds k (by omega)
    gapBound twin (record_descentDefined bounds (by omega) hkUpper)
      (record_ascentDefined bounds (by omega) hkUpper) descent ascent

end

end PrimeFactorUnimodality
