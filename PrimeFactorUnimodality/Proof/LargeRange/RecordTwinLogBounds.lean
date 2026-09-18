import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Helpers.Analytic.ReciprocalPrimeBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinStructure

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Logarithmic bounds for the certified record twin -/

namespace PrimeFactorUnimodality

noncomputable section

theorem log_recordLower_sub_one_lt :
    Real.log ((recordLower - 1 : Nat) : Real) < 165000 := by
  have lowerSubPos : 0 < recordLower - 1 := by
    have := recordLower_gt_one
    omega
  have baseLt : recordBase < 2 ^ 29 := by
    norm_num [recordBase]
  have factorSqEq : recordFactor ^ 2 = recordBase ^ 8192 := by
    rw [recordFactor, ← pow_mul]
  have lowerLt : recordLower - 1 < (2 ^ 29) ^ 8192 := by
    calc
      recordLower - 1 < recordFactor ^ 2 :=
        (Nat.sub_le recordLower 1).trans_lt recordLower_lt_factor_sq
      _ = recordBase ^ 8192 := factorSqEq
      _ < (2 ^ 29) ^ 8192 := Nat.pow_lt_pow_left baseLt (by omega)
  have lowerSubPosReal : (0 : Real) < (recordLower - 1 : Nat) :=
    Nat.cast_pos.mpr lowerSubPos
  have lowerLtReal :
      ((recordLower - 1 : Nat) : Real) < (((2 ^ 29) ^ 8192 : Nat) : Real) :=
    Nat.cast_lt.mpr lowerLt
  have logged := Real.log_lt_log lowerSubPosReal lowerLtReal
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9]

private theorem log_165000_lt : Real.log 165000 < (121 : Real) / 10 := by
  have powerLt : (165000 : Real) < 3 ^ 11 := by norm_num
  have logged := Real.log_lt_log (by norm_num) powerLt
  rw [Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_three_lt_d9]

theorem log_log_recordLower_sub_one_lt :
    Real.log (Real.log ((recordLower - 1 : Nat) : Real)) < (121 : Real) / 10 := by
  have lowerSubOne : (1 : Real) < (recordLower - 1 : Nat) := by
    exact_mod_cast (show 1 < recordLower - 1 by
      have factorFive : 5 ≤ recordFactor := by
        unfold recordFactor recordBase
        exact (by norm_num : 5 ≤ 504983334).trans (Nat.le_pow (by norm_num))
      rw [recordLower]
      have productLarge : 20 ≤ recordFactor * (recordFactor - 1) :=
        Nat.mul_le_mul factorFive (show 4 ≤ recordFactor - 1 by omega)
      omega)
  have innerPos : 0 < Real.log ((recordLower - 1 : Nat) : Real) :=
    Real.log_pos lowerSubOne
  exact (Real.log_lt_log innerPos log_recordLower_sub_one_lt).trans log_165000_lt

theorem recordLower_sub_one_ge_10372 : 10372 ≤ recordLower - 1 := by
  have factorLarge : 504983334 ≤ recordFactor := by
    unfold recordFactor recordBase
    exact Nat.le_pow (by norm_num)
  rw [recordLower]
  have productLarge : 504983334 * 504983333 ≤
      recordFactor * (recordFactor - 1) :=
    Nat.mul_le_mul factorLarge (by omega)
  omega

theorem dusartReciprocalError_lt_one_div_100_of_ge_10372
    {x : Nat} (hx : 10372 ≤ x) :
    dusartReciprocalError (x : Real) < (1 : Real) / 100 := by
  have log10372 : (9 : Real) < Real.log 10372 := by
    have powerLt : (2 : Real) ^ 13 < 10372 := by norm_num
    have logged := Real.log_lt_log (by positivity) powerLt
    rw [Real.log_pow] at logged
    norm_num at logged ⊢
    nlinarith [Real.log_two_gt_d9]
  have logLower : (9 : Real) < Real.log x :=
    log10372.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hx))
  have logPos : 0 < Real.log x := by linarith
  have squareLarge : (81 : Real) < (Real.log x) ^ 2 := by nlinarith
  have cubeLarge : (729 : Real) < (Real.log x) ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos logPos) logPos]
  have first : 1 / (10 * (Real.log x) ^ 2) < (1 : Real) / 810 := by
    apply one_div_lt_one_div_of_lt (by norm_num)
    nlinarith
  have second : 4 / (15 * (Real.log x) ^ 3) < (4 : Real) / 10935 := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith
  unfold dusartReciprocalError
  linarith

theorem recordLower_dusartReciprocalError_lt :
    dusartReciprocalError ((recordLower - 1 : Nat) : Real) <
      (1 : Real) / 100 :=
  dusartReciprocalError_lt_one_div_100_of_ge_10372 recordLower_sub_one_ge_10372

end

end PrimeFactorUnimodality
