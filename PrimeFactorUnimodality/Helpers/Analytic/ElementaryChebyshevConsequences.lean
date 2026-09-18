import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import VendorPrimeNumberTheoremAnd.ElementaryChebyshev

set_option autoImplicit false

/-!
# Clean consequences of the elementary Chebyshev estimates

The source estimates are converted here into simple rational-relative bounds
above one million. These provide a proved fallback for the uniform-tail prime
distribution argument without importing any unfinished explicit-PNT modules.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem log_twoHundredFiftyThousand_lt_thirteen :
    Real.log (250000 : Real) < 13 := by
  have powerLt : (250000 : Real) < 2 ^ (18 : Nat) := by norm_num
  have logged := Real.log_lt_log (by norm_num) powerLt
  rw [Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9]

theorem log_div_sqrt_le_twentySix_thousandths {x : Real}
    (hx : 250000 ≤ x) :
    Real.log x / Real.sqrt x ≤ (26 : Real) / 1000 := by
  have expTwoLe : Real.exp 2 ≤ (250000 : Real) := by
    have expTwoLt : Real.exp 2 < 9 := by
      rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
      have expOneLtThree : Real.exp 1 < 3 :=
        Real.exp_one_lt_d9.trans (by norm_num)
      convert mul_self_lt_mul_self (Real.exp_pos 1).le expOneLtThree using 1
      all_goals norm_num
    linarith
  have monotone := Real.log_div_sqrt_antitoneOn expTwoLe
    (expTwoLe.trans hx) hx
  change Real.log x / Real.sqrt x ≤
    Real.log (250000 : Real) / Real.sqrt (250000 : Real) at monotone
  have sqrtBase : Real.sqrt (250000 : Real) = 500 := by
    rw [show (250000 : Real) = 500 ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg]
    all_goals norm_num
  rw [sqrtBase] at monotone
  have base : Real.log (250000 : Real) / 500 ≤ (13 : Real) / 500 :=
    (div_le_div_iff_of_pos_right (by norm_num)).2
      log_twoHundredFiftyThousand_lt_thirteen.le
  apply monotone.trans
  convert base using 1
  norm_num

theorem log_le_fiftyTwo_millionths_mul {x : Real}
    (hx : 250000 ≤ x) :
    Real.log x ≤ (52 : Real) / 1000000 * x := by
  have expOneLe : Real.exp 1 ≤ (250000 : Real) := by
    linarith [Real.exp_one_lt_d9]
  have ratio := Real.log_div_self_antitoneOn expOneLe
    (expOneLe.trans hx) hx
  change Real.log x / x ≤ Real.log (250000 : Real) / 250000 at ratio
  have xPos : 0 < x := by linarith
  have basePos : (0 : Real) < 250000 := by norm_num
  have baseRatio : Real.log (250000 : Real) / 250000 <
      (52 : Real) / 1000000 := by
    apply (div_lt_iff₀ basePos).2
    norm_num
    exact log_twoHundredFiftyThousand_lt_thirteen
  have combined := ratio.trans baseRatio.le
  rw [div_le_iff₀ xPos] at combined
  simpa [mul_comm] using combined

theorem elementary_psi_lower_from_250000 {x : Real} (hx : 250000 ≤ x) :
    (92 : Real) / 100 * x ≤ Chebyshev.psi x := by
  have source := Chebyshev.psi_lower x (by linarith)
  have logBound := log_le_fiftyTwo_millionths_mul hx
  have aLower := Chebyshev.a_bound.1
  nlinarith

theorem elementary_theta_lower_from_250000 {x : Real} (hx : 250000 ≤ x) :
    (86 : Real) / 100 * x ≤ Chebyshev.theta x := by
  have psiLower := elementary_psi_lower_from_250000 hx
  have difference := Chebyshev.psi_sub_theta_le (x := x) (by linarith)
  have ratio := log_div_sqrt_le_twentySix_thousandths hx
  have xNonneg : 0 ≤ x := by linarith
  have sqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have correction : 2 * Real.sqrt x * Real.log x ≤ (52 : Real) / 1000 * x := by
    have scaled := mul_le_mul_of_nonneg_left ratio (show 0 ≤ 2 * x by positivity)
    have identity :
        2 * x * (Real.log x / Real.sqrt x) =
          2 * Real.sqrt x * Real.log x := by
      field_simp [sqrtPos.ne']
      rw [Real.sq_sqrt xNonneg]
      ring
    rw [identity] at scaled
    nlinarith
  linarith

theorem log_oneMillion_lt_fourteen :
    Real.log (1000000 : Real) < 14 := by
  have power_lt : (1000000 : Real) < 2 ^ (20 : Nat) := by norm_num
  have logged := Real.log_lt_log (by norm_num) power_lt
  rw [Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9]

theorem log_div_sqrt_le_fourteen_thousandths {x : Real}
    (hx : 1000000 ≤ x) :
    Real.log x / Real.sqrt x ≤ (14 : Real) / 1000 := by
  have expTwoLe : Real.exp 2 ≤ (1000000 : Real) := by
    have expTwoLt : Real.exp 2 < 9 := by
      rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
      have expOneLtThree : Real.exp 1 < 3 :=
        Real.exp_one_lt_d9.trans (by norm_num)
      convert mul_self_lt_mul_self (Real.exp_pos 1).le expOneLtThree using 1
      all_goals norm_num
    linarith
  have monotone := Real.log_div_sqrt_antitoneOn expTwoLe
    (expTwoLe.trans hx) hx
  change Real.log x / Real.sqrt x ≤
    Real.log (1000000 : Real) / Real.sqrt (1000000 : Real) at monotone
  have sqrtMillion : Real.sqrt (1000000 : Real) = 1000 := by
    rw [show (1000000 : Real) = 1000 ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_nonneg]
    all_goals norm_num
  rw [sqrtMillion] at monotone
  exact monotone.trans ((div_le_div_iff_of_pos_right
    (by norm_num : (0 : Real) < 1000)).2
    log_oneMillion_lt_fourteen.le)

theorem log_le_fourteen_millionths_mul {x : Real}
    (hx : 1000000 ≤ x) :
    Real.log x ≤ (14 : Real) / 1000000 * x := by
  have expOneLe : Real.exp 1 ≤ (1000000 : Real) := by
    linarith [Real.exp_one_lt_d9]
  have ratio := Real.log_div_self_antitoneOn expOneLe
    (expOneLe.trans hx) hx
  change Real.log x / x ≤ Real.log (1000000 : Real) / 1000000 at ratio
  have xPos : 0 < x := by linarith
  have millionPos : (0 : Real) < 1000000 := by norm_num
  have baseRatio : Real.log (1000000 : Real) / 1000000 <
      (14 : Real) / 1000000 :=
    div_lt_div_of_pos_right log_oneMillion_lt_fourteen millionPos
  have combined := ratio.trans baseRatio.le
  rw [div_le_iff₀ xPos] at combined
  simpa [mul_comm] using combined

theorem elementary_psi_lower {x : Real} (hx : 1000000 ≤ x) :
    (92 : Real) / 100 * x ≤ Chebyshev.psi x := by
  have source := Chebyshev.psi_lower x (by linarith)
  have logBound := log_le_fourteen_millionths_mul hx
  have aLower := Chebyshev.a_bound.1
  nlinarith

theorem log_sq_le_onehundredninetysix_millionths_mul {x : Real}
    (hx : 1000000 ≤ x) :
    Real.log x ^ 2 ≤ (196 : Real) / 1000000 * x := by
  have ratio := log_div_sqrt_le_fourteen_thousandths hx
  have logNonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have sqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have ratioNonneg : 0 ≤ Real.log x / Real.sqrt x := div_nonneg logNonneg sqrtPos.le
  have ratioSq : (Real.log x / Real.sqrt x) ^ 2 ≤ ((14 : Real) / 1000) ^ 2 :=
    (sq_le_sq₀ ratioNonneg (by norm_num)).2 ratio
  have sqrtSq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  rw [div_pow, sqrtSq] at ratioSq
  have xPos : 0 < x := by linarith
  apply (div_le_iff₀ xPos).mp at ratioSq
  nlinarith

theorem elementary_psi_upper {x : Real} (hx : 1000000 ≤ x) :
    Chebyshev.psi x ≤ (1107 : Real) / 1000 * x := by
  have source := Chebyshev.psi_upper x (by linarith)
  have aUpper := Chebyshev.a_bound.2
  have xPos : 0 < x := by linarith
  have xDivFivePos : 0 < x / 5 := div_pos xPos (by norm_num)
  have logXNonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have logXDivFiveNonneg : 0 ≤ Real.log (x / 5) :=
    Real.log_nonneg (by linarith)
  have logSixGtOne : 1 < Real.log 6 := by
    rw [show (6 : Real) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [LogTables.log_2_gt, LogTables.log_3_gt]
  have logDivFiveLe : Real.log (x / 5) ≤ Real.log x :=
    Real.log_le_log xDivFivePos (by linarith)
  have ratioLe : Real.log (x / 5) / Real.log 6 ≤ Real.log x := by
    apply (div_le_iff₀ (by linarith)).2
    nlinarith [mul_nonneg logXNonneg (show 0 ≤ Real.log 6 - 1 by linarith)]
  have factorNonneg : 0 ≤ 5 * Real.log x - 5 := by
    have oneLtLog : 1 < Real.log x :=
      (Real.lt_log_iff_exp_lt xPos).2 (by linarith [Real.exp_one_lt_d9])
    linarith
  have errorLe :
      (Real.log (x / 5) / Real.log 6) * (5 * Real.log x - 5) ≤
        5 * Real.log x ^ 2 := by
    calc
      _ ≤ Real.log x * (5 * Real.log x - 5) :=
        mul_le_mul_of_nonneg_right ratioLe factorNonneg
      _ ≤ 5 * Real.log x ^ 2 := by nlinarith
  have logSq := log_sq_le_onehundredninetysix_millionths_mul hx
  have aUpper' : Chebyshev.a ≤ (92130 : Real) / 100000 := by
    norm_num at aUpper ⊢
    exact aUpper
  have mainLe : 6 * Chebyshev.a * x / 5 ≤
      6 * ((92130 : Real) / 100000) * x / 5 := by
    gcongr
  have errorFinal :
      (Real.log (x / 5) / Real.log 6) * (5 * Real.log x - 5) ≤
        5 * ((196 : Real) / 1000000 * x) :=
    errorLe.trans (mul_le_mul_of_nonneg_left logSq (by norm_num))
  calc
    Chebyshev.psi x
        ≤ 6 * Chebyshev.a * x / 5 +
            (Real.log (x / 5) / Real.log 6) * (5 * Real.log x - 5) := source
    _ ≤ 6 * ((92130 : Real) / 100000) * x / 5 +
          5 * ((196 : Real) / 1000000 * x) := add_le_add mainLe errorFinal
    _ ≤ (1107 : Real) / 1000 * x := by nlinarith

theorem elementary_theta_upper {x : Real} (hx : 1000000 ≤ x) :
    Chebyshev.theta x ≤ (1107 : Real) / 1000 * x :=
  (Chebyshev.theta_le_psi x).trans (elementary_psi_upper hx)

theorem log_sq_le_sixHundredSeventySix_millionths_mul {x : Real}
    (hx : 250000 ≤ x) :
    Real.log x ^ 2 ≤ (676 : Real) / 1000000 * x := by
  have ratio := log_div_sqrt_le_twentySix_thousandths hx
  have logNonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have sqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have ratioNonneg : 0 ≤ Real.log x / Real.sqrt x := div_nonneg logNonneg sqrtPos.le
  have ratioSq : (Real.log x / Real.sqrt x) ^ 2 ≤ ((26 : Real) / 1000) ^ 2 :=
    (sq_le_sq₀ ratioNonneg (by norm_num)).2 ratio
  have sqrtSq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  rw [div_pow, sqrtSq] at ratioSq
  have xPos : 0 < x := by linarith
  apply (div_le_iff₀ xPos).mp at ratioSq
  nlinarith

theorem elementary_psi_upper_from_250000 {x : Real} (hx : 250000 ≤ x) :
    Chebyshev.psi x ≤ (111 : Real) / 100 * x := by
  have source := Chebyshev.psi_upper x (by linarith)
  have aUpper := Chebyshev.a_bound.2
  have xPos : 0 < x := by linarith
  have xDivFivePos : 0 < x / 5 := div_pos xPos (by norm_num)
  have logXNonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have logXDivFiveNonneg : 0 ≤ Real.log (x / 5) :=
    Real.log_nonneg (by linarith)
  have logSixGtOne : 1 < Real.log 6 := by
    rw [show (6 : Real) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [LogTables.log_2_gt, LogTables.log_3_gt]
  have logDivFiveLe : Real.log (x / 5) ≤ Real.log x :=
    Real.log_le_log xDivFivePos (by linarith)
  have ratioLe : Real.log (x / 5) / Real.log 6 ≤ Real.log x := by
    apply (div_le_iff₀ (by linarith)).2
    nlinarith [mul_nonneg logXNonneg (show 0 ≤ Real.log 6 - 1 by linarith)]
  have factorNonneg : 0 ≤ 5 * Real.log x - 5 := by
    have oneLtLog : 1 < Real.log x :=
      (Real.lt_log_iff_exp_lt xPos).2 (by linarith [Real.exp_one_lt_d9])
    linarith
  have errorLe :
      (Real.log (x / 5) / Real.log 6) * (5 * Real.log x - 5) ≤
        5 * Real.log x ^ 2 := by
    calc
      _ ≤ Real.log x * (5 * Real.log x - 5) :=
        mul_le_mul_of_nonneg_right ratioLe factorNonneg
      _ ≤ 5 * Real.log x ^ 2 := by nlinarith
  have logSq := log_sq_le_sixHundredSeventySix_millionths_mul hx
  have aUpper' : Chebyshev.a ≤ (92130 : Real) / 100000 := by
    norm_num at aUpper ⊢
    exact aUpper
  have mainLe : 6 * Chebyshev.a * x / 5 ≤
      6 * ((92130 : Real) / 100000) * x / 5 := by
    gcongr
  have errorFinal :
      (Real.log (x / 5) / Real.log 6) * (5 * Real.log x - 5) ≤
        5 * ((676 : Real) / 1000000 * x) :=
    errorLe.trans (mul_le_mul_of_nonneg_left logSq (by norm_num))
  calc
    Chebyshev.psi x
        ≤ 6 * Chebyshev.a * x / 5 +
            (Real.log (x / 5) / Real.log 6) * (5 * Real.log x - 5) := source
    _ ≤ 6 * ((92130 : Real) / 100000) * x / 5 +
          5 * ((676 : Real) / 1000000 * x) := add_le_add mainLe errorFinal
    _ ≤ (111 : Real) / 100 * x := by nlinarith

theorem elementary_theta_upper_from_250000 {x : Real} (hx : 250000 ≤ x) :
    Chebyshev.theta x ≤ (111 : Real) / 100 * x :=
  (Chebyshev.theta_le_psi x).trans (elementary_psi_upper_from_250000 hx)

theorem elementary_theta_lower {x : Real} (hx : 1000000 ≤ x) :
    (89 : Real) / 100 * x ≤ Chebyshev.theta x := by
  have psiLower := elementary_psi_lower hx
  have difference := Chebyshev.psi_sub_theta_le (x := x) (by linarith)
  have ratio := log_div_sqrt_le_fourteen_thousandths hx
  have xNonneg : 0 ≤ x := by linarith
  have sqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have correction : 2 * Real.sqrt x * Real.log x ≤ (28 : Real) / 1000 * x := by
    have scaled := mul_le_mul_of_nonneg_left ratio (show 0 ≤ 2 * x by positivity)
    have identity :
        2 * x * (Real.log x / Real.sqrt x) =
          2 * Real.sqrt x * Real.log x := by
      field_simp [sqrtPos.ne']
      rw [Real.sq_sqrt xNonneg]
      ring
    rw [identity] at scaled
    nlinarith
  linarith

end

end PrimeFactorUnimodality
