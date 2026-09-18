import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Proof.LargeRange.TailStructuralBounds

set_option autoImplicit false

/-! # Primorial bounds for the optimized uniform tail

This file converts the rational localization of the selected prime into the
two logarithmic estimates used by the CRT construction.  All deep analytic
content remains isolated in `HasDusartThetaBounds`.
-/

namespace PrimeFactorUnimodality

noncomputable section

private theorem tail_log_selected_gt {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    (81 : Real) / 10 < Real.log q := by
  have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
  exact log_gt_81_div_10_of_3301_le (by exact_mod_cast (show 3301 ≤ q by omega))

/-- At the selected prime, the relative error in Dusart's lower theta bound
is less than `4/25`. -/
theorem tail_thetaRelativeError_lt {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    (12323 / 10000 : Real) / Real.log q < 4 / 25 := by
  have logLower := tail_log_selected_gt hr scaleLtQ
  have logPos : 0 < Real.log q := by linarith
  rw [div_lt_iff₀ logPos]
  nlinarith

private theorem log_3501_gt : (407 : Real) / 50 < Real.log 3501 := by
  have powerLt : (2 : Real) ^ 7 * 3 ^ 3 < 3501 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at logged
  rw [Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem tail_thetaRelativeError_lt_sharp {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    (12323 / 10000 : Real) / Real.log q < 19 / 125 := by
  have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
  have logLower : (407 : Real) / 50 < Real.log q :=
    log_3501_gt.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast qLarge))
  have logPos : 0 < Real.log q := by linarith
  rw [div_lt_iff₀ logPos]
  nlinarith

/-- The selected primorial has logarithm at least `0.84` times the tail
scale.  The deliberately rounded constant leaves room for later algebra. -/
theorem tail_log_primorial_lower
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    (21 / 25 : Real) * ((491 / 500 : Real) * r / Real.log r) <
      Real.log (primorial q) := by
  have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
  have qGtTwo : 2 < q := by omega
  have errorLt := tail_thetaRelativeError_lt hr scaleLtQ
  have factorLower : (21 / 25 : Real) <
      1 - (12323 / 10000 : Real) / Real.log q := by
    linarith
  have scalePos : 0 < (491 / 500 : Real) * r / Real.log r := by
    linarith [tailScale_gt_3500 hr]
  have qPosReal : (0 : Real) < q := by positivity
  calc
    (21 / 25 : Real) * ((491 / 500 : Real) * r / Real.log r) <
        (21 / 25 : Real) * q :=
      mul_lt_mul_of_pos_left scaleLtQ (by norm_num)
    _ < (q : Real) *
        (1 - (12323 / 10000 : Real) / Real.log q) := by
      rw [mul_comm (21 / 25 : Real) q]
      exact mul_lt_mul_of_pos_left factorLower qPosReal
    _ < Real.log (primorial q) :=
      dusart_lower_lt_log_primorial thetaBounds q qGtTwo

theorem tail_log_primorial_lower_sharp
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    (106 / 125 : Real) * ((491 / 500 : Real) * r / Real.log r) <
      Real.log (primorial q) := by
  have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
  have qGtTwo : 2 < q := by omega
  have errorLt := tail_thetaRelativeError_lt_sharp hr scaleLtQ
  have factorLower : (106 / 125 : Real) <
      1 - (12323 / 10000 : Real) / Real.log q := by
    linarith
  have qPosReal : (0 : Real) < q := by positivity
  calc
    (106 / 125 : Real) * ((491 / 500 : Real) * r / Real.log r) <
        (106 / 125 : Real) * q :=
      mul_lt_mul_of_pos_left scaleLtQ (by norm_num)
    _ < (q : Real) *
        (1 - (12323 / 10000 : Real) / Real.log q) := by
      rw [mul_comm (106 / 125 : Real) q]
      exact mul_lt_mul_of_pos_left factorLower qPosReal
    _ < Real.log (primorial q) :=
      dusart_lower_lt_log_primorial thetaBounds q qGtTwo

private theorem log_eight_lt_21_div_10 :
    Real.log 8 < (21 : Real) / 10 := by
  rw [show (8 : Real) = 2 ^ 3 by norm_num, Real.log_pow]
  nlinarith [Real.log_two_lt_d9]

/-- If the selected prime is within the rationalized short interval, then
`log (8P)` is below `1.009` times the tail scale. -/
theorem tail_log_eight_primorial_upper
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    Real.log (8 * primorial q) <
      (101 / 100 : Real) * ((491 / 500 : Real) * r / Real.log r) := by
  let x : Real := (491 / 500 : Real) * r / Real.log r
  have xLower : (3500 : Real) < x := by
    simpa only [x] using tailScale_gt_3500 hr
  have xPos : 0 < x := by linarith
  have qPos : 0 < q := by
    have : (0 : Real) < q := xPos.trans (by simpa only [x] using scaleLtQ)
    exact_mod_cast this
  have thetaUpper := log_eight_mul_primorial_lt_of_dusart thetaBounds q qPos
  have qTerm :
      (q : Real) * (1 + 1 / 36260) <
        ((2519 / 2500 : Real) * x) * (1 + 1 / 36260) := by
    exact mul_lt_mul_of_pos_right (by simpa only [x] using qUpper) (by norm_num)
  have logEightSmall : Real.log 8 < (1 / 1000 : Real) * x := by
    have : (21 / 10 : Real) < (1 / 1000 : Real) * x := by
      nlinarith
    exact log_eight_lt_21_div_10.trans this
  dsimp only [x] at qTerm logEightSmall ⊢
  nlinarith

private theorem log_nine_lt_22_div_10 :
    Real.log 9 < (22 : Real) / 10 := by
  rw [show (9 : Real) = 3 ^ 2 by norm_num, Real.log_pow]
  nlinarith [Real.log_three_lt_d9]

/-- The slightly wider `(4P,9P]` average-gap shell has the same convenient
`1.01` logarithmic upper bound. -/
theorem tail_log_nine_primorial_upper
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    Real.log (9 * primorial q) <
      (101 / 100 : Real) * ((491 / 500 : Real) * r / Real.log r) := by
  let x : Real := (491 / 500 : Real) * r / Real.log r
  have xLower : (3500 : Real) < x := by
    simpa only [x] using tailScale_gt_3500 hr
  have xPos : 0 < x := by linarith
  have qPos : 0 < q := by
    have : (0 : Real) < q := xPos.trans (by simpa only [x] using scaleLtQ)
    exact_mod_cast this
  have thetaUpper : Real.log (9 * primorial q) <
      Real.log 9 + (q : Real) * (1 + 1 / 36260) := by
    calc
      Real.log (9 * primorial q) = Real.log 9 + Real.log (primorial q) :=
        log_mul_primorial 9 q (by omega)
      _ < Real.log 9 + (q : Real) * (1 + 1 / 36260) :=
        add_lt_add_right (log_primorial_lt_of_dusart thetaBounds q qPos) _
  have qTerm :
      (q : Real) * (1 + 1 / 36260) <
        ((2519 / 2500 : Real) * x) * (1 + 1 / 36260) := by
    exact mul_lt_mul_of_pos_right (by simpa only [x] using qUpper) (by norm_num)
  have logNineSmall : Real.log 9 < (7 / 10000 : Real) * x := by
    have : (22 / 10 : Real) < (7 / 10000 : Real) * x := by
      nlinarith
    exact log_nine_lt_22_div_10.trans this
  dsimp only [x] at qTerm logNineSmall ⊢
  nlinarith

theorem tail_log_nine_primorial_lt_gapBound
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    Real.log (9 * primorial q) < tailGapBound q := by
  have logUpper := tail_log_nine_primorial_upper thetaBounds hr scaleLtQ qUpper
  have boundLower := tailGapBound_gt_onePointZeroOne q
  have scaleToQ :
      (101 / 100 : Real) * ((491 / 500 : Real) * r / Real.log r) <
        (101 / 100 : Real) * q :=
    mul_lt_mul_of_pos_left scaleLtQ (by norm_num)
  exact logUpper.trans (scaleToQ.trans boundLower)

end

end PrimeFactorUnimodality
