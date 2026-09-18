import PrimeFactorUnimodality.Helpers.Analytic.MertensProvider
import PrimeFactorUnimodality.Proof.LargeRange.TailAscentBounds

set_option autoImplicit false

/-! # Uniform-tail bounds from the proved Mertens estimate

Beyond the record range, the coarser but fully proved `O(1 / log x)`
reciprocal-prime estimate is already strong enough for the descent.  This file
keeps that numerical argument separate from the sharper conditional Dusart
interface.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem log_nat_gt_31_div_2 {r : Nat} (hr : 7300000 ≤ r) :
    (31 : Real) / 2 < Real.log r := by
  have powerLe : 4 * 3 ^ (13 : Nat) ≤ r := by norm_num at hr ⊢; omega
  have castPower' : (4 : Real) * 3 ^ (13 : Nat) ≤ r := by exact_mod_cast powerLe
  have logged := Real.log_le_log (by positivity) castPower'
  rw [Real.log_mul (by norm_num) (by positivity), show (4 : Real) = 2 ^ (2 : Nat) by norm_num,
    Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private theorem log_31_div_2_lt_11_div_4 :
    Real.log ((31 : Real) / 2) < (11 : Real) / 4 := by
  have powerLt : ((31 : Real) / 2) ^ 4 < 3 ^ (10 : Nat) := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_three_lt_d9]

private theorem closed_mertens_descent_expression {r : Nat}
    (hr : 7300000 ≤ r) :
    (54 / 100 : Real) * Real.log r +
        (181 / 10 : Real) / Real.log r <
      Real.log r - 2 * Real.log (Real.log r) - 5 / 12 := by
  let v : Real := Real.log r
  let v₀ : Real := 31 / 2
  have vLower : v₀ < v := by
    simpa only [v, v₀] using log_nat_gt_31_div_2 hr
  have v₀Pos : 0 < v₀ := by norm_num [v₀]
  have vPos : 0 < v := v₀Pos.trans vLower
  have ratioPos : 0 < v / v₀ := by positivity
  have logDecomposition : Real.log v =
      Real.log v₀ + Real.log (v / v₀) := by
    rw [← Real.log_mul v₀Pos.ne' ratioPos.ne']
    congr 2
    field_simp
  have ratioLog := Real.log_le_sub_one_of_pos ratioPos
  have baseLog : Real.log v₀ < (11 : Real) / 4 := by
    simpa only [v₀] using log_31_div_2_lt_11_div_4
  have logVUpper : Real.log v <
      (11 : Real) / 4 + (v / v₀ - 1) := by
    rw [logDecomposition]
    linarith
  have inverseUpper : (1 : Real) / v < 1 / v₀ := by
    exact one_div_lt_one_div_of_lt v₀Pos vLower
  have logVLinear : Real.log v <
      (7 : Real) / 4 + (2 / 31 : Real) * v := by
    dsimp only [v₀] at logVUpper
    convert logVUpper using 1 <;> ring
  have reciprocalUpper : (181 / 10 : Real) / v < 181 / 155 := by
    calc
      (181 / 10 : Real) / v = (181 / 10) * (1 / v) := by ring
      _ < (181 / 10) * (1 / v₀) :=
        mul_lt_mul_of_pos_left inverseUpper (by norm_num)
      _ = 181 / 155 := by norm_num [v₀]
  dsimp only [v₀] at vLower
  dsimp only [v] at vLower logVLinear reciprocalUpper ⊢
  nlinarith

theorem tail_descent_bracket_lower_closed_mertens
    (thetaBounds : HasDusartThetaBounds)
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    {r q : Nat} (hr : 7300000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    (54 / 100 : Real) * Real.log r <
      Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
        mertensErrorConstant / Real.log ((primorial q : Nat) : Real) -
        mertensErrorConstant /
          Real.log ((primeAt (r - 1) - 1 : Nat) : Real) := by
  let P : Nat := primorial q
  let X : Nat := primeAt (r - 1) - 1
  have hrBase : 38000 ≤ r := by omega
  have shell := tail_descent_loglog_shell_lower
    thetaBounds primeCountingBounds hrBase scaleLtQ
  have logRPos : 0 < Real.log r :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have logRLtP : Real.log r < Real.log P := by
    simpa only [P] using
      tail_log_r_lt_log_primorial thetaBounds hrBase scaleLtQ
  have rLeX : r ≤ X := by
    dsimp only [X, primeAt]
    have lower := Nat.add_two_le_nth_prime (r - 1)
    omega
  have logRLeX : Real.log r ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (show 0 < r by omega))
      (by exact_mod_cast rLeX)
  have invP : (1 : Real) / Real.log P ≤ 1 / Real.log r :=
    one_div_le_one_div_of_le logRPos logRLtP.le
  have invX : (1 : Real) / Real.log X ≤ 1 / Real.log r :=
    one_div_le_one_div_of_le logRPos logRLeX
  have constantNonneg : 0 ≤ mertensErrorConstant :=
    mertensErrorConstant_nonneg
  have errorP : mertensErrorConstant / Real.log P ≤
      (901 / 100 : Real) / Real.log r := by
    have invP' : (Real.log P)⁻¹ ≤ (Real.log r)⁻¹ := by
      simpa only [one_div] using invP
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left invP' constantNonneg).trans
      (mul_le_mul_of_nonneg_right mertensErrorConstant_lt_901_div_100.le
        (inv_nonneg.mpr logRPos.le))
  have errorX : mertensErrorConstant / Real.log X ≤
      (901 / 100 : Real) / Real.log r := by
    have invX' : (Real.log X)⁻¹ ≤ (Real.log r)⁻¹ := by
      simpa only [one_div] using invX
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left invX' constantNonneg).trans
      (mul_le_mul_of_nonneg_right mertensErrorConstant_lt_901_div_100.le
        (inv_nonneg.mpr logRPos.le))
  have errors : mertensErrorConstant / Real.log P +
      mertensErrorConstant / Real.log X <
        (181 / 10 : Real) / Real.log r := by
    have slack : (901 / 50 : Real) < 181 / 10 := by norm_num
    have invPos : 0 < (1 : Real) / Real.log r := by positivity
    have scaledSlack := mul_lt_mul_of_pos_right slack invPos
    calc
      mertensErrorConstant / Real.log P +
          mertensErrorConstant / Real.log X ≤
        (901 / 100 : Real) / Real.log r +
          (901 / 100 : Real) / Real.log r := add_le_add errorP errorX
      _ = (901 / 50 : Real) * (1 / Real.log r) := by ring
      _ < (181 / 10 : Real) * (1 / Real.log r) := scaledSlack
      _ = (181 / 10 : Real) / Real.log r := by ring
  have numeric := closed_mertens_descent_expression hr
  dsimp only [P, X] at shell errorP errorX errors ⊢
  nlinarith

theorem tail_descent_numeric_closed_mertens
    (thetaBounds : HasDusartThetaBounds)
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    {r qPrev q : Nat} (hr : 7300000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (scalePrev : (491 / 500 : Real) * r / Real.log r <
      (2519 / 2500 : Real) * qPrev) :
    (r : Real) < ((2 * qPrev + 1 : Nat) : Real) *
      (Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
        mertensErrorConstant / Real.log ((primorial q : Nat) : Real) -
        mertensErrorConstant /
          Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) := by
  let B : Real :=
    Real.log (Real.log ((primorial q : Nat) : Real)) -
      Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
      mertensErrorConstant / Real.log ((primorial q : Nat) : Real) -
      mertensErrorConstant /
        Real.log ((primeAt (r - 1) - 1 : Nat) : Real)
  have bracket : (54 / 100 : Real) * Real.log r < B := by
    simpa only [B] using tail_descent_bracket_lower_closed_mertens
      thetaBounds primeCountingBounds hr scaleLtQ
  have logRPos : 0 < Real.log r :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have scaleCross : (491 / 500 : Real) * r <
      (2519 / 2500 : Real) * qPrev * Real.log r :=
    (div_lt_iff₀ logRPos).mp (by convert scalePrev using 1 <;> ring)
  have coefficient : (2519 / 2500 : Real) * (500 / 491 : Real) <
      2 * (54 / 100 : Real) := by norm_num
  have qPrevPos : (0 : Real) < qPrev := by
    have scalePos : (0 : Real) <
        (491 / 500 : Real) * r / Real.log r := by positivity
    nlinarith [scalePrev]
  have core : (r : Real) <
      (2 * qPrev : Nat) * ((54 / 100 : Real) * Real.log r) := by
    push_cast
    nlinarith
  have raised := mul_lt_mul_of_pos_left bracket
    (show (0 : Real) < 2 * qPrev by positivity)
  have bracketPos : (0 : Real) < B := by
    have : (0 : Real) < (54 / 100 : Real) * Real.log r := by positivity
    linarith
  dsimp only [B] at raised ⊢
  push_cast at raised ⊢
  nlinarith

private theorem log_log_nat_gt_27_div_10 {r : Nat} (hr : 7300000 ≤ r) :
    (27 : Real) / 10 < Real.log (Real.log r) := by
  have logRLower := log_nat_gt_31_div_2 hr
  have fifteenLt : (15 : Real) < Real.log r := by linarith
  have logFifteen : (27 : Real) / 10 < Real.log 15 := by
    rw [show (15 : Real) = 3 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_three_gt_d9, Real.log_five_gt_d9]
  exact logFifteen.trans_le
    (Real.log_le_log (by norm_num) fifteenLt.le)

private theorem tail_closed_mertens_ascent_error_small
    (thetaBounds : HasDusartThetaBounds)
    {r q : Nat} (hr : 7300000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    mertensErrorConstant /
        Real.log ((9 * primorial q : Nat) : Real) < (1 : Real) / 300 := by
  have hrBase : 38000 ≤ r := by omega
  have scaleLarge := tailScale_gt_3500 hrBase
  have logPLower := tail_log_primorial_lower thetaBounds hrBase scaleLtQ
  have logP2900 : (2900 : Real) < Real.log (primorial q) := by
    nlinarith
  have pPos : (0 : Real) < primorial q := by
    exact_mod_cast primorial_pos q
  have logPLe : Real.log (primorial q) ≤
      Real.log ((9 * primorial q : Nat) : Real) := by
    apply Real.log_le_log pPos
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have logN2900 : (2900 : Real) <
      Real.log ((9 * primorial q : Nat) : Real) := logP2900.trans_le logPLe
  have logNPos : (0 : Real) <
      Real.log ((9 * primorial q : Nat) : Real) := by linarith
  rw [div_lt_iff₀ logNPos]
  nlinarith [mertensErrorConstant_lt_901_div_100]

theorem tail_ascent_bracket_lt_log_closed_mertens
    (thetaBounds : HasDusartThetaBounds)
    {r q : Nat} (hr : 7300000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
        mertensErrorConstant /
          Real.log ((9 * primorial q : Nat) : Real) + 1 <
      Real.log r := by
  have ratio := tail_loglog_nine_primorial_lt_log_ratio
    thetaBounds (show 38000 ≤ r by omega) scaleLtQ qUpper
  have logLogLarge := log_log_nat_gt_27_div_10 hr
  have errorSmall := tail_closed_mertens_ascent_error_small
    thetaBounds hr scaleLtQ
  nlinarith

theorem tail_ascent_numeric_closed_mertens
    (thetaBounds : HasDusartThetaBounds)
    {r q : Nat} (hr : 7300000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    (tailGapBound q : Real) *
        (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
          mertensErrorConstant /
            Real.log ((9 * primorial q : Nat) : Real) + 1) <
      (r : Real) := by
  have hrBase : 38000 ≤ r := by omega
  have gap := tail_gapBound_lt_r_div_log hrBase scaleLtQ qUpper
  have bracket := tail_ascent_bracket_lt_log_closed_mertens
    thetaBounds hr scaleLtQ qUpper
  have gapPos : (0 : Real) < tailGapBound q := by
    exact_mod_cast tailGapBound_pos q
  have bracketPos : (0 : Real) <
      Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
        mertensErrorConstant /
          Real.log ((9 * primorial q : Nat) : Real) + 1 := by
    have qLarge := tail_selected_prime_ge_3501 hrBase scaleLtQ
    have logNGtOne : (1 : Real) <
        Real.log ((9 * primorial q : Nat) : Real) := by
      have base : primorial 13 ≤ primorial q := primorial_mono (by omega)
      have value : primorial 13 = 30030 := by decide
      rw [value] at base
      apply (Real.lt_log_iff_exp_lt (by positivity)).2
      have expOne : Real.exp 1 < 3 :=
        Real.exp_one_lt_d9.trans (by norm_num)
      exact expOne.trans_le (by exact_mod_cast (show 3 ≤ 9 * primorial q by
        omega))
    have logLogPos : (0 : Real) <
        Real.log (Real.log ((9 * primorial q : Nat) : Real)) :=
      Real.log_pos logNGtOne
    have errorNonneg : 0 ≤ mertensErrorConstant /
        Real.log ((9 * primorial q : Nat) : Real) := by
      apply div_nonneg mertensErrorConstant_nonneg
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 9 * primorial q by
        have := primorial_pos q
        omega)
    nlinarith
  have logRPos : 0 < Real.log r :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  calc
    (tailGapBound q : Real) *
          (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
            mertensErrorConstant /
              Real.log ((9 * primorial q : Nat) : Real) + 1) <
        (tailGapBound q : Real) * Real.log r :=
      mul_lt_mul_of_pos_left bracket gapPos
    _ < ((r : Real) / Real.log r) * Real.log r :=
      mul_lt_mul_of_pos_right gap logRPos
    _ = r := by field_simp

end

end PrimeFactorUnimodality
