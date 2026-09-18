import PrimeFactorUnimodality.Proof.LargeRange.TailWeightBounds

set_option autoImplicit false

/-! # Ascent-weight numerics for the uniform tail -/

namespace PrimeFactorUnimodality

noncomputable section

theorem tailGapBound_le_sharp {q : Nat} (hq : 3501 ≤ q) :
    (tailGapBound q : Real) ≤ (10103 / 10000 : Real) * q := by
  have quotientBound : ((q / 100 : Nat) : Real) ≤ (q : Real) / 100 :=
    Nat.cast_div_le
  have unitBound : (1 : Real) ≤ (3 / 10000 : Real) * q := by
    have h : (10000 : Real) ≤ 3 * q := by
      exact_mod_cast (show (10000 : Nat) ≤ 3 * q by omega)
    nlinarith
  unfold tailGapBound
  push_cast
  nlinarith

theorem tail_gapBound_lt_r_div_log
    {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    (tailGapBound q : Real) < (r : Real) / Real.log r := by
  have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
  have gapLe := tailGapBound_le_sharp qLarge
  have factorPos : (0 : Real) < 10103 / 10000 := by norm_num
  have scaled := mul_lt_mul_of_pos_left qUpper factorPos
  have coefficient :
      (10103 / 10000 : Real) * (2519 / 2500 : Real) * (491 / 500 : Real) < 1 := by
    norm_num
  have ratioPos : (0 : Real) < (r : Real) / Real.log r := by
    have : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
    positivity
  calc
    (tailGapBound q : Real) ≤ (10103 / 10000 : Real) * q := gapLe
    _ < (10103 / 10000 : Real) *
        ((2519 / 2500 : Real) * ((491 / 500 : Real) * r / Real.log r)) := scaled
    _ < (r : Real) / Real.log r := by
      convert mul_lt_mul_of_pos_right coefficient ratioPos using 1 <;> ring

private theorem log_log_r_gt_two {r : Nat} (hr : 38000 ≤ r) :
    (2 : Real) < Real.log (Real.log r) := by
  have logRLower := log_nat_gt_1054_div_100 hr
  have nineLt : (9 : Real) < Real.log r := by linarith
  have logNine : (2 : Real) < Real.log 9 := by
    rw [show (9 : Real) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_three_gt_d9]
  exact logNine.trans_le (Real.log_le_log (by norm_num) nineLt.le)

/-- The core logarithmic comparison behind the ascent estimate, separated
from the choice of reciprocal-prime error term. -/
theorem tail_loglog_nine_primorial_lt_log_ratio
    (thetaBounds : HasDusartThetaBounds)
    {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    Real.log (Real.log ((9 * primorial q : Nat) : Real)) <
      Real.log r - Real.log (Real.log r) := by
  let N : Nat := 9 * primorial q
  have logNUpper := tail_log_nine_primorial_upper
    thetaBounds hr scaleLtQ qUpper
  have logRPos : 0 < Real.log r :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have coefficient : (101 / 100 : Real) * (491 / 500 : Real) < 1 := by
    norm_num
  have ratioPos : (0 : Real) < (r : Real) / Real.log r := by positivity
  have logNLtRatio : Real.log N < (r : Real) / Real.log r := by
    have scaled := mul_lt_mul_of_pos_right coefficient ratioPos
    have scaled' : (101 / 100 : Real) *
        ((491 / 500 : Real) * r / Real.log r) <
          (r : Real) / Real.log r := by
      convert scaled using 1 <;> ring
    dsimp only [N]
    push_cast
    exact logNUpper.trans scaled'
  have logNPos : 0 < Real.log N := by
    have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
    have nLarge : 1 < N := by
      dsimp only [N]
      have : 0 < primorial q := primorial_pos q
      omega
    exact Real.log_pos (by exact_mod_cast nLarge)
  have ratioLog :
      Real.log (Real.log N) < Real.log ((r : Real) / Real.log r) :=
    Real.log_lt_log logNPos logNLtRatio
  have logRatio : Real.log ((r : Real) / Real.log r) =
      Real.log r - Real.log (Real.log r) :=
    Real.log_div (by positivity) logRPos.ne'
  rw [logRatio] at ratioLog
  simpa only [N] using ratioLog

theorem tail_ascent_bracket_lt_log
    (thetaBounds : HasDusartThetaBounds)
    {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
        dusartReciprocalError (((9 * primorial q : Nat) : Real)) + 1 <
      Real.log r := by
  let N : Nat := 9 * primorial q
  have logNUpper := tail_log_nine_primorial_upper thetaBounds hr scaleLtQ qUpper
  have logRPos : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have coefficient : (101 / 100 : Real) * (491 / 500 : Real) < 1 := by norm_num
  have ratioPos : (0 : Real) < (r : Real) / Real.log r := by positivity
  have logNLtRatio : Real.log N < (r : Real) / Real.log r := by
    have scaled := mul_lt_mul_of_pos_right coefficient ratioPos
    have scaled' : (101 / 100 : Real) *
        ((491 / 500 : Real) * r / Real.log r) < (r : Real) / Real.log r := by
      convert scaled using 1 <;> ring
    dsimp only [N]
    push_cast
    exact logNUpper.trans scaled'
  have logNPos : 0 < Real.log N := by
    have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
    have nLarge : 1 < N := by
      dsimp only [N]
      have : 0 < primorial q := primorial_pos q
      omega
    exact Real.log_pos (by exact_mod_cast nLarge)
  have ratioLog :
      Real.log (Real.log N) < Real.log ((r : Real) / Real.log r) :=
    Real.log_lt_log logNPos logNLtRatio
  have logRatio : Real.log ((r : Real) / Real.log r) =
      Real.log r - Real.log (Real.log r) :=
    Real.log_div (by positivity) logRPos.ne'
  rw [logRatio] at ratioLog
  have nThreshold : 10372 ≤ N := by
    have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
    have base : primorial 13 ≤ primorial q := primorial_mono (by omega)
    have value : primorial 13 = 30030 := by decide
    rw [value] at base
    dsimp only [N]
    omega
  have errorSmall := dusartReciprocalError_lt_one_div_500 nThreshold
  have logLogLarge := log_log_r_gt_two hr
  dsimp only [N] at ratioLog errorSmall ⊢
  nlinarith

theorem tail_ascent_numeric
    (thetaBounds : HasDusartThetaBounds)
    {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    (tailGapBound q : Real) *
        (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
          dusartReciprocalError (((9 * primorial q : Nat) : Real)) + 1) <
      (r : Real) := by
  have gap := tail_gapBound_lt_r_div_log hr scaleLtQ qUpper
  have bracket := tail_ascent_bracket_lt_log thetaBounds hr scaleLtQ qUpper
  have gapPos : (0 : Real) < tailGapBound q := by
    exact_mod_cast tailGapBound_pos q
  have bracketPos : (0 : Real) <
      Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
        dusartReciprocalError (((9 * primorial q : Nat) : Real)) + 1 := by
    have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
    have logN : (1 : Real) < Real.log ((9 * primorial q : Nat) : Real) := by
      have base : primorial 13 ≤ primorial q := primorial_mono (by omega)
      have value : primorial 13 = 30030 := by decide
      rw [value] at base
      have nLarge : Real.exp 1 < ((9 * primorial q : Nat) : Real) := by
        have expOne : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        exact expOne.trans_le (by exact_mod_cast (show 3 ≤ 9 * primorial q by
          have := primorial_pos q
          omega))
      exact (Real.lt_log_iff_exp_lt (by positivity)).2 nLarge
    have : 0 < Real.log (Real.log ((9 * primorial q : Nat) : Real)) :=
      Real.log_pos logN
    unfold dusartReciprocalError
    positivity
  have logRPos : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  calc
    (tailGapBound q : Real) *
          (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
            dusartReciprocalError (((9 * primorial q : Nat) : Real)) + 1) <
        (tailGapBound q : Real) * Real.log r :=
      mul_lt_mul_of_pos_left bracket gapPos
    _ < ((r : Real) / Real.log r) * Real.log r :=
      mul_lt_mul_of_pos_right gap logRPos
    _ = r := by field_simp

end

end PrimeFactorUnimodality
