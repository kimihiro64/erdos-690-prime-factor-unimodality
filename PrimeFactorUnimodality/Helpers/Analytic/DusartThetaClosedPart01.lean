import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.ThetaEndpointRows

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # Checked small theta prefixes

Natural endpoint sums give the strict upper estimate through 29. Monotonicity
and rational logarithm envelopes give the symmetric estimate through seven.
The bounds include prime jumps; no singleton list is treated as real coverage.
-/

namespace PrimeFactorUnimodality

noncomputable section

private theorem theta_nat_lt_id_small {n : Nat} (hn : 2 ≤ n) (hN : n ≤ 29) :
    Chebyshev.theta (n : Real) < n := by
  have hsum := Chebyshev.theta_eq_sum_primesLE_log n
  interval_cases n <;>
    norm_num [Nat.primesLE, Nat.primesBelow, Finset.sum_filter,
      Finset.sum_range_succ] at hsum ⊢ <;>
    nlinarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_lt,
      LogTables.log_7_lt, LogTables.log_11_lt, LogTables.log_13_lt,
      LogTables.log_17_lt, LogTables.log_19_lt, LogTables.log_23_lt,
      LogTables.log_29_lt]

theorem wangCrapis_strictThetaPrefix_twenty_nine :
    HasStrictThetaUpperBelow (29 : Real) := by
  intro x hx hX
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    exact hx
  · have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor (le_of_not_gt hsmall)
    have hN : ⌊x⌋₊ ≤ 29 := Nat.floor_le_of_le hX
    rw [Chebyshev.theta_eq_theta_coe_floor]
    exact (theta_nat_lt_id_small hn hN).trans_le (Nat.floor_le hx.le)

theorem wangCrapis_thetaBoundsBelow_7 :
    HasDusartSymmetricThetaBoundsBelow (7 : Real) := by
  have strict : HasStrictThetaUpperBelow (7 : Real) := by
    intro x hx hX
    exact wangCrapis_strictThetaPrefix_twenty_nine x hx (by linarith)
  constructor
  · intro x hx hX
    have hu := strict x hx hX
    have : 0 < x / (36260 : Real) := by positivity
    linarith
  · intro x hx hX
    by_cases hx3 : x ≤ 3
    · exact dusartThetaBoundsBelow_three.2 x hx hx3
    have hxpos : 0 < x := by linarith
    have hu : Chebyshev.theta x ≤ x := (strict x hxpos hX).le
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hu)]
    suffices h : x - Chebyshev.theta x <
        (12323 / 10000 : Real) * x / Real.log x by linarith
    apply (lt_div_iff₀ hlogpos).mpr
    by_cases hx5 : x ≤ 5
    · have hsum := Chebyshev.theta_eq_sum_primesLE_log 3
      norm_num [Nat.primesLE, Nat.primesBelow, Finset.sum_filter,
        Finset.sum_range_succ] at hsum
      have hlo : (179 : Real) / 100 < Chebyshev.theta x := by
        have hm := Chebyshev.theta_mono (show (3 : Real) ≤ x by linarith)
        nlinarith [LogTables.log_2_gt, LogTables.log_3_gt]
      have hl : Real.log x ≤ (161 : Real) / 100 := by
        have := Real.log_le_log hxpos hx5
        linarith [LogTables.log_5_lt]
      have hm := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hu)
      have he : (x - Chebyshev.theta x) * ((161 : Real) / 100) <
          (12323 / 10000 : Real) * x := by nlinarith
      exact hm.trans_lt he
    · have hsum := Chebyshev.theta_eq_sum_primesLE_log 5
      norm_num [Nat.primesLE, Nat.primesBelow, Finset.sum_filter,
        Finset.sum_range_succ] at hsum
      have hlo : (34 : Real) / 10 < Chebyshev.theta x := by
        have hm := Chebyshev.theta_mono (show (5 : Real) ≤ x by linarith)
        nlinarith [LogTables.log_2_gt, LogTables.log_3_gt, LogTables.log_5_gt]
      have hl : Real.log x ≤ (1947 : Real) / 1000 := by
        have := Real.log_le_log hxpos hX
        linarith [LogTables.log_7_lt]
      have hm := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hu)
      have he : (x - Chebyshev.theta x) * ((1947 : Real) / 1000) <
          (12323 / 10000 : Real) * x := by nlinarith
      exact hm.trans_lt he

theorem wangCrapis_thetaPrefix :
    HasDusartSymmetricThetaBoundsBelow (2 : Real) :=
  hasDusartSymmetricThetaBoundsBelow_mono (by norm_num) dusartThetaBoundsBelow_three

theorem wangCrapis_thetaPrefix_three :
    HasDusartSymmetricThetaBoundsBelow (3 : Real) :=
  dusartThetaBoundsBelow_three

theorem wangCrapis_thetaBounds_lower_2_3
    {x : Real} (hx : 2 < x) (hx3 : x ≤ 3) :
    x * (1 - (12323 / 10000 : Real) / Real.log x) <
      Chebyshev.theta x := by
  have h := (abs_lt.mp (dusartThetaBoundsBelow_three.2 x hx hx3)).1
  have h' : x - (12323 / 10000 : Real) * x / Real.log x < Chebyshev.theta x := by
    linarith
  convert h' using 1 <;> ring

theorem wangCrapis_thetaBounds_upper_0_3
    {x : Real} (hx : 0 < x) (hx3 : x ≤ 3) :
    Chebyshev.theta x - x < x / 36260 :=
  dusartThetaBoundsBelow_three.1 x hx hx3

theorem wangCrapis_thetaBoundsBelow_3 :
    HasDusartSymmetricThetaBoundsBelow (3 : Real) :=
  dusartThetaBoundsBelow_three

theorem wangCrapis_thetaBoundsBelow_4 :
    HasDusartSymmetricThetaBoundsBelow (4 : Real) :=
  hasDusartSymmetricThetaBoundsBelow_mono (by norm_num) wangCrapis_thetaBoundsBelow_7

theorem wangCrapis_thetaBoundsBelow_5 :
    HasDusartSymmetricThetaBoundsBelow (5 : Real) :=
  hasDusartSymmetricThetaBoundsBelow_mono (by norm_num) wangCrapis_thetaBoundsBelow_7

theorem wangCrapis_thetaBoundsBelow_6 :
    HasDusartSymmetricThetaBoundsBelow (6 : Real) :=
  hasDusartSymmetricThetaBoundsBelow_mono (by norm_num) wangCrapis_thetaBoundsBelow_7

theorem wangCrapis_theta_lower_error_below_seven
    {x : Real} (hx : 2 < x) (hX : x ≤ 7) :
    |Chebyshev.theta x - x| < (12323 / 10000 : Real) * x / Real.log x :=
  wangCrapis_thetaBoundsBelow_7.2 x hx hX

theorem wangCrapis_theta_lower_error_below_six
    {x : Real} (hx : 2 < x) (hX : x ≤ 6) :
    |Chebyshev.theta x - x| < (12323 / 10000 : Real) * x / Real.log x :=
  wangCrapis_thetaBoundsBelow_6.2 x hx hX

theorem wangCrapis_strictThetaPrefix_three :
    HasStrictThetaUpperBelow (3 : Real) := by
  intro x hx hX
  exact wangCrapis_strictThetaPrefix_twenty_nine x hx (by linarith)

theorem wangCrapis_strictThetaPrefix_seven :
    HasStrictThetaUpperBelow (7 : Real) := by
  intro x hx hX
  exact wangCrapis_strictThetaPrefix_twenty_nine x hx (by linarith)

theorem wangCrapis_strictThetaPrefix_eleven :
    HasStrictThetaUpperBelow (11 : Real) := by
  intro x hx hX
  exact wangCrapis_strictThetaPrefix_twenty_nine x hx (by linarith)

theorem wangCrapis_strictThetaPrefix_thirteen :
    HasStrictThetaUpperBelow (13 : Real) := by
  intro x hx hX
  exact wangCrapis_strictThetaPrefix_twenty_nine x hx (by linarith)

theorem wangCrapis_strictThetaPrefix_nineteen :
    HasStrictThetaUpperBelow (19 : Real) := by
  intro x hx hX
  exact wangCrapis_strictThetaPrefix_twenty_nine x hx (by linarith)

end

end PrimeFactorUnimodality
