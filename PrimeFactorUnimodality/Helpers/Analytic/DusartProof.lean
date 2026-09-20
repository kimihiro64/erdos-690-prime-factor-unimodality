import PrimeFactorUnimodality.Helpers.Analytic.RelativePsiTheta
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryChebyshevConsequences
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

theorem exp_twentyEight_lt_dusart_endpoint :
    Real.exp 28 < (1446257067000 : Real) := by
  rw [show (28 : Real) = (28 : Nat) * 1 by norm_num,
    Real.exp_nat_mul]
  have hpow : (Real.exp 1) ^ (28 : Nat) <
      (2.7182818286 : Real) ^ (28 : Nat) := by
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9
      (Real.exp_pos 1).le (by norm_num)
  have hnum : (2.7182818286 : Real) ^ (28 : Nat) <
      (1446257067000 : Real) := by norm_num
  exact hpow.trans hnum

/-! The numerical tail step used in Dusart's theta estimate. -/
theorem theta_le_one_plus_dusart_error_of_psi_upper_and_gap
    {x : Real}
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x ≤
      (100002841 : Real) / 100000000 * x -
        (9999 : Real) / 10000 * Real.sqrt x := by
  linarith

theorem dusart_gap_from_theta_root_lower
    {x : Real} (hx : 2 ≤ x)
    (hroot : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.theta (x ^ (1 / 2 : Real))) :
    (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hdecomp := psi_sub_theta_ge_theta_sqrt hx
  have hroot' : (9999 : Real) / 10000 * x ^ (1 / 2 : Real) ≤
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  simpa only [Real.sqrt_eq_rpow] using hroot'.trans hdecomp

theorem theta_lower_9999_of_logFourth_error_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (herror : |Chebyshev.theta y - y| ≤
      (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * y ≤ Chebyshev.theta y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  have hscaled' : (648 : Real) / 1000 * y / (Real.log y) ^ 4 ≤
      (648 : Real) / 1000 * y / (42 : Real) ^ 4 := by
    calc
      (648 : Real) / 1000 * y / (Real.log y) ^ 4 =
          (648 : Real) / 1000 * (y / (Real.log y) ^ 4) := by ring
      _ ≤ (648 : Real) / 1000 * (y / (42 : Real) ^ 4) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = (648 : Real) / 1000 * y / (42 : Real) ^ 4 := by ring
  have hlow := (abs_le.mp herror).1
  nlinarith [hscaled']

theorem theta_lower_9999_of_strict_logFourth_error_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (herror : |Chebyshev.theta y - y| <
      (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * y < Chebyshev.theta y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  have hscaled' : (648 : Real) / 1000 * y / (Real.log y) ^ 4 ≤
      (648 : Real) / 1000 * y / (42 : Real) ^ 4 := by
    calc
      (648 : Real) / 1000 * y / (Real.log y) ^ 4 =
          (648 : Real) / 1000 * (y / (Real.log y) ^ 4) := by ring
      _ ≤ (648 : Real) / 1000 * (y / (42 : Real) ^ 4) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = (648 : Real) / 1000 * y / (42 : Real) ^ 4 := by ring
  have hlow := (abs_lt.mp herror).1
  nlinarith [hscaled']

theorem dusart_gap_from_strict_theta_root_lower
    {x : Real} (hx : 2 ≤ x)
    (hroot : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.theta (x ^ (1 / 2 : Real))) :
    (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x := by
  have hdecomp := psi_sub_theta_ge_theta_sqrt hx
  have hroot' : (9999 : Real) / 10000 * x ^ (1 / 2 : Real) <
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  have hgap' : (9999 : Real) / 10000 * x ^ (1 / 2 : Real) <
      Chebyshev.psi x - Chebyshev.theta x :=
    hroot'.trans_le hdecomp
  simpa only [Real.sqrt_eq_rpow] using hgap'

theorem psi_sub_theta_ge_9999_sqrt_of_large_theta_error
    {x : Real} (hx : (4e18 : Real) ^ 2 ≤ x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| ≤
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by
    have hcut : (0 : Real) < (4e18 : Real) ^ 2 := by positivity
    linarith
  have hroot_cut : (4e18 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by positivity : (0 : Real) < (4e18 : Real))).2
    nlinarith
  have hroot := theta_lower_9999_of_logFourth_error_at_large
    hroot_cut (herror (Real.sqrt x) hroot_cut)
  have hroot' : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  exact dusart_gap_from_theta_root_lower (by linarith) hroot'

theorem psi_sub_theta_gt_9999_sqrt_of_large_strict_theta_error
    {x : Real} (hx : (4e18 : Real) ^ 2 ≤ x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| <
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by
    have hcut : (0 : Real) < (4e18 : Real) ^ 2 := by positivity
    linarith
  have hroot_cut : (4e18 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by positivity : (0 : Real) < (4e18 : Real))).2
    nlinarith
  have hroot := theta_lower_9999_of_strict_logFourth_error_at_large
    hroot_cut (herror (Real.sqrt x) hroot_cut)
  have hroot' : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  exact dusart_gap_from_strict_theta_root_lower (by linarith) hroot'

theorem psi_sub_theta_le_of_root_bound
    {x c : Real} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y ≤ c * y) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      c * (x ^ (1 / 2 : Real) + x ^ (1 / 3 : Real) +
        x ^ (1 / 5 : Real)) := by
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hroot (x ^ (2 : Real)⁻¹) (by positivity)
  have h3 := hroot (x ^ (3 : Real)⁻¹) (by positivity)
  have h5 := hroot (x ^ (5 : Real)⁻¹) (by positivity)
  have h2' : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
      c * x ^ (1 / 2 : Real) := by
    convert h2 using 1 <;> norm_num
  have h3' : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
      c * x ^ (1 / 3 : Real) := by
    convert h3 using 1 <;> norm_num
  have h5' : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      c * x ^ (1 / 5 : Real) := by
    convert h5 using 1 <;> norm_num
  nlinarith [hdecomp, h2', h3', h5']

theorem psi_sub_theta_le_of_three_root_bounds
    {x c : Real} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (h2 : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
      c * x ^ (1 / 2 : Real))
    (h3 : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
      c * x ^ (1 / 3 : Real))
    (h5 : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      c * x ^ (1 / 5 : Real)) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      c * (x ^ (1 / 2 : Real) + x ^ (1 / 3 : Real) +
        x ^ (1 / 5 : Real)) := by
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  nlinarith [hdecomp, h2, h3, h5]

theorem fifth_rpow_le_three_fifths_cube_rpow
    {x : Real} (hx : (121 : Real) ≤ x) :
    x ^ (1 / 5 : Real) ≤ (3 : Real) / 5 * x ^ (1 / 3 : Real) := by
  have hx_pos : 0 < x := by linarith
  have hpow : ((13 : Real) / 10) ^ (15 : Nat) ≤ x := by
    have hnum : ((13 : Real) / 10) ^ (15 : Nat) ≤ 121 := by norm_num
    exact hnum.trans hx
  have hlog := Real.log_le_log
    (by positivity : (0 : Real) < ((13 : Real) / 10) ^ (15 : Nat)) hpow
  rw [Real.log_pow] at hlog
  have ha : (13 : Real) / 10 ≤ x ^ (1 / 15 : Real) := by
    apply Real.le_rpow_of_log_le hx_pos
    nlinarith
  have ha_pos : 0 < x ^ (1 / 15 : Real) := by positivity
  have h5 : x ^ (1 / 5 : Real) =
      (x ^ (1 / 15 : Real)) ^ (3 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx_pos)]
    norm_num
  have h3 : x ^ (1 / 3 : Real) =
      (x ^ (1 / 15 : Real)) ^ (5 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx_pos)]
    norm_num
  rw [h5, h3]
  let a : Real := x ^ (1 / 15 : Real)
  have ha2 : (5 : Real) / 3 ≤ a ^ 2 := by
    dsimp [a]
    nlinarith [sq_nonneg (x ^ (1 / 15 : Real) - 13 / 10)]
  have hunit : (1 : Real) ≤ (3 / 5 : Real) * a ^ 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hunit (by positivity : 0 ≤ a ^ 3)
  dsimp [a] at hmul ⊢
  nlinarith

theorem dusart_gap_upper_from_uniform_root_bound
    {x : Real} (hx : (121 : Real) ≤ x)
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y ≤ (100007 : Real) / 100000 * y) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hdecomp := psi_sub_theta_le_of_root_bound
    (x := x) (c := (100007 : Real) / 100000) (by linarith) (by norm_num) hroot
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hdecomp
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp]
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp', hscaled', hcoeff]

theorem psi_upper_of_theta_upper_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (htheta : Chebyshev.theta y ≤ y + y / 36260) :
    Chebyshev.psi y ≤ (100007 : Real) / 100000 * y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hcor : Chebyshev.psi y - Chebyshev.theta y ≤
      y / (Real.log y) ^ 4 := by
    have habs := theta_sub_psi_abs_le_logFourth hy
    have hnonneg : 0 ≤ Chebyshev.psi y - Chebyshev.theta y := by
      linarith [Chebyshev.theta_le_psi y]
    rw [abs_sub_comm, abs_of_nonneg hnonneg] at habs
    exact habs
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  nlinarith [hcor, hscaled, htheta]

theorem dusart_gap_upper_from_three_large_theta_bounds
    {x : Real} (hx : (121 : Real) ≤ x)
    (h2cut : (4e18 : Real) ≤ x ^ (2 : Real)⁻¹)
    (h3cut : (4e18 : Real) ≤ x ^ (3 : Real)⁻¹)
    (h5cut : (4e18 : Real) ≤ x ^ (5 : Real)⁻¹)
    (h2theta : Chebyshev.theta (x ^ (2 : Real)⁻¹) ≤
      x ^ (2 : Real)⁻¹ + x ^ (2 : Real)⁻¹ / 36260)
    (h3theta : Chebyshev.theta (x ^ (3 : Real)⁻¹) ≤
      x ^ (3 : Real)⁻¹ + x ^ (3 : Real)⁻¹ / 36260)
    (h5theta : Chebyshev.theta (x ^ (5 : Real)⁻¹) ≤
      x ^ (5 : Real)⁻¹ + x ^ (5 : Real)⁻¹ / 36260) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have h2psi := psi_upper_of_theta_upper_at_large h2cut h2theta
  have h3psi := psi_upper_of_theta_upper_at_large h3cut h3theta
  have h5psi := psi_upper_of_theta_upper_at_large h5cut h5theta
  have h2psi' : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) := by
    simpa only [show (2 : Real)⁻¹ = 1 / 2 by norm_num] using h2psi
  have h3psi' : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 3 : Real) := by
    simpa only [show (3 : Real)⁻¹ = 1 / 3 by norm_num] using h3psi
  have h5psi' : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [show (5 : Real)⁻¹ = 1 / 5 by norm_num] using h5psi
  have hdecomp := psi_sub_theta_le_of_three_root_bounds
    (x := x) (c := (100007 : Real) / 100000) (by linarith) (by norm_num)
    h2psi' h3psi' h5psi'
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hdecomp
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp]
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp', hscaled', hcoeff]

theorem psi_sub_theta_ge_elementary_sqrt_gap
    {x : Real} (hx : (62500000000 : Real) ≤ x) :
    (86 : Real) / 100 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by linarith
  have hroot_lower : (250000 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by norm_num : (0 : Real) < 250000)).2
    nlinarith
  have htheta := elementary_theta_lower_from_250000 hroot_lower
  have hdecomp := psi_sub_theta_ge_theta_sqrt (by linarith : (2 : Real) ≤ x)
  have htheta' : (86 : Real) / 100 * Real.sqrt x ≤
      Chebyshev.theta (Real.sqrt x) := by
    simpa only [Real.sqrt_eq_rpow] using htheta
  have hdecomp' : Chebyshev.theta (Real.sqrt x) ≤
      Chebyshev.psi x - Chebyshev.theta x := by
    simpa only [Real.sqrt_eq_rpow] using hdecomp
  exact htheta'.trans hdecomp'

theorem dusart_theta_upper_tail_step
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_upper : x ≤ (1446257067000 : Real))
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := by
    simpa using Real.sq_sqrt (le_of_lt hx_pos)
  have hmain := theta_le_one_plus_dusart_error_of_psi_upper_and_gap hpsi hgap
  have hlinear :
      (100002841 : Real) / 100000000 * x -
          (9999 : Real) / 10000 * Real.sqrt x - x ≤ x / 36260 := by
    have hsqrt_lower : (894000 : Real) ≤ Real.sqrt x := by
      apply (Real.le_sqrt' (by norm_num : (0 : Real) < 894000)).2
      nlinarith
    have hsqrt_upper : Real.sqrt x ≤ (12026689 : Real) / 10 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · norm_num
      · nlinarith
    have hxs : x ≤ (12026689 : Real) / 10 * Real.sqrt x := by
      calc
        x = Real.sqrt x * Real.sqrt x := by nlinarith [hsqrt_sq]
        _ ≤ (12026689 : Real) / 10 * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hsqrt_upper hsqrt_nonneg
    nlinarith
  linarith

theorem dusart_theta_upper_e28_step
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  apply dusart_theta_upper_tail_step hx ?_ hpsi hgap
  exact hx_exp.trans (le_of_lt exp_twentyEight_lt_dusart_endpoint)

theorem dusart_theta_upper_e28_from_absolute_psi_error
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi_error : |Chebyshev.psi x - x| ≤
      (2841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  have hpsi : Chebyshev.psi x ≤
      (100002841 : Real) / 100000000 * x := by
    have hupper := (abs_le.mp hpsi_error).2
    nlinarith
  exact dusart_theta_upper_e28_step hx hx_exp hpsi hgap

/-! The strict form is the one consumed by the published theta interface.
The paper's two strict input estimates are retained here instead of being
weakened to a closed inequality at this boundary. -/
theorem dusart_theta_upper_e28_step_strict
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi : Chebyshev.psi x < (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x < x / 36260 := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := by
    simpa using Real.sq_sqrt (le_of_lt hx_pos)
  have hx_upper : x ≤ (1446257067000 : Real) := by
    exact hx_exp.trans (le_of_lt exp_twentyEight_lt_dusart_endpoint)
  have hsqrt_lower : (894000 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by norm_num : (0 : Real) < 894000)).2
    nlinarith
  have hsqrt_upper : Real.sqrt x ≤ (12026689 : Real) / 10 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  have hxs : x ≤ (12026689 : Real) / 10 * Real.sqrt x := by
    calc
      x = Real.sqrt x * Real.sqrt x := by nlinarith [hsqrt_sq]
      _ ≤ (12026689 : Real) / 10 * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hsqrt_upper hsqrt_nonneg
  have hlinear :
      (100002841 : Real) / 100000000 * x -
          (9999 : Real) / 10000 * Real.sqrt x - x ≤ x / 36260 := by
    nlinarith
  have hmain : Chebyshev.theta x - x <
      (100002841 : Real) / 100000000 * x -
        (9999 : Real) / 10000 * Real.sqrt x - x := by
    linarith
  exact hmain.trans_le hlinear

end
end PrimeFactorUnimodality
