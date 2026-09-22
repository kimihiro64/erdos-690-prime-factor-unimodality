import PrimeFactorUnimodality.Helpers.Analytic.DusartRootBounds

set_option autoImplicit false

/-! # Numerical transfer from psi bounds to theta bounds

Analytic estimates and assemblers with no generated endpoint dependencies.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem dusart_gap_upper_from_uniform_root_bound
    {x : Real} (hx : (64 : Real) ≤ x)
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

theorem psi_upper_of_strict_theta_upper_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (htheta : Chebyshev.theta y < y + y / 36260) :
    Chebyshev.psi y < (100007 : Real) / 100000 * y := by
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
  have hsum : Chebyshev.psi y <
      y + y / 36260 + y / (42 : Real) ^ 4 := by
    nlinarith [hcor, hscaled]
  have hbound : y + y / 36260 + y / (42 : Real) ^ 4 ≤
      (100007 : Real) / 100000 * y := by
    nlinarith [hy_pos]
  exact hsum.trans_le hbound

theorem dusart_gap_upper_from_three_large_theta_bounds
    {x : Real} (hx : (64 : Real) ≤ x)
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

theorem dusart_gap_upper_from_three_strict_large_theta_bounds
    {x : Real} (hx : (64 : Real) ≤ x)
    (h2cut : (4e18 : Real) ≤ x ^ (2 : Real)⁻¹)
    (h3cut : (4e18 : Real) ≤ x ^ (3 : Real)⁻¹)
    (h5cut : (4e18 : Real) ≤ x ^ (5 : Real)⁻¹)
    (h2theta : Chebyshev.theta (x ^ (2 : Real)⁻¹) <
      x ^ (2 : Real)⁻¹ + x ^ (2 : Real)⁻¹ / 36260)
    (h3theta : Chebyshev.theta (x ^ (3 : Real)⁻¹) <
      x ^ (3 : Real)⁻¹ + x ^ (3 : Real)⁻¹ / 36260)
    (h5theta : Chebyshev.theta (x ^ (5 : Real)⁻¹) <
      x ^ (5 : Real)⁻¹ + x ^ (5 : Real)⁻¹ / 36260) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have h2psi := psi_upper_of_strict_theta_upper_at_large h2cut h2theta
  have h3psi := psi_upper_of_strict_theta_upper_at_large h3cut h3theta
  have h5psi := psi_upper_of_strict_theta_upper_at_large h5cut h5theta
  have h2psi' : Chebyshev.psi (x ^ (2 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) := by
    simpa only [show (2 : Real)⁻¹ = 1 / 2 by norm_num] using h2psi
  have h3psi' : Chebyshev.psi (x ^ (3 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 3 : Real) := by
    simpa only [show (3 : Real)⁻¹ = 1 / 3 by norm_num] using h3psi
  have h5psi' : Chebyshev.psi (x ^ (5 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [show (5 : Real)⁻¹ = 1 / 5 by norm_num] using h5psi
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  have hdecomp'' : Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp, h2psi', h3psi', h5psi']
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [hsqrt] using hdecomp''
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
