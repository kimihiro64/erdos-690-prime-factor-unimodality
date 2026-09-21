import PrimeFactorUnimodality.Helpers.Analytic.DusartProofPart04


set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/- The finite boundary in Dusart's Lemma 3.3 is exactly 10^33. -/

/-! # DusartProof source part 05

This module is a sequential source split of the analytic development.
-/

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

/-! Global form of Dusart's Proposition 3.1.  The finite interval ending at
the square of the explicit theta cutoff is kept as a separate input; above it
the square-root substitution and the theta error prove the estimate directly. -/
theorem dusart_proposition_3_1_of_finite_and_strict_theta_error
    (finite : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| <
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  intro x hx
  by_cases hlarge : (4e18 : Real) ^ 2 ≤ x
  · exact psi_sub_theta_gt_9999_sqrt_of_large_strict_theta_error
      hlarge herror
  · exact finite x hx (lt_of_not_ge hlarge)

/-! The same Proposition 3.1 split in the exact tail interface used by the
provider modules. -/
theorem dusart_proposition_3_1_of_finite_and_thetaErrorAbove
    (finite : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (4e18 : Real)) :
    ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  apply dusart_proposition_3_1_of_finite_and_strict_theta_error finite
  intro y hy
  exact thetaError y hy

theorem dusart_proposition_3_1_of_indexed_rows_and_thetaErrorAbove
    {n : Nat} {X : Real}
    {rows : Fin n → DusartProposition31FiniteRow}
    (hX : (4e18 : Real) ^ 2 ≤ X)
    (cover : DusartProposition31FiniteIndexedRowsCover rows X)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (4e18 : Real)) :
    ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  apply dusart_proposition_3_1_of_finite_and_thetaErrorAbove
    (fun x hx hxc => dusartProposition31Finite_of_indexed_rows cover
      x hx (le_trans (le_of_lt hxc) hX))
  exact thetaError

theorem dusart_proposition_3_1_of_rows_and_thetaErrorAbove
    {X : Real} {rows : List DusartProposition31FiniteRow}
    (hX : (4e18 : Real) ^ 2 ≤ X)
    (cover : DusartProposition31FiniteRowsCover rows X)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (4e18 : Real)) :
    ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  exact dusart_proposition_3_1_of_indexed_rows_and_thetaErrorAbove
    hX (dusartProposition31FiniteIndexedRowsCover_of_list cover) thetaError

theorem dusart_proposition_3_1_of_integer_endpoint_check_and_thetaErrorAbove
    (endpoint : ∀ n : Nat, 121 ≤ n →
      (9999 : Real) / 10000 * Real.sqrt ((n : Real) + 1) <
        Chebyshev.psi (n : Real) - Chebyshev.theta n)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (4e18 : Real)) :
    ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  apply dusart_proposition_3_1_of_finite_and_thetaErrorAbove
    (fun x hx hxc =>
      dusartProposition31Finite_of_integer_endpoint_check
        (X := (4e18 : Real) ^ 2) endpoint x hx (le_of_lt hxc))
  exact thetaError

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

theorem psi_sub_theta_lt_of_root_bound
    {x c : Real} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y < c * y) :
    Chebyshev.psi x - Chebyshev.theta x <
      c * (x ^ (1 / 2 : Real) + x ^ (1 / 3 : Real) +
        x ^ (1 / 5 : Real)) := by
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hroot (x ^ (2 : Real)⁻¹) (by positivity)
  have h3 := hroot (x ^ (3 : Real)⁻¹) (by positivity)
  have h5 := hroot (x ^ (5 : Real)⁻¹) (by positivity)
  have h2' : Chebyshev.psi (x ^ (2 : Real)⁻¹) <
      c * x ^ (1 / 2 : Real) := by
    convert h2 using 1 <;> norm_num
  have h3' : Chebyshev.psi (x ^ (3 : Real)⁻¹) <
      c * x ^ (1 / 3 : Real) := by
    convert h3 using 1 <;> norm_num
  have h5' : Chebyshev.psi (x ^ (5 : Real)⁻¹) <
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
    {x : Real} (hx : (64 : Real) ≤ x) :
    x ^ (1 / 5 : Real) ≤ (3 : Real) / 5 * x ^ (1 / 3 : Real) := by
  have hx_pos : 0 < x := by linarith
  have hpow : ((13 : Real) / 10) ^ (15 : Nat) ≤ x := by
    have hnum : ((13 : Real) / 10) ^ (15 : Nat) ≤ 64 := by norm_num
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

/-! This is Dusart's Proposition 3.2 after the root estimate has been
supplied.  The root estimate is kept explicit so this theorem records the
actual prime-power argument rather than importing Proposition 3.2. -/
theorem dusart_proposition_3_2_of_uniform_strict_root_bound
    {x : Real} (hx : (64 : Real) ≤ x)
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y < (100007 : Real) / 100000 * y) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hdecomp := psi_sub_theta_lt_of_root_bound
    (x := x) (c := (100007 : Real) / 100000) (by linarith) (by norm_num)
    hroot
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hdecomp
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 *
          x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp, hscaled', hcoeff]

/-! The published proposition is global.  Its proof has a finite endpoint
check below `64` and the prime-power argument above that endpoint; keeping
those two inputs separate makes the exact scope of the remaining finite check
visible to the final provider. -/
theorem dusart_proposition_3_2_of_uniform_strict_root_bound_all
    (small : ∀ x : Real, 0 < x → x < 64 →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real))
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y < (100007 : Real) / 100000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  by_cases hsmall : x < 64
  · exact small x hx hsmall
  · exact dusart_proposition_3_2_of_uniform_strict_root_bound
      (le_of_not_gt hsmall) hroot

theorem dusart_proposition_3_2_of_uniform_strict_root_bound_all_closed
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y < (100007 : Real) / 100000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  exact dusart_proposition_3_2_of_uniform_strict_root_bound_all
    (fun y hy hy64 => dusart_proposition_3_2_small_64 hy hy64) hroot x hx

/-! This is the numerical composition used in the paper: Lemma 3.3 controls
the prime-power tail after the square-root term, while Proposition 5.1
controls that square-root theta term. -/
theorem dusart_proposition_3_2_of_lemma_3_3_and_theta_upper
    {x : Real} (hx : 0 < x)
    (hlemma : Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / 3 : Real))
    (htheta : Chebyshev.theta (Real.sqrt x) <
      (100007 : Real) / 100000 * Real.sqrt x) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  nlinarith

theorem dusart_proposition_3_2_of_lemma_3_3_and_dusart_theta_upper
    {x : Real} (hx : 0 < x)
    (hlemma : Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / 3 : Real))
    (htheta : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have htheta' := htheta (Real.sqrt x) hsqrt_pos
  have htheta'' : Chebyshev.theta (Real.sqrt x) <
      (100007 : Real) / 100000 * Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  exact dusart_proposition_3_2_of_lemma_3_3_and_theta_upper
    hx hlemma htheta''

theorem dusart_theta_upper_100007_of_bounds
    (thetaBounds : HasDusartThetaBounds) :
    ∀ y : Real, 0 < y →
      Chebyshev.theta y < (100007 : Real) / 100000 * y := by
  intro y hy
  have hupper := thetaBounds.1 y hy
  nlinarith

/-! The paper's global Proposition 3.2 assembly.  The input `lemma` is the
uniform Lemma 3.3 estimate, including its bounded direct-computation range;
the second input is the global Proposition 5.1 theta upper bound. -/
theorem dusart_proposition_3_2_of_paper_lemma_and_theta_upper
    (hlemma : ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / 3 : Real))
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  exact dusart_proposition_3_2_of_lemma_3_3_and_dusart_theta_upper
    hx (hlemma x hx) theta_upper

theorem dusart_proposition_3_2_of_paper_lemma_and_theta_bounds
    (hlemma : ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / 3 : Real))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
          Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  exact dusart_proposition_3_2_of_lemma_3_3_and_theta_upper hx
    (hlemma x hx)
    (dusart_theta_upper_100007_of_bounds thetaBounds
      (Real.sqrt x) (Real.sqrt_pos.2 hx))

theorem dusart_proposition_3_2_of_10m_lemma_and_theta_bounds
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  apply dusart_proposition_3_2_of_paper_lemma_and_theta_bounds
  exact dusart_lemma_3_3_of_10m_intermediate_and_theta_upper
    (dusart_theta_upper_1000081_of_bounds thetaBounds)

/-! The prime-power part of Dusart's Lemma 3.3.  For the large range the
floor in the Chebyshev decomposition is at least two, so the square-root
term can be split off exactly and only exponents `k ≥ 3` remain. -/
theorem dusart_lemma_3_3_prime_power_decomposition
    {x : Real} (hx : (9 : Real) ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) =
      ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊,
        Chebyshev.theta (x ^ (1 / (k : Real))) := by
  have hx2 : (2 : Real) ≤ x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN : 2 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ hlog2).2
    have hlog : Real.log 4 ≤ Real.log x := by
      apply Real.log_le_log (by norm_num)
      linarith
    rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num,
      Real.log_pow] at hlog
    norm_num at hlog ⊢
    linarith
  have hsplit :
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
          Chebyshev.theta (x ^ (1 / (k : Real))) =
        Chebyshev.theta (x ^ ((1 : Real) / 2)) +
          ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊,
            Chebyshev.theta (x ^ (1 / (k : Real))) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hN,
      ← Finset.Icc_add_one_left_eq_Ioc]
    ring_nf
  have hdecomp := Chebyshev.psi_eq_theta_add_sum_theta hx2
  have hsqrt : x ^ ((1 : Real) / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsplit, hsqrt] at hdecomp
  linarith

/- Integer-power certificates can bound each real power in the intermediate
   exponent range without asking the kernel to approximate an irrational root. -/
theorem dusart_rpow_ratio_bound
    {x b q : Real} {k : Nat}
    (hb : 1 ≤ b) (hbx : b ≤ x) (hk : 3 ≤ k)
    (hq0 : 0 ≤ q)
    (hq : 1 ≤ q ^ (3 * k) * b ^ (k - 3)) :
    x ^ (1 / (k : Real)) ≤ q * x ^ (1 / (3 : Real)) := by
  have hx : 0 < x := lt_of_lt_of_le (by linarith) hbx
  have hpow_base : b ^ (k - 3) ≤ x ^ (k - 3) := by
    exact pow_le_pow_left' (by linarith) hbx
  have hprod : 1 ≤ q ^ (3 * k) * x ^ (k - 3) := by
    calc
      (1 : Real) ≤ q ^ (3 * k) * b ^ (k - 3) := hq
      _ ≤ q ^ (3 * k) * x ^ (k - 3) := by
        gcongr
  have hpow_nat : x ^ 3 ≤ q ^ (3 * k) * x ^ k := by
    have hx3 : 0 ≤ x ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hprod hx3
    rw [← pow_add] at hmul
    have hkadd : 3 + (k - 3) = k := by omega
    rw [hkadd] at hmul
    nlinarith
  have hpow :
      (x ^ (1 / (k : Real))) ^ (3 * k) ≤
        (q * x ^ (1 / (3 : Real))) ^ (3 * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
    norm_num at *
    rw [show (1 / (k : Real)) * (3 * k : Real) = 3 by
      field_simp; ring]
    rw [show (1 / (3 : Real)) * (3 * k : Real) = k by
      norm_num; ring]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    simpa [pow_mul] using hpow_nat
  exact (Real.rpow_le_rpow_iff (by positivity) (by positivity)
    (by positivity : (0 : Real) < (3 * k : Real))).mp hpow

/-! A reusable elementary estimate for the real-power sum occurring after the
decomposition.  The only input is monotonicity of `x^a` in the exponent when
`x ≥ 1`; the finite cardinality calculation is kept explicit. -/
theorem dusart_prime_power_rpow_sum_le
    {x : Real} (hx : (1 : Real) ≤ x) {N : Nat} (hN : 3 ≤ N) :
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
      x ^ (1 / (3 : Real)) +
        ((N : Real) - 3) * x ^ (1 / (4 : Real)) := by
  have hunion : Finset.Icc 3 N = {3} ∪ Finset.Icc 4 N := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_singleton, Finset.mem_union]
    omega
  rw [hunion, Finset.sum_union]
  · simp only [Finset.sum_singleton]
    calc
      x ^ (1 / (3 : Real)) + ∑ k ∈ Finset.Icc 4 N, x ^ (1 / (k : Real)) ≤
          x ^ (1 / (3 : Real)) +
            (Finset.Icc 4 N).card • x ^ (1 / (4 : Real)) := by
        gcongr
        apply Finset.sum_le_card_nsmul
        intro k hk
        have hk4 : 4 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkr : (4 : Real) ≤ (k : Real) := by exact_mod_cast hk4
        have hexp : (1 / (k : Real) : Real) ≤ 1 / 4 := by
          exact one_div_le_one_div_of_le (by norm_num) hkr
        exact Real.rpow_le_rpow_of_exponent_le hx hexp
      _ = x ^ (1 / (3 : Real)) +
          ((N : Real) - 3) * x ^ (1 / (4 : Real)) := by
        rw [nsmul_eq_mul, Nat.card_Icc]
        have hsub : 4 ≤ N + 1 := by omega
        rw [Nat.cast_sub hsub]
        push_cast
        ring
  · apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    simp only [Finset.mem_singleton] at hk₁
    simp only [Finset.mem_Icc] at hk₂
    omega

/-! The numerical coefficient in Lemma 3.3 depends only on the number of
exponents, not on the way that count was obtained.  Keeping this conversion
separate lets a later explicit endpoint argument replace the coarse logarithmic
count without repeating the prime-power estimate. -/
theorem dusart_prime_power_rpow_sum_le_of_count
    {x : Real} (hx : (1 : Real) ≤ x) {N : Nat} (hN : 3 ≤ N)
    (hcount : (N : Real) ≤ (7 : Real) / 10 * x ^ (1 / (12 : Real))) :
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
      (17 : Real) / 10 * x ^ (1 / (3 : Real)) := by
  have hsum := dusart_prime_power_rpow_sum_le hx hN
  have hNnonneg : 0 ≤ (N : Real) - 3 := by
    exact_mod_cast Nat.zero_le (N - 3)
  have hpow4 : 0 ≤ x ^ (1 / (4 : Real)) := by positivity
  have htail : ((N : Real) - 3) * x ^ (1 / (4 : Real)) ≤
      (7 : Real) / 10 * x ^ (1 / (3 : Real)) := by
    calc
      ((N : Real) - 3) * x ^ (1 / (4 : Real)) ≤
          (N : Real) * x ^ (1 / (4 : Real)) := by
        gcongr
        norm_num
      _ ≤ ((7 : Real) / 10 * x ^ (1 / (12 : Real))) *
          x ^ (1 / (4 : Real)) :=
        mul_le_mul_of_nonneg_right hcount hpow4
      _ = (7 : Real) / 10 *
          (x ^ (1 / (12 : Real)) * x ^ (1 / (4 : Real))) := by ring
      _ = (7 : Real) / 10 * x ^ (1 / (3 : Real)) := by
        rw [← Real.rpow_add (by positivity : 0 < x)]
        congr 1
        norm_num
  calc
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
        x ^ (1 / (3 : Real)) +
          ((N : Real) - 3) * x ^ (1 / (4 : Real)) := hsum
    _ ≤ x ^ (1 / (3 : Real)) +
        (7 : Real) / 10 * x ^ (1 / (3 : Real)) :=
      add_le_add le_rfl htail
    _ = (17 : Real) / 10 * x ^ (1 / (3 : Real)) := by ring

/-! The logarithmic count of exponents is negligible at Dusart's large
cutoff.  This is the elementary monotonicity estimate used to turn the
finite sum above into a fixed multiple of `x^(1/3)`. -/
theorem dusart_floor_log_div_two_le_rpow
    {x : Real} (hx : (10 ^ 11 : Real) ^ 3 ≤ x) :
    (⌊Real.log x / Real.log 2⌋₊ : Real) ≤
      (7 : Real) / 10 * x ^ (1 / (12 : Real)) := by
  have hx0 : (10 : Real) ^ 33 ≤ x := by
    convert hx using 1
    norm_num [pow_mul]
  have hx0_pos : 0 < (10 : Real) ^ 33 := by positivity
  have hx_pos : 0 < x := hx0_pos.trans_le hx0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_pos : 0 < Real.log x := by
    apply Real.log_pos
    have : (1 : Real) < (10 : Real) ^ 33 := by norm_num
    exact this.trans_le hx0
  have hthreshold : Real.exp ((1 / (12 : Real))⁻¹) ≤ (10 : Real) ^ 33 := by
    rw [show (1 / (12 : Real))⁻¹ = 12 by norm_num]
    have hexp : Real.exp (12 : Real) < (3 : Real) ^ 12 := by
      rw [show (12 : Real) = (12 : Nat) * 1 by norm_num,
        Real.exp_nat_mul]
      exact pow_lt_pow_left₀ Real.exp_one_lt_three
        (Real.exp_pos 1).le (by norm_num)
    linarith
  have hratio_mono := Real.log_div_self_rpow_antitoneOn
    (a := (1 / (12 : Real))) (by norm_num)
    hthreshold (le_trans hthreshold hx0) hx0
  have hpow160 : (160 : Real) ≤ ((10 : Real) ^ 33) ^ (1 / (12 : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    apply Real.le_rpow_of_log_le (by norm_num)
    rw [show (160 : Real) = 2 ^ (4 : Nat) * 10 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have hlog2_10 : 16 * Real.log 2 ≤ 7 * Real.log 10 := by
      have hpow : (2 : Real) ^ 16 ≤ (10 : Real) ^ 7 := by norm_num
      have := Real.log_le_log (by positivity) hpow
      rw [Real.log_pow, Real.log_pow] at this
      exact this
    have hlog10_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have hlog160 : Real.log 160 = 4 * Real.log 2 + Real.log 10 := by
      rw [show (160 : Real) = 2 ^ (4 : Nat) * 10 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    nlinarith [hlog2_10]
  have hlog10_lt : Real.log 10 < (231 : Real) / 100 := by
    have hexp : (10 : Real) < Real.exp ((231 : Real) / 100) := by
      have h := Real.sum_le_exp_of_nonneg (x := (231 : Real) / 100)
        (by norm_num) 8
      norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
      nlinarith
    exact (Real.log_lt_iff_lt_exp (x := (10 : Real))
      (y := (231 : Real) / 100) (by norm_num)).2 hexp
  have hratio : Real.log x / x ^ (1 / (12 : Real)) ≤
      (7 : Real) / 10 * Real.log 2 := by
    have hden : 0 < x ^ (1 / (12 : Real)) := by positivity
    have hmono : Real.log x / x ^ (1 / (12 : Real)) ≤
        Real.log ((10 : Real) ^ 33) / ((10 : Real) ^ 33) ^ (1 / (12 : Real)) := by
      simpa using hratio_mono
    have hnum : Real.log ((10 : Real) ^ 33) ≤ (33 : Real) * ((231 : Real) / 100) := by
      rw [Real.log_pow]
      nlinarith
    have hquot : Real.log ((10 : Real) ^ 33) /
        ((10 : Real) ^ 33) ^ (1 / (12 : Real)) ≤
        ((33 : Real) * ((231 : Real) / 100)) / 160 := by
      calc
        Real.log ((10 : Real) ^ 33) /
            ((10 : Real) ^ 33) ^ (1 / (12 : Real)) ≤
            ((33 : Real) * ((231 : Real) / 100)) /
              ((10 : Real) ^ 33) ^ (1 / (12 : Real)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ ((33 : Real) * ((231 : Real) / 100)) / 160 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow160
    have hlog2_lower : (69 : Real) / 100 < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    nlinarith [hmono, hquot]
  have hfloor : (⌊Real.log x / Real.log 2⌋₊ : Real) ≤
      Real.log x / Real.log 2 := by
    exact_mod_cast Nat.floor_le (div_nonneg hlogx_pos.le hlog2.le)
  have hcount : Real.log x / Real.log 2 ≤
      (7 : Real) / 10 * x ^ (1 / (12 : Real)) := by
    have hden : 0 < x ^ (1 / (12 : Real)) := by positivity
    apply (div_le_iff₀ hlog2).2
    have h := (div_le_iff₀ hden).1 hratio
    nlinarith
  exact hfloor.trans hcount

/-! Large-range form of Dusart's Lemma 3.3.  The remaining finite range is
handled separately by the paper's direct computation; this theorem contains
the complete analytic tail argument. -/
theorem dusart_lemma_3_3_large_of_count
    {x : Real} (hx : (10 ^ 11 : Real) ^ 3 ≤ x)
    (hcount : (⌊Real.log x / Real.log 2⌋₊ : Real) ≤
      (7 : Real) / 10 * x ^ (1 / (12 : Real)))
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  have hx9 : (9 : Real) ≤ x := by
    have : (9 : Real) ≤ (10 ^ 11 : Real) ^ 3 := by norm_num
    exact this.trans hx
  have hdecomp := dusart_lemma_3_3_prime_power_decomposition hx9
  let N : Nat := ⌊Real.log x / Real.log 2⌋₊
  have hN3 : 3 ≤ N := by
    dsimp [N]
    apply Nat.le_floor
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    apply (le_div_iff₀ hlog2).2
    have hlog : Real.log 8 ≤ Real.log x := by
      apply Real.log_le_log (by norm_num)
      exact (show (8 : Real) ≤ (10 ^ 11 : Real) ^ 3 by norm_num).trans hx
    rw [show (8 : Real) = 2 ^ (3 : Nat) by norm_num,
      Real.log_pow] at hlog
    norm_num at hlog ⊢
    linarith
  have hsum17 := dusart_prime_power_rpow_sum_le_of_count
    (x := x) (by linarith [hx]) hN3 hcount
  have htheta_sum :
      (∑ k ∈ Finset.Icc 3 N,
        Chebyshev.theta (x ^ (1 / (k : Real)))) <
      (1000081 : Real) / 1000000 *
        (∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real))) := by
    calc
      (∑ k ∈ Finset.Icc 3 N,
          Chebyshev.theta (x ^ (1 / (k : Real)))) <
          ∑ k ∈ Finset.Icc 3 N,
            (1000081 : Real) / 1000000 * x ^ (1 / (k : Real)) := by
        apply Finset.sum_lt_sum_of_nonempty
        · simp [hN3]
        · intro k hk
          apply theta_upper
          positivity
      _ = (1000081 : Real) / 1000000 *
          (∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real))) := by
        rw [Finset.mul_sum]
  have hcoef :
      (1000081 : Real) / 1000000 * (17 / 10 : Real) <
        (1777745 : Real) / 1000000 := by norm_num
  dsimp [N] at hdecomp htheta_sum hsum17
  calc
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) =
      ∑ k ∈ Finset.Icc 3 N,
        Chebyshev.theta (x ^ (1 / (k : Real))) := hdecomp
    _ < (1000081 : Real) / 1000000 *
        (∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real))) := htheta_sum
    _ ≤ (1000081 : Real) / 1000000 *
        ((17 : Real) / 10 * x ^ (1 / (3 : Real))) :=
      mul_le_mul_of_nonneg_left hsum17 (by norm_num)
    _ = ((1000081 : Real) / 1000000 * (17 / 10 : Real)) *
        x ^ (1 / (3 : Real)) := by ring
    _ < (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) :=
      mul_lt_mul_of_pos_right hcoef (by positivity)

/-! The published large-range theorem supplies the count estimate by the
elementary logarithmic argument, while the preceding theorem keeps that
numerical step replaceable by an independent explicit estimate. -/

end

end PrimeFactorUnimodality
