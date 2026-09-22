import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Helpers.Analytic.DusartFiniteRows
import PrimeFactorUnimodality.Helpers.Analytic.DusartPrimePower
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryChebyshevConsequences
import PrimeFactorUnimodality.Helpers.Analytic.RelativePsiTheta

set_option autoImplicit false

/-! # Root estimates in Dusart's psi–theta comparison

Analytic estimates and assemblers with no generated endpoint dependencies.
-/

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

theorem theta_lower_9999_of_logFourth_error_at_large_strict
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (herror : |Chebyshev.theta y - y| ≤
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
  have hlow := (abs_le.mp herror).1
  nlinarith [hscaled']

theorem theta_lower_9999_of_logFourth_error_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (herror : |Chebyshev.theta y - y| ≤
      (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * y ≤ Chebyshev.theta y := by
  exact (theta_lower_9999_of_logFourth_error_at_large_strict hy herror).le

theorem theta_lower_9999_of_strict_logFourth_error_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (herror : |Chebyshev.theta y - y| <
      (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * y < Chebyshev.theta y := by
  exact theta_lower_9999_of_logFourth_error_at_large_strict hy herror.le

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

theorem psi_sub_theta_gt_9999_sqrt_of_large_theta_error
    {x : Real} (hx : (4e18 : Real) ^ 2 ≤ x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| ≤
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by
    have hcut : (0 : Real) < (4e18 : Real) ^ 2 := by positivity
    linarith
  have hroot_cut : (4e18 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by positivity : (0 : Real) < (4e18 : Real))).2
    nlinarith
  have hroot := theta_lower_9999_of_logFourth_error_at_large_strict
    hroot_cut (herror (Real.sqrt x) hroot_cut)
  have hroot' : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  exact dusart_gap_from_strict_theta_root_lower (by linarith) hroot'

theorem psi_sub_theta_gt_9999_sqrt_of_large_strict_theta_error
    {x : Real} (hx : (4e18 : Real) ^ 2 ≤ x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| <
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x := by
  exact psi_sub_theta_gt_9999_sqrt_of_large_theta_error hx (fun y hy => (herror y hy).le)

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
  intro x hx
  by_cases hlarge : (4e18 : Real) ^ 2 ≤ x
  · exact psi_sub_theta_gt_9999_sqrt_of_large_theta_error hlarge thetaError
  · exact finite x hx (lt_of_not_ge hlarge)

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

end

end PrimeFactorUnimodality
