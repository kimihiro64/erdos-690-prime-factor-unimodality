import PrimeFactorUnimodality.Helpers.Analytic.RelativePsiTheta
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryChebyshevConsequences
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLogBounds
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem psi_sub_theta_mono {x y : Real} (hxy : x ≤ y) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      Chebyshev.psi y - Chebyshev.theta y := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono hxy)⟩, hn.2⟩
  · intro n hn hns
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem psi_sub_theta_nat_24_lt_four :
    Chebyshev.psi (24 : Real) - Chebyshev.theta 24 < 4 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 24
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 24
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 25,
      ↑(Nat.log p 24) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 25, Real.log ↑p < 4
  have hp : Nat.primesBelow 25 = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem psi_sub_theta_nat_3_eq_zero :
    Chebyshev.psi (3 : Real) - Chebyshev.theta 3 = 0 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 3
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 3
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesLE 3,
      ↑(Nat.log p 3) * Real.log ↑p) -
    ∑ p ∈ Nat.primesLE 3, Real.log ↑p = 0
  have hp : Nat.primesLE 3 = {2, 3} := by decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]

theorem psi_sub_theta_nat_8_lt_two :
    Chebyshev.psi (8 : Real) - Chebyshev.theta 8 < 2 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 8
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 8
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 9,
      ↑(Nat.log p 8) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 9, Real.log ↑p < 2
  have hp : Nat.primesBelow 9 = {2, 3, 5, 7} := by decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9]

theorem psi_sub_theta_nat_35_lt_eight :
    Chebyshev.psi (35 : Real) - Chebyshev.theta 35 < 8 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 35
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 35
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesLE 35,
      ↑(Nat.log p 35) * Real.log ↑p) -
    ∑ p ∈ Nat.primesLE 35, Real.log ↑p < 8
  have hp : Nat.primesLE 35 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  ring_nf
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt]

theorem psi_sub_theta_nat_63_lt_nine :
    Chebyshev.psi (63 : Real) - Chebyshev.theta 63 < 9 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 63
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 63
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesLE 63,
      ↑(Nat.log p 63) * Real.log ↑p) -
    ∑ p ∈ Nat.primesLE 63, Real.log ↑p < 9
  have hp : Nat.primesLE 63 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  ring_nf
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt]

theorem dusart_proposition_3_2_small_64
    {x : Real} (hx : 0 < x) (hx64 : x < 64) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have htransport : Chebyshev.psi x - Chebyshev.theta x =
      Chebyshev.psi (⌊x⌋₊ : Real) - Chebyshev.theta (⌊x⌋₊ : Real) := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.theta_eq_theta_coe_floor]
  by_cases h9 : x < 9
  · by_cases h4 : x < 4
    · have hzero : Chebyshev.psi x - Chebyshev.theta x = 0 := by
        have hf : ⌊x⌋₊ < 4 := (Nat.floor_lt hx.le).2 h4
        have hfloor : (⌊x⌋₊ : Real) ≤ 3 := by
          exact_mod_cast Nat.le_of_lt_succ hf
        have hupper : Chebyshev.psi x - Chebyshev.theta x ≤ 0 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_eq
            psi_sub_theta_nat_3_eq_zero
        have hnonneg : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
          exact sub_nonneg.mpr (Chebyshev.theta_le_psi x)
        exact le_antisymm hupper hnonneg
      rw [hzero]
      positivity
    · have hx4 : (4 : Real) ≤ x := le_of_not_gt h4
      have hfloor : (⌊x⌋₊ : Real) ≤ 8 := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by norm_num; exact h9))
      have hleft : Chebyshev.psi x - Chebyshev.theta x < 2 := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_8_lt_two
      have hsqrt : (2 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
      nlinarith [hleft, hsqrt,
        Real.rpow_nonneg (show 0 ≤ x by linarith) (1 / 3 : Real)]
  · have hx9 : (9 : Real) ≤ x := le_of_not_gt h9
    by_cases h25 : x < 25
    · have hfloor : (⌊x⌋₊ : Real) ≤ 24 := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by norm_num; exact h25))
      have hleft : Chebyshev.psi x - Chebyshev.theta x < 4 := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_24_lt_four
      have hsqrt : (3 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
      have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
        have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
          (by linarith : (8 : Real) ≤ x)
          (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
        norm_num at hpow ⊢
        exact hpow
      nlinarith [hleft, hsqrt, hcuberoot]
    · have hx25 : (25 : Real) ≤ x := le_of_not_gt h25
      by_cases h36 : x < 36
      · have hfloor : (⌊x⌋₊ : Real) ≤ 35 := by
          exact_mod_cast Nat.le_of_lt_succ
            ((Nat.floor_lt hx.le).2 (by norm_num; exact h36))
        have hleft : Chebyshev.psi x - Chebyshev.theta x < 8 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_35_lt_eight
        have hsqrt : (5 : Real) ≤ Real.sqrt x := by
          nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
        have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
          have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
            (by linarith : (8 : Real) ≤ x)
            (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
          norm_num at hpow ⊢
          exact hpow
        nlinarith [hleft, hsqrt, hcuberoot]
      · have hx36 : (36 : Real) ≤ x := le_of_not_gt h36
        have hfloor : (⌊x⌋₊ : Real) ≤ 63 := by
          exact_mod_cast Nat.le_of_lt_succ
            ((Nat.floor_lt hx.le).2 (by norm_num; exact hx64))
        have hleft : Chebyshev.psi x - Chebyshev.theta x < 9 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_63_lt_nine
        have hsqrt : (6 : Real) ≤ Real.sqrt x := by
          nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
        have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
          have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
            (by linarith : (8 : Real) ≤ x)
            (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
          norm_num at hpow ⊢
          exact hpow
        nlinarith [hleft, hsqrt, hcuberoot]

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
  have hupper : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260 := by
    intro y hy
    have h := thetaBounds.1 y hy
    nlinarith
  exact dusart_proposition_3_2_of_paper_lemma_and_theta_upper
    hlemma hupper

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
theorem dusart_lemma_3_3_large
    {x : Real} (hx : (10 ^ 11 : Real) ^ 3 ≤ x)
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
  have hsum_rpow := dusart_prime_power_rpow_sum_le
    (x := x) (by linarith [hx]) hN3
  have hcount := dusart_floor_log_div_two_le_rpow hx
  have hxpos : 0 < x := by positivity
  have htail : ((N : Real) - 3) * x ^ (1 / (4 : Real)) ≤
      (7 : Real) / 10 * x ^ (1 / (3 : Real)) := by
    have hNnonneg : 0 ≤ (N : Real) - 3 := by exact_mod_cast Nat.zero_le (N - 3)
    have hpow4 : 0 ≤ x ^ (1 / (4 : Real)) := by positivity
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
        rw [← Real.rpow_add hxpos]
        congr 1
        norm_num
  have hsum17 :
      ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
        (17 : Real) / 10 * x ^ (1 / (3 : Real)) := by
    calc
      ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
          x ^ (1 / (3 : Real)) +
            ((N : Real) - 3) * x ^ (1 / (4 : Real)) := hsum_rpow
      _ ≤ x ^ (1 / (3 : Real)) +
          (7 : Real) / 10 * x ^ (1 / (3 : Real)) :=
        add_le_add le_rfl htail
      _ = (17 : Real) / 10 * x ^ (1 / (3 : Real)) := by ring
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

/-! Global Lemma 3.3 assembled from the paper's bounded direct computation
and the analytic tail above. -/
theorem dusart_lemma_3_3_of_finite_and_theta_upper
    {X : Real} (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (finite : ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx
  by_cases hle : x ≤ X
  · exact finite x hx hle
  · have hcut : ¬ x ≤ (10 ^ 11 : Real) ^ 3 := by
      intro hcut
      exact hle (hcut.trans hX)
    exact dusart_lemma_3_3_large (le_of_not_ge hcut) theta_upper

theorem dusart_proposition_3_2_of_finite_lemma_and_theta_upper
    {X : Real} (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (finite : ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (theta_error : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / (3 : Real)) := by
  apply dusart_proposition_3_2_of_paper_lemma_and_theta_upper
  · apply dusart_lemma_3_3_of_finite_and_theta_upper hX finite
    intro y hy
    have h := theta_error y hy
    nlinarith
  · exact theta_error

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
