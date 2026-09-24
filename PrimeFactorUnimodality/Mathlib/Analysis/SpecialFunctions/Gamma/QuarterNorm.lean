/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.BetaNorm
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.HalfIntegerNorm

/-! # A uniform compensated Gamma bound on the quarter line

The Beta-integral norm bound compares real parts one quarter and three
quarters. Legendre duplication and the exact half-line estimate then bound
the quarter-line Gamma factor at every signed height.
-/

namespace Complex

/-- Duplication bounds the compensated product on the two quarter lines. -/
theorem norm_Gamma_quarter_mul_three_quarters_mul_exp_le (t : ℝ) :
    ‖Gamma ((1 / 4 : ℂ) + (t : ℂ) * I)‖ *
      ‖Gamma ((3 / 4 : ℂ) + (t : ℂ) * I)‖ * Real.exp (Real.pi * t) ≤ 2 * Real.pi := by
  have hd := congrArg norm (Gamma_mul_Gamma_add_half ((1 / 4 : ℂ) + (t : ℂ) * I))
  have ha : (1 / 4 : ℂ) + (t : ℂ) * I + 1 / 2 = 3 / 4 + (t : ℂ) * I := by ring
  have hb : 2 * ((1 / 4 : ℂ) + (t : ℂ) * I) = 1 / 2 + ((2 * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [ha, hb, norm_mul, norm_mul, norm_mul] at hd
  have hc : ‖(2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I))‖ =
      Real.sqrt 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl,
      norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num [← Real.sqrt_eq_rpow]
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_assoc, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hd
  rw [hd]
  have hhalf := norm_Gamma_half_add_mul_I_mul_exp_le (2 * t)
  have he : Real.pi * (2 * t) / 2 = Real.pi * t := by ring
  rw [he] at hhalf
  calc
    _ = (‖Gamma ((1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ *
          Real.exp (Real.pi * t)) * Real.sqrt (2 * Real.pi) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hhalf (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (by positivity)

/-- A height-independent bound for the compensated quarter-line Gamma factor. -/
theorem norm_Gamma_quarter_add_mul_I_mul_exp_le (t : ℝ) :
    ‖Gamma ((1 / 4 : ℂ) + (t : ℂ) * I)‖ * Real.exp (Real.pi * t / 2) ≤
      Real.sqrt (2 * Real.pi * (Real.Gamma (1 / 4) / Real.Gamma (3 / 4))) := by
  have hratio := norm_Gamma_div_norm_Gamma_add_real_le
    (s := (1 / 4 : ℂ) + (t : ℂ) * I) (by norm_num) (a := 1 / 2) (by norm_num)
  have ha : (1 / 4 : ℂ) + (t : ℂ) * I + ((1 / 2 : ℝ) : ℂ) =
      3 / 4 + (t : ℂ) * I := by push_cast; ring
  rw [ha, show ((1 / 4 : ℂ) + (t : ℂ) * I).re = (1 / 4 : ℝ) by norm_num,
    show (1 / 4 : ℝ) + 1 / 2 = 3 / 4 by norm_num] at hratio
  have hn : 0 < ‖Gamma ((3 / 4 : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by norm_num))
  have hcompare := (div_le_iff₀ hn).mp hratio
  have hr : 0 ≤ Real.Gamma (1 / 4) / Real.Gamma (3 / 4) := by positivity
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  have he : Real.exp (Real.pi * t / 2) ^ 2 = Real.exp (Real.pi * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, he, Real.sq_sqrt (by positivity)]
  calc
    _ ≤ (Real.Gamma (1 / 4) / Real.Gamma (3 / 4)) *
        (‖Gamma ((1 / 4 : ℂ) + (t : ℂ) * I)‖ *
          ‖Gamma ((3 / 4 : ℂ) + (t : ℂ) * I)‖ * Real.exp (Real.pi * t)) := by
      have h := mul_le_mul_of_nonneg_left hcompare
        (mul_nonneg (norm_nonneg (Gamma ((1 / 4 : ℂ) + (t : ℂ) * I)))
          (Real.exp_pos (Real.pi * t)).le)
      nlinarith
    _ ≤ (Real.Gamma (1 / 4) / Real.Gamma (3 / 4)) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left (norm_Gamma_quarter_mul_three_quarters_mul_exp_le t) hr
    _ = _ := by ring

end Complex

namespace Real

/-- Log-convexity between one and two bounds the quarter value by recurrence. -/
theorem Gamma_one_quarter_le_four : Gamma (1 / 4) ≤ 4 := by
  have hc := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (s := 1) (t := 2) (a := 3 / 4) (b := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hc
  have hr := Gamma_add_one (s := 1 / 4) (by norm_num)
  norm_num at hr
  linarith

/-- A rational upper bound for the compensated quarter-line constant, with no numerical oracle. -/
theorem sqrt_Gamma_quarter_ratio_le_five :
    sqrt (2 * Real.pi * (Gamma (1 / 4) / Gamma (3 / 4))) ≤ 5 := by
  have hprod : Gamma (1 / 4) * Gamma (3 / 4) = sqrt 2 * Real.pi := by
    have hd := Gamma_mul_Gamma_add_half (1 / 4)
    norm_num [Gamma_one_half_eq, ← sqrt_eq_rpow] at hd
    calc
      _ = sqrt Real.pi * sqrt 2 * sqrt Real.pi := hd
      _ = sqrt 2 * (sqrt Real.pi * sqrt Real.pi) := by ring
      _ = _ := by rw [mul_self_sqrt pi_pos.le]
  have hg : 0 < Gamma (1 / 4) := Gamma_pos_of_pos (by norm_num)
  have hg' : 0 < Gamma (3 / 4) := Gamma_pos_of_pos (by norm_num)
  have hs : (32 : ℝ) ≤ 25 * sqrt 2 := by
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sqrt_nonneg 2]
  have hcross : 2 * Real.pi * Gamma (1 / 4) ≤ 25 * Gamma (3 / 4) := by
    apply (mul_le_mul_iff_of_pos_right hg).mp
    calc
      _ = 2 * Real.pi * Gamma (1 / 4) ^ 2 := by ring
      _ ≤ 2 * Real.pi * 4 ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le Gamma_one_quarter_le_four 2)
          (by positivity)
      _ ≤ 25 * (sqrt 2 * Real.pi) := by
        nlinarith [mul_le_mul_of_nonneg_right hs pi_pos.le]
      _ = _ := by rw [← hprod]; ring
  apply (sq_le_sq₀ (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)).mp
  rw [sq_sqrt (by positivity), ← mul_div_assoc]
  exact (div_le_iff₀ hg').mpr (by
    simpa only [show (5 : ℝ) ^ 2 = 25 by norm_num] using hcross)

end Real

namespace Complex

/-- A rational compensated Gamma bound suitable for polynomial Gaussian estimates. -/
theorem norm_Gamma_quarter_add_mul_I_mul_exp_le_five (t : ℝ) :
    ‖Gamma ((1 / 4 : ℂ) + (t : ℂ) * I)‖ * Real.exp (Real.pi * t / 2) ≤ 5 :=
  (norm_Gamma_quarter_add_mul_I_mul_exp_le t).trans Real.sqrt_Gamma_quarter_ratio_le_five

end Complex
