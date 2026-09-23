import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoffScalars
import PrimeFactorUnimodality.Mathlib.NumberTheory.Chebyshev.PsiBounds

/-! # A sharper elementary prime-power correction above three billion

The square-root and cube-root arguments already lie on rays where the
elementary psi bound is much stronger than its global constant. Costa-Pereira's
three-root inequality then costs at most 8/5 times the square root.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

private theorem exp_two_le_nine : exp 2 ≤ (9 : ℝ) := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
  nlinarith [exp_one_lt_d9, exp_pos 1]

private theorem log_four_le : log (4 : ℝ) ≤ (139 / 100 : ℝ) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  norm_num
  linarith [log_two_lt_d9]

/-- The elementary psi bound has coefficient 3/2 from forty thousand onward. -/
theorem psi_le_three_halves_mul {y : ℝ} (hy : 40000 ≤ y) :
    ψ y ≤ (3 / 2 : ℝ) * y := by
  have hl : log (40000 : ℝ) ≤ (53 / 5 : ℝ) := by
    rw [show (40000 : ℝ) = 4 * 10 ^ 4 by norm_num,
      log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
    have hfour : log (4 : ℝ) ≤ (1387 / 1000 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      norm_num
      linarith [log_two_lt_d9]
    linarith [dusart_log_ten_bounds.2]
  have hp := psi_le_mul_of_sqrt_cutoff (a := 40000) (r := 200)
    (by linarith [exp_two_le_nine]) hy (by norm_num) (by norm_num) (by norm_num) hl
  exact hp.trans (mul_le_mul_of_nonneg_right (by linarith [log_four_le]) (by linarith))

/-- The elementary psi bound has coefficient two from one thousand onward. -/
theorem psi_le_two_mul_from_thousand {y : ℝ} (hy : 1000 ≤ y) : ψ y ≤ 2 * y := by
  have hl : log (1000 : ℝ) ≤ 7 := by
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, log_pow]
    norm_num
    linarith [dusart_log_ten_bounds.2]
  have hp := psi_le_mul_of_sqrt_cutoff (a := 1000) (r := 30)
    (by linarith [exp_two_le_nine]) hy (by norm_num) (by norm_num) (by norm_num) hl
  exact hp.trans (mul_le_mul_of_nonneg_right (by linarith [log_four_le]) (by linarith))

/-- A power comparison supplies an exact rational lower bound for a positive root. -/
private theorem root_lower {x r : ℝ} {n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hx : r ^ n ≤ x) : r ≤ x ^ (1 / (n : ℝ)) := by
  have hxpos : 0 < x := (pow_pos hr n).trans_le hx
  apply le_rpow_of_log_le hxpos
  have hl := log_le_log (pow_pos hr n) hx
  rw [log_pow] at hl
  have hl' : log r ≤ log x / (n : ℝ) :=
    (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr (by nlinarith)
  exact hl'.trans_eq (by ring)

/-- The sharper correction holds on the entire ray, not only at sampled points. -/
theorem psi_sub_theta_le_sharper_root {x : ℝ} (hx : (3000000000 : ℝ) ≤ x) :
    ψ x - θ x ≤ (8 / 5 : ℝ) * exp (log x / 2) := by
  have hxpos : 0 < x := by linarith
  have hb : 0 ≤ log x := log_nonneg (by linarith)
  have hs := root_lower (r := 40000) (n := 2) (by norm_num) (by norm_num)
    (by nlinarith : (40000 : ℝ) ^ 2 ≤ x)
  have hc := root_lower (r := 1000) (n := 3) (by norm_num) (by norm_num)
    (by nlinarith : (1000 : ℝ) ^ 3 ≤ x)
  have hpsi := add_le_add (add_le_add (psi_le_three_halves_mul hs)
    (psi_le_two_mul_from_thousand hc)) (psi_le_const_mul_self
      (show 0 ≤ x ^ (1 / 5 : ℝ) by positivity))
  have hmain := (psi_sub_theta_le_psi_add_psi_add_psi x).trans (by
    simpa only [one_div, Nat.cast_ofNat] using hpsi)
  simp only [rpow_def_of_pos hxpos] at hmain
  have hsmall : exp (-log x / 6) ≤ (1 / 37 : ℝ) := by
    have hl := log_le_log (by norm_num : (0 : ℝ) < 37 ^ 6)
      (by nlinarith : (37 : ℝ) ^ 6 ≤ x)
    rw [log_pow] at hl
    have he := exp_le_exp.mpr (show -log x / 6 ≤ -log 37 by norm_num at hl; linarith)
    simpa only [exp_neg, exp_log (by norm_num : (0 : ℝ) < 37), one_div] using he
  have hquarter : exp (-log x / 4) ≤ (1 / 230 : ℝ) := by
    have hl := log_le_log (by norm_num : (0 : ℝ) < 230 ^ 4)
      (by nlinarith : (230 : ℝ) ^ 4 ≤ x)
    rw [log_pow] at hl
    have he := exp_le_exp.mpr (show -log x / 4 ≤ -log 230 by norm_num at hl; linarith)
    simpa only [exp_neg, exp_log (by norm_num : (0 : ℝ) < 230), one_div] using he
  have hthird : exp (log x * (3 : ℝ)⁻¹) ≤ exp (log x / 2) / 37 := by
    rw [show log x * (3 : ℝ)⁻¹ = log x / 2 + -log x / 6 by ring, exp_add]
    exact (mul_le_mul_of_nonneg_left hsmall (exp_pos _).le).trans_eq (by ring)
  have hfifth : exp (log x * (5 : ℝ)⁻¹) ≤ exp (log x / 2) / 230 := by
    have he := (exp_le_exp.mpr (show -3 * log x / 10 ≤ -log x / 4 by linarith)).trans hquarter
    rw [show log x * (5 : ℝ)⁻¹ = log x / 2 + -3 * log x / 10 by ring, exp_add]
    exact (mul_le_mul_of_nonneg_left he (exp_pos _).le).trans_eq (by ring)
  have hcoeff : (log 4 + 4) * exp (log x * (5 : ℝ)⁻¹) ≤
      (27 / 5 : ℝ) * exp (log x / 2) / 230 := by
    calc
      _ ≤ (log 4 + 4) * (exp (log x / 2) / 230) :=
        mul_le_mul_of_nonneg_left hfifth (by positivity)
      _ ≤ (27 / 5 : ℝ) * (exp (log x / 2) / 230) :=
        mul_le_mul_of_nonneg_right (by linarith [log_four_le]) (by positivity)
      _ = _ := by ring
  have hhalf : exp (log x * (2 : ℝ)⁻¹) = exp (log x / 2) := by rw [div_eq_mul_inv]
  rw [hhalf] at hmain
  nlinarith only [hmain, hthird, hcoeff, exp_pos (log x / 2)]

/-- Normalize the correction using only a rational square comparison. -/
theorem abs_theta_sub_div_le_sharper_root {x r ε : ℝ}
    (hx : (3000000000 : ℝ) ≤ x) (hr : 0 < r) (hrx : r ^ 2 ≤ x)
    (hpsi : |ψ x - x| / x ≤ ε) : |θ x - x| / x ≤ ε + (8 / 5) / r := by
  have hxpos : 0 < x := by linarith
  have hl := log_le_log (pow_pos hr 2) hrx
  rw [log_pow] at hl
  have he : exp (-log x / 2) ≤ 1 / r := by
    have h := exp_le_exp.mpr (show -log x / 2 ≤ -log r by norm_num at hl; linarith)
    simpa only [exp_neg, exp_log hr, one_div] using h
  have hi : exp (log x / 2) / x = exp (-log x / 2) := by
    calc
      _ = exp (log x / 2) / exp (log x) := by rw [exp_log hxpos]
      _ = exp (-log x / 2) := by rw [← exp_sub]; congr 1; ring
  have hroot := div_le_div_of_nonneg_right (psi_sub_theta_le_sharper_root hx) hxpos.le
  rw [mul_div_assoc, hi] at hroot
  have hroot' : (ψ x - θ x) / x ≤ (8 / 5) / r := hroot.trans
    ((mul_le_mul_of_nonneg_left he (by norm_num)).trans_eq (by ring))
  have hp := abs_le.mp ((div_le_iff₀ hxpos).mp hpsi)
  have hc := (div_le_iff₀ hxpos).mp hroot'
  apply (div_le_iff₀ hxpos).mpr
  apply abs_le.mpr
  have hn := mul_nonneg (show 0 ≤ (8 / 5 : ℝ) / r by positivity) hxpos.le
  constructor <;> nlinarith only [hp.1, hp.2, hc, theta_le_psi x, hn]

end

end PrimeFactorUnimodality
