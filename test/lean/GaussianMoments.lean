import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.PolynomialMoments

/-! The exact moments include order zero, odd orders, and arbitrary real shifts. -/

open MeasureTheory

example : (∫ x : ℝ, |x| ^ 0 * Real.exp (-(1 : ℝ) * x ^ 2)) = Real.sqrt Real.pi := by
  simpa only [Nat.cast_zero, zero_add, div_one, Real.one_rpow, one_mul,
    Real.Gamma_one_half_eq] using
    Real.integral_abs_pow_mul_exp_neg_mul_sq 0 (b := 1) (by norm_num)

example {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| * Real.exp (-b * x ^ 2)) = 1 / b := by
  simpa using Real.integral_abs_pow_mul_exp_neg_mul_sq 1 hb

example (a c : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (a + |x|) ^ 3 * (c + |x|) ^ 2 * Real.exp (-b * x ^ 2)) :=
  Real.integrable_add_abs_pow_mul_add_abs_pow_mul_exp_neg_mul_sq 3 2 a c hb

example {b s : ℝ} (hb : 0 < b) (hs : -1 < s) :
    (∫ x : ℝ in Set.Ioi 0, x ^ s * Real.exp (-b * x ^ 2)) =
      (1 / b) ^ ((s + 1) / 2) * Real.Gamma ((s + 1) / 2) / 2 :=
  Real.integral_rpow_mul_exp_neg_mul_sq_Ioi hb hs

example (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| ^ (n + 2) * Real.exp (-b * x ^ 2)) =
      ((n : ℝ) + 1) / (2 * b) * ∫ x : ℝ, |x| ^ n * Real.exp (-b * x ^ 2) :=
  Real.integral_abs_pow_mul_exp_neg_mul_sq_add_two n hb
