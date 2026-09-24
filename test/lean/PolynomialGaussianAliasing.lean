import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.PolynomialGaussianAliasing

/-! Check the global tangent, arbitrary orders and exact Gaussian alias normalization. -/

example (k : ℕ) {b R x : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-b * x ^ 2) ≤
      R ^ k * Real.exp (-b * R ^ 2) *
        Real.exp (((k : ℝ) / R - 2 * b * R) * (x - R)) :=
  Real.pow_mul_exp_neg_mul_sq_le_tangent k hb hR hx

example {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B / 2) :
    ‖(∑' n : ℤ, Real.exp (-(u + (n : ℝ) * B) ^ 2)) - Real.exp (-u ^ 2)‖ ≤
      2 * Real.exp (-(B / 2) ^ 2) / (1 - Real.exp (-B ^ 2)) := by
  simpa only [Nat.cast_zero, pow_zero, mul_zero, one_mul, mul_one, neg_mul,
    zero_sub] using Fourier.norm_periodization_sub_le_of_polynomialGaussian_bound
      0 (C := 1) (b := 1) (f := fun x : ℝ => Real.exp (-x ^ 2))
      (by norm_num) (by norm_num) hB (by simpa using sq_pos_of_pos hB) hu
      (fun x => by simp)
