import PrimeFactorUnimodality.Helpers.Analytic.DigammaEulerIdentity

/-! # A uniform reciprocal-sum error in the right half-plane

Apply the proved first-order Euler--Maclaurin identity to `1/(z+x)`.
The Bernoulli factor is bounded by one half, and the integral of the
derivative norm telescopes into real reciprocal endpoints. The resulting
bound is uniform in both the imaginary part and the truncation length.

The Euler--Maclaurin identity and Bernoulli bound are reused directly from
the pinned PNT revision `f6147e7572ab3abe5428101bc0b13627bcb005df`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

private theorem norm_inv_add_le {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖(z + x)⁻¹‖ ≤ 1 / (z.re + x) := by
  rw [norm_inv, one_div]
  exact inv_anti₀ (by linarith) (by simpa using re_le_norm (z + x))

/-- The finite reciprocal sum differs from its logarithmic integral by at most `1/Re(z)`. -/
theorem norm_sum_inv_add_sub_log_le {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖(∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹) -
      (Complex.log (z + (N : ℂ)) - Complex.log z)‖ ≤ 1 / z.re := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hir : IntervalIntegrable (fun x : ℝ => ((z.re + x) ^ 2)⁻¹) volume 0 (N : ℝ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hN
    exact ((by fun_prop : ContinuousOn (fun x : ℝ => z.re + x) (Icc 0 (N : ℝ))).pow 2).inv₀
      (fun x hx => pow_ne_zero 2 (by linarith [hx.1] : z.re + x ≠ 0))
  have hInt : (∫ x in (0 : ℝ)..N, ((z.re + x) ^ 2)⁻¹) =
      1 / z.re - 1 / (z.re + N) := by
    have hd (x : ℝ) (hx : x ∈ uIcc 0 (N : ℝ)) :
        HasDerivAt (fun y : ℝ => -(z.re + y)⁻¹) ((z.re + x) ^ 2)⁻¹ x := by
      rw [uIcc_of_le hN] at hx
      convert! (((hasDerivAt_id x).const_add z.re).inv
        (by linarith [hx.1] : z.re + x ≠ 0)).neg using 1
      simp only [id_eq, neg_div, one_div, neg_neg]
    simpa [one_div, sub_eq_add_neg, add_comm] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hir
  have hR : ‖∫ x in (0 : ℝ)..N, -((z + x) ^ 2)⁻¹ * (B1 x : ℂ)‖ ≤
      (1 / 2 : ℝ) * (1 / z.re - 1 / (z.re + N)) := by
    rw [← hInt, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hN _ (hir.const_mul (1 / 2))
    filter_upwards with x hx
    simp only [norm_mul, norm_neg, norm_inv, norm_pow, norm_real, Real.norm_eq_abs]
    have hn : ((‖z + x‖ ^ 2)⁻¹) ≤ ((z.re + x) ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos (by linarith [hx.1]))
        (pow_le_pow_left₀ (by linarith [hx.1]) (by simpa using re_le_norm (z + x)) 2)
    exact (mul_le_mul hn (abs_B1_le_half hx.1.le) (abs_nonneg _) (by positivity)).trans_eq
      (mul_comm _ _)
  rw [sum_inv_add_sub_log_eq_euler hz N]
  have hEnd : ‖(z⁻¹ + (z + (N : ℂ))⁻¹) / 2‖ ≤
      (1 / z.re + 1 / (z.re + N)) / 2 := by
    rw [norm_div, norm_ofNat]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (norm_add_le _ _).trans (add_le_add (by simpa using norm_inv_add_le hz le_rfl)
      (by simpa using norm_inv_add_le hz hN))
  exact (norm_add_le _ _).trans ((add_le_add hEnd hR).trans_eq (by ring))

end

end PrimeFactorUnimodality
