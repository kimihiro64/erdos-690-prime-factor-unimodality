import PrimeFactorUnimodality.Helpers.Analytic.DigammaLogBounds

/-! # A height-decaying explicit digamma error

Reuse the exact reciprocal Euler--Maclaurin remainder and its actual
digamma limit. On the right half-plane, `norm(z+x)^2` is at least
`(norm(z)+x)^2/2`. Integrating this majorant gives `2/norm(z)` for the
finite error and hence for `digamma(z)-log(z)`. This bound decays at large
imaginary height, unlike the earlier `1/Re(z)` bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

private theorem norm_add_real_ge {z : ℂ} (hz : 0 ≤ z.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖z‖ ≤ ‖z + x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero]
  nlinarith [mul_nonneg hz hx]

private theorem sq_norm_add_real_ge {z : ℂ} (hz : 0 ≤ z.re) {x : ℝ} (hx : 0 ≤ x) :
    (‖z‖ + x) ^ 2 ≤ 2 * ‖z + x‖ ^ 2 := by
  have he : ‖z + x‖ ^ 2 = ‖z‖ ^ 2 + 2 * z.re * x + x ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero]
    ring
  rw [he]
  nlinarith [sq_nonneg (‖z‖ - x), mul_nonneg hz hx]

/-- The same finite reciprocal-sum error has a bound decaying with the full complex norm. -/
theorem norm_sum_inv_add_sub_log_le_inv_norm {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖(∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹) -
      (Complex.log (z + (N : ℂ)) - Complex.log z)‖ ≤ 2 / ‖z‖ := by
  have hr : 0 < ‖z‖ := hz.trans_le (re_le_norm z)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hir : IntervalIntegrable (fun x : ℝ => ((‖z‖ + x) ^ 2)⁻¹) volume 0 (N : ℝ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hN
    exact ((by fun_prop : ContinuousOn (fun x : ℝ => ‖z‖ + x) (Icc 0 (N : ℝ))).pow 2).inv₀
      (fun x hx => pow_ne_zero 2 (by linarith [hx.1] : ‖z‖ + x ≠ 0))
  have hInt : (∫ x in (0 : ℝ)..N, ((‖z‖ + x) ^ 2)⁻¹) =
      1 / ‖z‖ - 1 / (‖z‖ + N) := by
    have hd (x : ℝ) (hx : x ∈ uIcc 0 (N : ℝ)) :
        HasDerivAt (fun y : ℝ => -(‖z‖ + y)⁻¹) ((‖z‖ + x) ^ 2)⁻¹ x := by
      rw [uIcc_of_le hN] at hx
      convert! (((hasDerivAt_id x).const_add ‖z‖).inv
        (by linarith [hx.1] : ‖z‖ + x ≠ 0)).neg using 1
      simp only [id_eq, neg_div, one_div, neg_neg]
    simpa [one_div, sub_eq_add_neg, add_comm] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hir
  have hR : ‖∫ x in (0 : ℝ)..N, -((z + x) ^ 2)⁻¹ * (B1 x : ℂ)‖ ≤
      1 / ‖z‖ - 1 / (‖z‖ + N) := by
    rw [← hInt]
    apply intervalIntegral.norm_integral_le_of_norm_le hN _ hir
    filter_upwards with x hx
    simp only [norm_mul, norm_neg, norm_inv, norm_pow, norm_real, Real.norm_eq_abs]
    have hx₀ : 0 ≤ x := hx.1.le
    have hn : (‖z + x‖ ^ 2)⁻¹ ≤ 2 * ((‖z‖ + x) ^ 2)⁻¹ := by
      have hp : 0 < ‖z + x‖ := hr.trans_le (norm_add_real_ge hz.le hx₀)
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (sq_pos_of_pos hp)
        (sq_pos_of_pos (by linarith : 0 < ‖z‖ + x))]
      simpa using sq_norm_add_real_ge hz.le hx₀
    have hb := mul_le_mul hn (abs_B1_le_half hx₀) (abs_nonneg (B1 x)) (by positivity)
    nlinarith only [hb]
  rw [sum_inv_add_sub_log_eq_euler hz N]
  have hEnd : ‖(z⁻¹ + (z + (N : ℂ))⁻¹) / 2‖ ≤ 1 / ‖z‖ := by
    have hn : ‖(z + (N : ℂ))⁻¹‖ ≤ ‖z‖⁻¹ := by
      rw [norm_inv]
      exact inv_anti₀ hr (by simpa using norm_add_real_ge hz.le hN)
    rw [norm_div, norm_ofNat]
    have he := norm_add_le z⁻¹ (z + (N : ℂ))⁻¹
    rw [norm_inv] at he
    rw [one_div]
    linarith
  have he := (norm_add_le _ _).trans (add_le_add hEnd hR)
  have hp : 0 ≤ 1 / (‖z‖ + (N : ℝ)) := by positivity
  simp only [div_eq_mul_inv, one_mul] at he hp ⊢
  linarith only [he, hp]

/-- An explicit approximation that tends to zero as the imaginary height grows. -/
theorem norm_digamma_sub_log_le_inv_norm {z : ℂ} (hz : 0 < z.re) :
    ‖digamma z - Complex.log z‖ ≤ 2 / ‖z‖ :=
  le_of_tendsto (tendsto_norm_sum_inv_add_sub_log hz)
    (Filter.Eventually.of_forall (norm_sum_inv_add_sub_log_le_inv_norm hz))

/-- The height-decaying complex estimate bounds both sides of the real part. -/
theorem abs_re_digamma_sub_log_norm_le_inv_norm {z : ℂ} (hz : 0 < z.re) :
    |(digamma z).re - Real.log ‖z‖| ≤ 2 / ‖z‖ := by
  simpa only [sub_re, Complex.log_re] using
    (abs_re_le_norm (digamma z - Complex.log z)).trans (norm_digamma_sub_log_le_inv_norm hz)

end

end PrimeFactorUnimodality
