import PrimeFactorUnimodality.Helpers.Analytic.DigammaExplicitBounds

set_option autoImplicit false

/-! # Lower and absolute real-part bounds for digamma

The terms of the real digamma series are nonnegative when `Re(z) >= 1`.
Recurrence moves any point of the right half-plane to that region. Together
with the explicit upper bound this controls the absolute real part on the
quarter-line used by the smoothed explicit formula's gamma integral.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

private theorem re_inv_le_inv_re {z : ℂ} (hz : 0 < z.re) :
    z⁻¹.re ≤ z.re⁻¹ := by
  have hz₀ : z ≠ 0 := by intro h; simp [h] at hz
  rw [inv_re, inv_eq_one_div]
  apply (div_le_div_iff₀ (normSq_pos.mpr hz₀) hz).mpr
  simpa only [one_mul, ← pow_two] using re_sq_le_normSq z

/-- The real part is bounded below by the value at one on the closed right half-plane. -/
theorem neg_eulerMascheroni_le_re_digamma {z : ℂ} (hz : 1 ≤ z.re) :
    -Real.eulerMascheroniConstant ≤ (digamma z).re := by
  have hsum := Complex.hasSum_re
    (Complex.hasSum_digamma_of_re_pos (lt_of_lt_of_le zero_lt_one hz))
  have hterms (n : ℕ) : 0 ≤ (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹).re := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hzn : 0 < (z + n).re := by simp only [add_re, natCast_re]; positivity
    have hi := (re_inv_le_inv_re hzn).trans (inv_anti₀ hn (by
      simp only [add_re, natCast_re]; linarith))
    have hre : (((n : ℂ) + 1)⁻¹).re = ((n : ℝ) + 1)⁻¹ := by
      rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
        ← ofReal_inv, ofReal_re]
    rw [sub_re, hre]
    linarith
  have hnonneg : 0 ≤ ∑' n : ℕ, (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹).re :=
    tsum_nonneg hterms
  rw [hsum.tsum_eq] at hnonneg
  simp only [add_re, ofReal_re] at hnonneg
  linarith

/-- Recurrence supplies a lower bound throughout the open right half-plane. -/
theorem re_digamma_lower_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    -Real.eulerMascheroniConstant - z.re⁻¹ ≤ (digamma z).re := by
  have hpoles : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h := neg_eulerMascheroni_le_re_digamma (z := z + 1) (by simp; linarith)
  rw [digamma_apply_add_one z hpoles, add_re] at h
  linarith [re_inv_le_inv_re hz]

/-- A two-sided bound without unspecified constants. -/
theorem abs_re_digamma_le_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    |(digamma z).re| ≤ Real.log (‖z‖ + 2) + 1 +
      |Real.eulerMascheroniConstant| + z.re⁻¹ := by
  have hpoles : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hu := re_digamma_le_log_norm_sub_one_add_two (z := z + 1) (by simp; linarith)
  rw [digamma_apply_add_one z hpoles, add_re, add_sub_cancel_right] at hu
  have hi : 0 ≤ (z⁻¹).re := by rw [inv_re]; exact div_nonneg hz.le (normSq_nonneg z)
  have hl := re_digamma_lower_of_re_pos hz
  have hlog : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg z])
  exact abs_le.mpr ⟨by linarith [le_abs_self Real.eulerMascheroniConstant],
    by linarith [abs_nonneg Real.eulerMascheroniConstant, inv_pos.mpr hz]⟩

/-- The gamma integration line has an explicit logarithmic absolute real-part bound. -/
theorem abs_re_digamma_quarter_line_le (t : ℝ) :
    |(digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re| ≤
      Real.log (|t| + 3) + |Real.eulerMascheroniConstant| + 5 := by
  let z : ℂ := ((1 / 2 : ℂ) + (t : ℂ) * I) / 2
  have hre : z.re = 1 / 4 := by simp [z]; norm_num
  have him : z.im = t / 2 := by simp [z]
  have h := abs_re_digamma_le_of_re_pos (z := z) (by rw [hre]; norm_num)
  have hn := norm_le_abs_re_add_abs_im z
  simp only [hre, him, abs_div] at hn
  norm_num at hn
  have hlog : Real.log (‖z‖ + 2) ≤ Real.log (|t| + 3) :=
    Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  rw [hre] at h
  norm_num at h
  linarith

end

end PrimeFactorUnimodality
