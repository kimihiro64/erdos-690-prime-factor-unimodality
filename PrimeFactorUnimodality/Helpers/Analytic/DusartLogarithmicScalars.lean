import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.PiBounds

/-! # Scalar bounds for a decreasing logarithmic psi error

Above logarithmic height fifty, a small interval of relative smoothing
steps controls the width and the cubic reciprocal cost. Taylor monomials
bound the low-zero exponential decay and the elementary correction.
These inequalities contain no zero-location assumptions.
-/

namespace PrimeFactorUnimodality

open Real

/-- Fourth-order Taylor decay for the half-logarithmic exponential. -/
theorem dusartLog_half_exp_le {b : ℝ} (hb : 0 < b) :
    exp (-b / 2) ≤ 384 / b ^ 4 := by
  have he := Real.pow_div_factorial_le_exp (b / 2) (by positivity) 4
  have hi := one_div_le_one_div_of_le
    (by positivity : 0 < (b / 2) ^ 4 / ((4 : ℕ).factorial : ℝ)) he
  rw [show -b / 2 = -(b / 2) by ring, Real.exp_neg]
  rw [one_div] at hi
  refine hi.trans_eq ?_
  norm_num
  field_simp
  norm_num

/-- The low block's numerical coefficient fits within a logarithmic allowance. -/
theorem dusartLog_low_le {b : ℝ} (hb : 50 ≤ b) :
    77 * exp (-b / 2) ≤ (6 / 25 : ℝ) / b := by
  have hbpos : 0 < b := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 50) hb 3
  calc
    _ ≤ 77 * (384 / b ^ 4) := mul_le_mul_of_nonneg_left
      (dusartLog_half_exp_le hbpos) (by norm_num)
    _ = 29568 / b ^ 4 := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (pow_pos hbpos 4) hbpos).mpr
      nlinarith only [hbpos, mul_nonneg (by linarith : 0 ≤ b ^ 3 - 50 ^ 3) hbpos.le]

/-- The relative smoothing window keeps the total width below eleven tenths. -/
theorem dusartLog_width_le {b s : ℝ} (hb : 50 ≤ b) (hs : s ≤ 1 / (20 * b)) :
    1 + 3 * s ≤ (11 / 10 : ℝ) := by
  have hden : (1000 : ℝ) ≤ 20 * b := by linarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000) hden
  linarith

/-- The high-block cubic smoothing coefficient has a uniform polynomial bound. -/
theorem dusartLog_coefficient_le {b s : ℝ} (hb : 50 ≤ b)
    (hs₀ : 1 / (60 * b) ≤ s) (hs₁ : s ≤ 1 / (20 * b)) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ 8 * (11 / 10 : ℝ) ^ 4 * (60 * b) ^ 3 := by
  have hbpos : 0 < b := by linarith
  have hspos : 0 < s := (by positivity : 0 < 1 / (60 * b)).trans_le hs₀
  have hn := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 3 * s)
    (dusartLog_width_le hb hs₁) 4
  have hd := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (60 * b)) hs₀ 3
  calc
    _ ≤ 8 * (11 / 10 : ℝ) ^ 4 / s ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
    _ ≤ 8 * (11 / 10 : ℝ) ^ 4 / (1 / (60 * b)) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
    _ = _ := by field_simp

/-- The complete polynomial high-tail constant fits within its logarithmic allowance. -/
theorem dusartLog_high_le {b : ℝ} (hb : 0 < b) :
    (8 * (11 / 10 : ℝ) ^ 4 * (60 * b) ^ 3) *
      (576 / (b / 56) ^ 4) * (4 / 10 ^ 18) ≤ (3 / 50 : ℝ) / b := by
  apply (le_div_iff₀ hb).mpr
  have he : (8 * (11 / 10 : ℝ) ^ 4 * (60 * b) ^ 3) *
      (576 / (b / 56) ^ 4) * (4 / 10 ^ 18) * b =
      8 * (11 / 10 : ℝ) ^ 4 * 60 ^ 3 * 576 * 56 ^ 4 * (4 / 10 ^ 18) := by
    field_simp
  rw [he]
  norm_num

/-- The normalized elementary correction is at most four over the base point. -/
theorem dusartLog_correction_le {x : ℝ} (hx : 2 ≤ x) :
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x ≤ 4 / x := by
  have hd : 1 ≤ 2 * (x ^ 2 - 1) := by nlinarith
  have hr : 1 / (2 * (x ^ 2 - 1)) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
  have hl : Real.log (2 * π) ≤ 3 := by
    have h := Real.log_le_log (by positivity : 0 < 2 * π)
      (by linarith [pi_lt_four] : 2 * π ≤ 2 ^ 3)
    rw [Real.log_pow] at h
    norm_num at h
    linarith [Real.log_two_lt_d9]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- The elementary correction also has a decreasing logarithmic allowance. -/
theorem dusartLog_four_div_exp_le {b : ℝ} (hb : 50 ≤ b) :
    4 / exp b ≤ (4 / 25 : ℝ) / b := by
  have hbpos : 0 < b := by linarith
  have he := Real.pow_div_factorial_le_exp b hbpos.le 2
  norm_num at he
  calc
    _ ≤ 4 / (b ^ 2 / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) he
    _ ≤ _ := by
      apply (le_div_iff₀ hbpos).mpr
      have hid : 4 / (b ^ 2 / 2) * b = 8 / b := by field_simp; ring
      rw [hid]
      exact (div_le_iff₀ hbpos).mpr (by linarith)

end PrimeFactorUnimodality
