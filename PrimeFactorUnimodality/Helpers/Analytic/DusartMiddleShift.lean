import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleAverage

/-! # Adjacent smoothing geometry for the middle-range square-log step

The chosen relative step is eight hundredths of the reciprocal log square.
The lower base loses at most one logarithmic unit. Its relative step stays
in the evaluated window, with the true lower logarithm and normalization.
-/

namespace PrimeFactorUnimodality

open Real

/-- The actual lower base loses at most one logarithmic unit and less than one percent in size. -/
theorem dusartMiddle_shift_geometry {x : ℝ} (hx : 1 < x) (hb : 85 ≤ Real.log x) :
    let s := (2 / 25 : ℝ) / Real.log x ^ 2
    let t := 1 - 3 * s
    (99 / 100 : ℝ) ≤ t ∧ t ≤ 1 ∧ 1 < x * t ∧
      Real.log x - 1 ≤ Real.log (x * t) ∧ Real.log (x * t) ≤ Real.log x := by
  dsimp only
  let s := (2 / 25 : ℝ) / Real.log x ^ 2
  let t := 1 - 3 * s
  have hbpos : 0 < Real.log x := Real.log_pos hx
  have hspos : 0 < s := by dsimp [s]; positivity
  have hsmax : s ≤ (2 / 25 : ℝ) / 85 ^ 2 := div_le_div_of_nonneg_left
    (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 85) hb 2)
  have ht : (99 / 100 : ℝ) ≤ t := by dsimp [t]; linarith
  have htpos : 0 < t := by linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hy1 : 1 < x * t := by
    have he := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hxpos] at he
    have hm := mul_le_mul_of_nonneg_left ht hxpos.le
    nlinarith
  have hylog : Real.log (x * t) = Real.log x + Real.log t :=
    Real.log_mul hxpos.ne' htpos.ne'
  have hlogt : -1 ≤ Real.log t := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 1 / 2 ≤ t)
    rw [one_div, Real.log_inv] at hl
    linarith [Real.log_two_lt_d9]
  have hlogt1 : Real.log t ≤ 0 := Real.log_nonpos htpos.le ht1
  exact ⟨ht, ht1, hy1, by linarith, by linarith⟩

/-- The normalized lower step satisfies both ends of the proved square-log window. -/
theorem dusartMiddle_left_step_window {x : ℝ} (hx : 1 < x) (hb : 85 ≤ Real.log x) :
    let s := (2 / 25 : ℝ) / Real.log x ^ 2
    let t := 1 - 3 * s
    (3 / 40 : ℝ) / Real.log (x * t) ^ 2 ≤ s / t ∧
      s / t ≤ (17 / 200 : ℝ) / Real.log (x * t) ^ 2 := by
  dsimp only
  let b := Real.log x
  let s := (2 / 25 : ℝ) / b ^ 2
  let t := 1 - 3 * s
  obtain ⟨ht, ht1, hy1, hbl, hbu⟩ := dusartMiddle_shift_geometry hx hb
  have htpos : 0 < t := by dsimp [t, s, b]; linarith
  have hbpos : 0 < b := Real.log_pos hx
  have hcpos : 0 < Real.log (x * t) := Real.log_pos hy1
  have hspos : 0 < s := by dsimp [s]; positivity
  have hratio : (49 / 50 : ℝ) * b ≤ Real.log (x * t) := by dsimp [b]; linarith
  have hsq := pow_le_pow_left₀ (by positivity) hratio 2
  have hsq₁ := pow_le_pow_left₀ hcpos.le hbu 2
  constructor
  · calc
      _ ≤ s := by
        apply (div_le_div_iff₀ (pow_pos hcpos 2) (pow_pos hbpos 2)).mpr
        nlinarith only [hsq, sq_nonneg b]
      _ ≤ s / t := (le_div_iff₀ htpos).mpr (by nlinarith)
  · calc
      _ ≤ s / (99 / 100 : ℝ) := div_le_div_of_nonneg_left hspos.le (by norm_num) ht
      _ = (8 / 99 : ℝ) / b ^ 2 := by dsimp [s]; ring
      _ ≤ (17 / 200 : ℝ) / b ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg b)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (pow_pos hcpos 2) hsq₁

end PrimeFactorUnimodality
