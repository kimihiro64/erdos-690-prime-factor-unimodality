import PrimeFactorUnimodality.Helpers.Analytic.DusartFarAverage

/-! # Stability of the exponential step under the lower-average shift

A logarithmic shift by at most one moves the root parameter by at most
one half. The two exponential steps then differ by at most a factor two.
The actual lower base point and its renormalized step satisfy these bounds.
-/

namespace PrimeFactorUnimodality

open Real

/-- Nearby logarithmic arguments give comparable exponential steps. -/
theorem dusartFar_step_shift_le {b c : ℝ} (hc : 4704 ≤ c)
    (hcb : c ≤ b) (hbc : b ≤ c + 1) :
    exp (-(4 / 5 : ℝ) * sqrt (b / 6)) ≤ exp (-(4 / 5 : ℝ) * sqrt (c / 6)) ∧
      exp (-(4 / 5 : ℝ) * sqrt (c / 6)) ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (b / 6)) := by
  have hroot := dusartFar_root_ge hc
  have hsq := sq_sqrt (by linarith : 0 ≤ c / 6)
  have hshift : sqrt (b / 6) ≤ sqrt (c / 6) + 1 / 2 := by
    apply (sqrt_le_left (by positivity)).mpr
    nlinarith only [hroot, hsq, hbc]
  have hmono := sqrt_le_sqrt (by linarith : c / 6 ≤ b / 6)
  refine ⟨exp_le_exp.mpr (by linarith), ?_⟩
  calc
    _ = exp (-(4 / 5 : ℝ) * sqrt (b / 6)) *
        exp ((4 / 5 : ℝ) * (sqrt (b / 6) - sqrt (c / 6))) := by
      rw [← exp_add]
      congr 1
      ring
    _ ≤ exp (-(4 / 5 : ℝ) * sqrt (b / 6)) * exp (Real.log 2) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [log_two_gt_d9])) (by positivity)
    _ = _ := by rw [exp_log (by norm_num : (0 : ℝ) < 2)]; ring

/-- The lower base remains on the far ray, with a logarithmic loss of at most one. -/
theorem dusartFar_shift_geometry {x : ℝ} (hx : 1 < x) (hb : 5000 ≤ Real.log x) :
    let s := exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))
    let t := 1 - 3 * s
    (1 / 2 : ℝ) ≤ t ∧ t ≤ 1 ∧ 1 < x * t ∧
      Real.log x - 1 ≤ Real.log (x * t) ∧ Real.log (x * t) ≤ Real.log x := by
  dsimp only
  let s := exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))
  let t := 1 - 3 * s
  have hspos : 0 < s := exp_pos _
  have hsmax : s ≤ (1 / 5000000000 : ℝ) := dusartFar_exp_step_le
    (dusartFar_root_ge (by linarith))
  have ht : (1 / 2 : ℝ) ≤ t := by dsimp [t]; linarith
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
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) ht
    rw [one_div, Real.log_inv] at hl
    linarith [Real.log_two_lt_d9]
  have hlogt1 : Real.log t ≤ 0 := Real.log_nonpos htpos.le ht1
  exact ⟨ht, ht1, hy1, by linarith, by linarith⟩

/-- The lower average's relative step belongs to its own exponential step window. -/
theorem dusartFar_left_step_window {x : ℝ} (hx : 1 < x) (hb : 5000 ≤ Real.log x) :
    let s := exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))
    let t := 1 - 3 * s
    exp (-(4 / 5 : ℝ) * sqrt (Real.log (x * t) / 6)) / 2 ≤ s / t ∧
      s / t ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log (x * t) / 6)) := by
  dsimp only
  let s := exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))
  let t := 1 - 3 * s
  obtain ⟨ht, ht1, _, hbl, hbu⟩ := dusartFar_shift_geometry hx hb
  have htpos : 0 < t := by dsimp [t, s]; linarith
  have hspos : 0 < s := exp_pos _
  have hsteps := dusartFar_step_shift_le (by linarith : 4704 ≤ Real.log (x * t))
    hbu (by linarith)
  constructor
  · calc
      _ ≤ s := by linarith [hsteps.2]
      _ ≤ s / t := (le_div_iff₀ htpos).mpr (by nlinarith)
  · calc
      _ ≤ 2 * s := (div_le_iff₀ htpos).mpr (by nlinarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsteps.1 (by norm_num)

end PrimeFactorUnimodality
