import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserRelative
import PrimeFactorUnimodality.Helpers.Analytic.DusartFarStepWindow
import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalNormMonotone

/-! # Square-log error for actual psi averages on the far ray

The low block, finite window, complete high tail and elementary correction
are bounded separately. Their square-log moments fit inside one hundredth
uniformly in the relative-step window. Low-height verification and the
numerical region with constant six remain explicit zero-location inputs.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The logarithmic starting point supplies the root-parameter threshold. -/
theorem dusartFar_root_ge {b : ℝ} (hb : 4704 ≤ b) : 28 ≤ sqrt (b / 6) := by
  have hs := sq_sqrt (by linarith : 0 ≤ b / 6)
  have hn := sqrt_nonneg (b / 6)
  nlinarith

/-- The far scalar budget is uniform over all smaller admissible verification heights. -/
theorem dusartBoxRosserRelativeBudget_le_far_of_height_le {s x H : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x)
    (hs₀ : exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)))
    (hH : 10 ≤ H) (hH₁ : H ≤ 1000000000) :
    dusartBoxRosserRelativeBudget 0 s x 6 (4 / 5) 10 H (1 / 2) ≤
      (1 / 100 : ℝ) / Real.log x ^ 2 := by
  let X := sqrt (Real.log x / 6)
  have hX : 28 ≤ X := dusartFar_root_ge hb
  have hs : 0 < s := (by positivity : 0 < exp (-(4 / 5 : ℝ) * X) / 2).trans_le hs₀
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hbpos : 0 < Real.log x := Real.log_pos hx
  have hx2 : 2 ≤ x := by
    have he := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hxpos] at he
    linarith
  have hscale : Real.log x ^ 2 = 36 * X ^ 4 := by
    have hsquare := sq_sqrt (by linarith : 0 ≤ Real.log x / 6)
    calc
      _ = (6 * X ^ 2) ^ 2 := by congr 1; dsimp [X]; linarith
      _ = _ := by ring
  have hlow : ((1 + 3 * s) * exp (-(1 / 2) * Real.log x)) *
      xiLowReciprocalNormBound 10 H (1 / 2) ≤
        77 * exp (-Real.log x / 2) := by
    calc
      _ ≤ ((1 + 3 * s) * exp (-(1 / 2) * Real.log x)) * 70 :=
        mul_le_mul_of_nonneg_left
          (xiLowReciprocalNormBound_half_le_of_le_billion hH hH₁) (by positivity)
      _ ≤ ((11 / 10 : ℝ) * exp (-(1 / 2) * Real.log x)) * 70 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (dusartFar_width_le hX hs₁) (exp_pos _).le) (by norm_num)
      _ = _ := by rw [show -(1 / 2) * Real.log x = -Real.log x / 2 by ring]; ring
  have hbudget : dusartBoxRosserRelativeBudget 0 s x 6 (4 / 5) 10 H (1 / 2) ≤
      77 * exp (-Real.log x / 2) + 32 * X * exp (-(5 / 4 : ℝ) * X) +
        2048 * X * exp (-(5 / 4 : ℝ) * X) + 4 / x := by
    simpa only [dusartBoxRosserRelativeBudget, Nat.reduceAdd, Nat.cast_ofNat,
      show (2 : ℝ) ^ 3 = 8 by norm_num, X] using
      add_le_add (add_le_add (add_le_add hlow (dusartFar_window_le hX hs hs₁))
        (dusartFar_high_le hX hs₀ hs₁)) (dusartLog_correction_le hx2)
  have hl := dusartFar_low_moment_le hb
  have hw := dusartFar_window_moment_le hX
  have hh := dusartFar_high_moment_le hX
  have hc := dusartFar_correction_moment_le hb
  rw [← hscale] at hw hh
  rw [Real.exp_log hxpos] at hc
  apply (le_div_iff₀ (pow_pos hbpos 2)).mpr
  have hm := mul_le_mul_of_nonneg_left hbudget (sq_nonneg (Real.log x))
  nlinarith only [hm, hl, hw, hh, hc]

/-- The billion-height specialization retains the original scalar interface. -/
theorem dusartBoxRosserRelativeBudget_le_far {s x : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x)
    (hs₀ : exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))) :
    dusartBoxRosserRelativeBudget 0 s x 6 (4 / 5) 10 1000000000 (1 / 2) ≤
      (1 / 100 : ℝ) / Real.log x ^ 2 :=
  dusartBoxRosserRelativeBudget_le_far_of_height_le hx hb hs₀ hs₁ (by norm_num) le_rfl

/-- The actual averaged error accepts low-zero data at any smaller admissible height. -/
theorem abs_dusartPsiAverageError_div_le_far_of_height_le {s x H : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x)
    (hs₀ : exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)))
    (hH : 20 ≤ H) (hH₁ : H ≤ 1000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError 3 (s * x) x| / x ≤ (1 / 100 : ℝ) / Real.log x ^ 2 := by
  have hX := dusartFar_root_ge hb
  have hs : 0 < s := (by positivity :
    0 < exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2).trans_le hs₀
  have hparam : Real.log (2 * π) ≤ 1 / 3 + sqrt ((Real.log x / 6) / 3) := by
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * π)
    have hn := sqrt_nonneg ((Real.log x / 6) / 3)
    have hsquare := sq_sqrt (by linarith : 0 ≤ (Real.log x / 6) / 3)
    have hr : 10 ≤ sqrt ((Real.log x / 6) / 3) := by nlinarith
    linarith [pi_lt_four]
  have h := abs_dusartPsiAverageError_div_le_rosserRelative 0 hs hx
    (by norm_num : (0 : ℝ) < 6) (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num)
    (by norm_num) hparam (by norm_num : (10 : ℝ) ≤ 10)
    (by linarith : (10 : ℝ) < H) hH (by norm_num : (0 : ℝ) < 1 / 2)
    (hH₁.trans (dusartFar_cutoff_ge_billion hX))
    (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hgap) hreg
  exact h.trans (dusartBoxRosserRelativeBudget_le_far_of_height_le hx hb hs₀ hs₁
    (by linarith) hH₁)

/-- The original billion-height average is a specialization of the height-uniform theorem. -/
theorem abs_dusartPsiAverageError_div_le_far {s x : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x)
    (hs₀ : exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)))
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError 3 (s * x) x| / x ≤ (1 / 100 : ℝ) / Real.log x ^ 2 :=
  abs_dusartPsiAverageError_div_le_far_of_height_le hx hb hs₀ hs₁
    (by norm_num) le_rfl hgap hreg

end

end PrimeFactorUnimodality
