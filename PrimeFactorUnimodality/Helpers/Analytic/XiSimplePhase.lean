import PrimeFactorUnimodality.Helpers.Analytic.XiStirlingPhase
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogHeightBounds

/-! # An elementary high-height xi phase with an explicit error

Two argument evaluations and the logarithm of a complex norm can be replaced
by a real logarithm and shared pi constants. Upper-quadrant argument bounds
and the logarithmic norm correction give the full error at every positive
height. The existing Gamma remainder remains an additional one tenth.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- An elementary phase retaining the pole factor's upper-half-plane branch. -/
def xiSimplePhase (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / 2) - t / 2 - t / 2 * Real.log Real.pi + 7 * Real.pi / 8

/-- The argument and logarithmic corrections are bounded at every positive height. -/
theorem abs_turingStirlingPhase_sub_simple_le {t : ℝ} (ht : 0 < t) :
    |turingStirlingPhase t - xiSimplePhase t| ≤ 33 / (16 * t) := by
  let z : ℂ := (5 / 4 : ℂ) + (t : ℂ) / 2 * I
  let w : ℂ := (1 / 2 : ℂ) + t * I - 1
  have hzre : z.re = 5 / 4 := by simp [z]
  have hzim : z.im = t / 2 := by simp [z]
  have hwre : w.re = -1 / 2 := by norm_num [w]
  have hwim : w.im = t := by simp [w]
  have hzpos : 0 < z.im := by rw [hzim]; positivity
  have hgU : arg z ≤ Real.pi / 2 :=
    arg_le_pi_div_two_iff.mpr (Or.inl (by rw [hzre]; norm_num))
  have hgL : Real.pi / 2 - 5 / (2 * t) ≤ arg z := by
    have h := pi_div_two_sub_re_div_im_le_arg hzpos (by rw [hzre]; norm_num)
    rw [hzre, hzim] at h
    convert h using 1
    field_simp
    ring
  have hcU : arg w ≤ Real.pi / 2 + 1 / (2 * t) := by
    have h := arg_le_pi_div_two_sub_re_div_im (by rwa [hwim]) (by rw [hwre]; norm_num)
    rw [hwre, hwim] at h
    convert h using 1
    field_simp
    ring
  have hcL : Real.pi / 2 ≤ arg w := by
    by_contra hn
    rcases arg_lt_pi_div_two_iff.mp (lt_of_not_ge hn) with hr | hi | he
    · rw [hwre] at hr
      norm_num at hr
    · rw [hwim] at hi
      linarith
    · have := congrArg Complex.im he
      rw [hwim] at this
      simp only [zero_im] at this
      linarith
  have hlogL : 0 ≤ t / 2 * (Real.log ‖z‖ - Real.log (t / 2)) := by
    apply mul_nonneg (by positivity)
    apply sub_nonneg.mpr
    apply Real.log_le_log (by positivity)
    rw [← hzim]
    exact im_le_norm z
  have hlogU : t / 2 * (Real.log ‖z‖ - Real.log (t / 2)) ≤ 25 / (16 * t) := by
    have h := im_mul_log_norm_sub_log_im_le hzpos
    rw [hzre, hzim] at h
    convert h using 1
    field_simp
    ring
  have hbudget : 0 < (1 : ℝ) / t := one_div_pos.mpr ht
  have he : turingStirlingPhase t - xiSimplePhase t =
      (3 / 4 : ℝ) * (arg z - Real.pi / 2) +
        t / 2 * (Real.log ‖z‖ - Real.log (t / 2)) + (arg w - Real.pi / 2) := by
    unfold turingStirlingPhase xiSimplePhase
    dsimp only [z, w]
    ring
  rw [he]
  rw [div_mul_eq_div_mul_one_div] at hgL hcU hlogU
  rw [div_mul_eq_div_mul_one_div]
  apply abs_le.mpr
  constructor <;> linarith

/-- Retain the full existing Gamma remainder when approximating the actual xi phase. -/
theorem abs_turingCountingPhase_sub_simple_le {t : ℝ} (ht : 0 < t) :
    |turingCountingPhase t - xiSimplePhase t| ≤ 1 / 10 + 33 / (16 * t) :=
  (abs_sub_le _ _ _).trans (add_le_add (abs_turingCountingPhase_sub_stirling_le t)
    (abs_turingStirlingPhase_sub_simple_le ht))

end

end PrimeFactorUnimodality
