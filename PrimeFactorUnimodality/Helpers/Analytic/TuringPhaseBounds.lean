import PrimeFactorUnimodality.Helpers.Analytic.TuringCountPhase
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingRemainder
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogHeightBounds

/-! # A subunit upper bound for the exact counting-phase correction

The shifted Gamma factor contributes `3*pi/8`, and the pole contributes
`pi/2`, retaining the counting model's missing `7/8` constant. The remaining
norm and argument errors decay with height. From height 32 the total
correction is at most `15*pi/16`, strictly less than one zero's phase.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The exact smooth phase has its constant offset and a height-decaying error explicitly bounded. -/
theorem turingCountingPhase_sub_main_le {T : ℝ} (hT : 0 < T) :
    turingCountingPhase T - Real.pi * xiZeroCountingMainTerm T ≤
      7 * Real.pi / 8 + 1 / 10 + 33 / (16 * T) := by
  let z : ℂ := (5 / 4 : ℂ) + (T : ℂ) / 2 * I
  have hzre : z.re = 5 / 4 := by dsimp [z]; norm_num
  have hzim : z.im = T / 2 := by dsimp [z]; simp
  have hlog : T / 2 * (Real.log ‖z‖ - Real.log (T / 2)) ≤ 25 / (16 * T) := by
    have h := im_mul_log_norm_sub_log_im_le (z := z) (by rw [hzim]; positivity)
    rw [hzre, hzim] at h
    convert h using 1
    ring
  have harg : (3 / 4 : ℝ) * arg z ≤ 3 * Real.pi / 8 := by
    have h : arg z ≤ Real.pi / 2 := arg_le_pi_div_two_iff.mpr (Or.inl (by rw [hzre]; norm_num))
    linarith
  have hpole : arg ((1 / 2 : ℂ) + T * I - 1) ≤ Real.pi / 2 + 1 / (2 * T) := by
    have h := arg_le_pi_div_two_sub_re_div_im
      (z := (1 / 2 : ℂ) + T * I - 1) (by simpa using hT) (by norm_num)
    convert h using 1
    simp
    ring
  have hg := abs_xiGamma_half_contour_sub_stirling_le
    (σ := 2) (by norm_num) T
  rw [xiGamma_half_contour_eq_left (by norm_num)] at hg
  have he : (3 / 4 : ℝ) * arg z + T / 2 * Real.log ‖z‖ - T / 2 -
      T / 2 * Real.log Real.pi - Real.pi * xiZeroCountingMainTerm T =
        (3 / 4 : ℝ) * arg z + T / 2 * (Real.log ‖z‖ - Real.log (T / 2)) := by
    unfold xiZeroCountingMainTerm
    rw [show T / (2 * Real.pi) = (T / 2) / Real.pi by ring,
      Real.log_div (by positivity : T / 2 ≠ 0) Real.pi_pos.ne']
    field_simp
    ring
  have hfrac : 25 / (16 * T) + 1 / (2 * T) = 33 / (16 * T) := by ring
  change |(xiGammaLog ((1 / 2 : ℂ) + T * I)).im -
    ((3 / 4 : ℝ) * arg z + T / 2 * Real.log ‖z‖ - T / 2 -
      T / 2 * Real.log Real.pi)| ≤ 1 / 10 at hg
  unfold turingCountingPhase
  linarith [le_abs_self ((xiGammaLog ((1 / 2 : ℂ) + T * I)).im -
    ((3 / 4 : ℝ) * arg z + T / 2 * Real.log ‖z‖ - T / 2 - T / 2 * Real.log Real.pi))]

/-- Above height 32, the phase correction is bounded by strictly less than one count unit. -/
theorem turingCountingPhase_sub_main_le_fifteen_sixteenths {T : ℝ} (hT : 32 ≤ T) :
    turingCountingPhase T - Real.pi * xiZeroCountingMainTerm T ≤ (15 / 16 : ℝ) * Real.pi := by
  have ht0 : 0 < T := by linarith
  have h := turingCountingPhase_sub_main_le ht0
  have hfrac : 33 / (16 * T) ≤ (33 / 512 : ℝ) :=
    (div_le_iff₀ (by positivity : 0 < 16 * T)).mpr (by nlinarith)
  linarith [Real.pi_gt_three]

end

end PrimeFactorUnimodality
