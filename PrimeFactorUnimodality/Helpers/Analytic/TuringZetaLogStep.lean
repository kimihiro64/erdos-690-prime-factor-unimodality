import PrimeFactorUnimodality.Helpers.Analytic.TuringGammaLower
import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogIntegral

/-! # Lower comparison of actual zeta and xi logarithmic steps

To the right of the critical line the pole factor has nonnegative gain.
The proved Gamma increment bound thus loses at most two in converting the
actual negative xi increment to the zeta decrement. Endpoint zeros will be
handled almost everywhere by the integral consumer.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The actual zeta decrement on a unit interval shifted from the critical line. -/
def turingZetaLogDecrement (T x : ℝ) : ℝ :=
  Real.log ‖riemannZeta ((x : ℂ) + ((1 / 2 : ℂ) + T * I))‖ -
    Real.log ‖riemannZeta ((x : ℂ) + ((1 / 2 : ℂ) + T * I) + 1)‖

/-- The pole contribution to a rightward unit step is nonnegative beyond the critical line. -/
theorem turing_pole_log_gain_nonneg (T : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.log ‖(x : ℂ) + ((1 / 2 : ℂ) + T * I)‖ -
      Real.log ‖(x : ℂ) + ((1 / 2 : ℂ) + T * I) - 1‖ := by
  have h := logNormStep_nonneg (w := (1 / 2 : ℂ) - T * I) (by norm_num) hx
  have ha : ((x + 1 : ℝ) : ℂ) - ((1 / 2 : ℂ) - T * I) =
      (x : ℂ) + ((1 / 2 : ℂ) + T * I) := by push_cast; ring
  have hb : (x : ℂ) - ((1 / 2 : ℂ) - T * I) =
      (x : ℂ) + ((1 / 2 : ℂ) + T * I) - 1 := by ring
  simpa only [logNormStep, ha, hb] using h

/-- The actual zeta decrement is bounded below by the negative xi increment and a fixed loss. -/
theorem turingZetaLogDecrement_ge {T x : ℝ} (hT : T ≠ 0) (hx : 0 ≤ x)
    (hxi : riemannXi ((x : ℂ) + ((1 / 2 : ℂ) + T * I)) ≠ 0) :
    -turingXiLogIncrement T x - 2 ≤ turingZetaLogDecrement T x := by
  let s : ℂ := (x : ℂ) + ((1 / 2 : ℂ) + T * I)
  have hs : 0 < s.re := by norm_num [s]; linarith
  have hs1 : s ≠ 1 := by intro he; exact hT (by simpa [s] using congrArg Complex.im he)
  have hplus : 1 < (s + 1).re := by simp only [add_re, one_re]; linarith
  have hplus1 : s + 1 ≠ 1 := by intro he; simp [he] at hplus
  have hz := log_norm_riemannXi_eq_pole_gamma_zeta hs hs1 hxi
  have hz1 := log_norm_riemannXi_eq_pole_gamma_zeta (zero_lt_one.trans hplus) hplus1
    (riemannXi_ne_zero_of_one_lt_re hplus)
  simp only [add_sub_cancel_right] at hz1
  have hg := xiGammaLog_unit_sub_re_ge hs
  have hp : 0 ≤ Real.log ‖s‖ - Real.log ‖s - 1‖ := turing_pole_log_gain_nonneg T hx
  change -(Real.log ‖riemannXi (s + 1)‖ - Real.log ‖riemannXi s‖) - 2 ≤
    Real.log ‖riemannZeta s‖ - Real.log ‖riemannZeta (s + 1)‖
  linarith

end

end PrimeFactorUnimodality
