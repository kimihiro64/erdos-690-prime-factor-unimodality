import PrimeFactorUnimodality.Helpers.Analytic.BacklundCircleBounds
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.CircleAverageAntipodal

/-! # The asymmetric logarithmic mean on the Backlund circle

Opposite points have complementary real parts. One receives the linear
right-semicircle bound and the other the quadratic global bound. Averaging
this pair gives growth `3/2*log(T)` for the surrogate, rather than `2*log(T)`.
This includes zeros of the auxiliary function: the totalized real logarithm
at zero is handled explicitly, and integrability follows from analyticity.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Metric Real

/-- The explicit logarithmic mean of the linear and quadratic circle bounds. -/
def backlundCircleLogBound (T : ℝ) : ℝ :=
  (Real.log (22 * |T|) + Real.log (50 * |T| ^ 2)) / 2

private theorem log_norm_backlundAuxiliary_le {T M : ℝ} {z : ℂ} (n : ℕ) (hM : 1 ≤ M)
    (hp : ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    Real.log ‖backlundAuxiliary T n z‖ ≤ (n : ℝ) * Real.log M := by
  by_cases hn : backlundAuxiliary T n z = 0
  · simp only [hn, norm_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hM)
  · rw [← Real.log_pow]
    exact Real.log_le_log (norm_pos_iff.mpr hn) (norm_backlundAuxiliary_le_pow hp hm)

private theorem antipode_mem_unit_circle {z : ℂ} (hz : z ∈ sphere (11 / 10 : ℂ) 1) :
    2 * (11 / 10 : ℂ) - z ∈ sphere (11 / 10 : ℂ) 1 := by
  simp only [mem_sphere, dist_eq_norm] at hz ⊢
  rw [show 2 * (11 / 10 : ℂ) - z - 11 / 10 = -(z - 11 / 10) by ring, norm_neg]
  exact hz

/-- The actual auxiliary logarithmic mean satisfies the half-circle estimate at every power. -/
theorem circleAverage_log_backlundAuxiliary_le {T : ℝ} (hT : 10 ≤ |T|) (n : ℕ) :
    circleAverage (fun z => Real.log ‖backlundAuxiliary T n z‖) (11 / 10 : ℂ) 1 ≤
      (n : ℝ) * backlundCircleLogBound T := by
  have hfull (z : ℂ) (hz : z ∈ sphere (11 / 10 : ℂ) 1) :
      Real.log ‖backlundAuxiliary T n z‖ ≤ (n : ℝ) * Real.log (50 * |T| ^ 2) := by
    apply log_norm_backlundAuxiliary_le n (by nlinarith [sq_nonneg (|T| - 1)])
      (norm_backlundSurrogate_unit_circle_le hT hz)
    simpa only [abs_neg, ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      norm_backlundSurrogate_unit_circle_le (t := -T) (by simpa using hT) hz
  have hright (z : ℂ) (hz : z ∈ sphere (11 / 10 : ℂ) 1) (hr : 11 / 10 ≤ z.re) :
      Real.log ‖backlundAuxiliary T n z‖ ≤ (n : ℝ) * Real.log (22 * |T|) := by
    apply log_norm_backlundAuxiliary_le n (by linarith)
      (norm_backlundSurrogate_unit_right_semicircle_le hT hz hr)
    simpa only [abs_neg, ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      norm_backlundSurrogate_unit_right_semicircle_le (t := -T) (by simpa using hT) hz hr
  have ha : AnalyticOnNhd ℂ (backlundAuxiliary T n) (sphere (11 / 10 : ℂ) |(1 : ℝ)|) :=
    fun z _ => (differentiable_backlundAuxiliary T n).analyticAt z
  have h := circleAverage_le_of_antipodal_bound ha.meromorphicOn.circleIntegrable_log_norm
    (B := (n : ℝ) * (Real.log (22 * |T|) + Real.log (50 * |T| ^ 2))) (by
      intro z hz
      rw [abs_one] at hz
      have hz' := antipode_mem_unit_circle hz
      by_cases hr : 11 / 10 ≤ z.re
      · nlinarith [hright z hz hr, hfull _ hz']
      · have hr' : 11 / 10 ≤ (2 * (11 / 10 : ℂ) - z).re := by
          norm_num [sub_re, mul_re] at *
          linarith
        nlinarith [hfull z hz, hright _ hz' hr'])
  convert h using 1
  dsimp [backlundCircleLogBound]
  ring

end

end PrimeFactorUnimodality
