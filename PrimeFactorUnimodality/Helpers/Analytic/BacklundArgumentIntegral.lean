import PrimeFactorUnimodality.Helpers.Analytic.BacklundArgument
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.IntervalIntegral

/-! # The horizontal logarithmic-derivative integral in Backlund's argument

The continuous logarithm constructed from the exponential covering has
derivative equal to the surrogate's logarithmic derivative. Its increment
is therefore exactly the horizontal contour integral, with integrability
proved from analyticity and nonvanishing. The imaginary part inherits the
power-limit Jensen bound, ready for the argument-principle calculation.
-/

namespace PrimeFactorUnimodality
noncomputable section
open Complex Metric Real Set

/-- The horizontal restriction has the actual complex derivative as its real derivative. -/
theorem hasDerivAt_backlundSurrogate_horizontal (T x : ℝ) :
    HasDerivAt (fun y : ℝ => Backlund.zetaSurrogate ((y : ℂ) + T * I))
      (deriv Backlund.zetaSurrogate ((x : ℂ) + T * I)) x := by
  simpa using ((Backlund.zetaSurrogate_differentiable ((x : ℂ) + T * I)).hasDerivAt.comp
    (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (T * I))).comp_ofReal

/-- Nonvanishing on the closed segment makes its logarithmic derivative integrable. -/
theorem intervalIntegrable_backlundSurrogate_logDeriv {T a b : ℝ} (hab : a ≤ b)
    (hne : ∀ x ∈ Icc a b, Backlund.zetaSurrogate ((x : ℂ) + T * I) ≠ 0) :
    IntervalIntegrable (fun x : ℝ => logDeriv Backlund.zetaSurrogate ((x : ℂ) + T * I))
      MeasureTheory.volume a b := by
  have hdc : Continuous (deriv Backlund.zetaSurrogate) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (Backlund.zetaSurrogate_differentiable.analyticAt z).deriv.continuousAt)
  have hc : Continuous (fun x : ℝ => (x : ℂ) + T * I) := by fun_prop
  exact ContinuousOn.intervalIntegrable_of_Icc hab
    ((hdc.comp hc).continuousOn.div
      (Backlund.zetaSurrogate_differentiable.continuous.comp hc).continuousOn hne)

/-- The contour integral equals the increment of any continuous logarithm on the segment. -/
theorem integral_backlundSurrogate_logDeriv_eq {T a b : ℝ} {L : ℝ → ℂ} (hab : a ≤ b)
    (hL : ContinuousOn L (Icc a b))
    (he : ∀ x ∈ Icc a b, Complex.exp (L x) = Backlund.zetaSurrogate ((x : ℂ) + T * I)) :
    ∫ x in a..b, logDeriv Backlund.zetaSurrogate ((x : ℂ) + T * I) = L b - L a := by
  have hne : ∀ x ∈ Icc a b, Backlund.zetaSurrogate ((x : ℂ) + T * I) ≠ 0 := by
    intro x hx
    rw [← he x hx]
    exact Complex.exp_ne_zero _
  exact Complex.integral_div_eq_logarithm_sub hab hL
    (fun x _ => hasDerivAt_backlundSurrogate_horizontal T x) he
    (intervalIntegrable_backlundSurrogate_logDeriv hab hne)

/-- Jensen bounds the actual horizontal argument integral after the infinite-power limit. -/
theorem abs_im_integral_backlundSurrogate_logDeriv_le {T σ r R M a b : ℝ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hab : a ≤ b) (hseg : ∀ x ∈ Icc a b, |x - σ| ≤ r)
    (hne : ∀ x ∈ Icc a b, Backlund.zetaSurrogate ((x : ℂ) + T * I) ≠ 0)
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |(∫ x in a..b, logDeriv Backlund.zetaSurrogate ((x : ℂ) + T * I)).im| ≤ Real.pi *
      (Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) / Real.log (R / r)) := by
  obtain ⟨L, hL, _, he, hb⟩ := exists_backlund_log_with_argument_bound
    hσ hr hrR hM hab hseg hne hp hm
  rw [integral_backlundSurrogate_logDeriv_eq hab hL.continuousOn he, Complex.sub_im]
  exact hb

end
end PrimeFactorUnimodality
