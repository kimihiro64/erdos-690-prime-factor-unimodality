import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingAbel

/-! # The exact counting-error identity behind the Lehman estimate

Subtract the smooth logarithmic counting term from finite xi Abel summation.
Both boundary errors and the integral of the actual counting discrepancy
are retained. The smooth term has no `7/8` constant, matching the density
`log(T/(2π))/(2π)` in the Lehman integral. No numerical bound for the
discrepancy is assumed proved by this identity.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- The primitive of the logarithmic zero density, with no constant offset. -/
def xiZeroCountingMainTerm (T : ℝ) : ℝ :=
  (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π)

/-- The discrepancy uses the actual multiplicity-counted positive zeros. -/
def xiZeroCountingRemainder (T : ℝ) : ℝ := (xiZeroCount T : ℝ) - xiZeroCountingMainTerm T

/-- The smooth counting term has exactly the density in the Lehman integral. -/
theorem hasDerivAt_xiZeroCountingMainTerm {T : ℝ} (hT : 0 < T) :
    HasDerivAt xiZeroCountingMainTerm ((1 / (2 * π)) * Real.log (T / (2 * π))) T := by
  have hq : T / (2 * π) ≠ 0 := ne_of_gt (by positivity : 0 < T / (2 * π))
  have h := ((Real.hasDerivAt_mul_log hq).sub (hasDerivAt_id (T / (2 * π)))).comp T
    ((hasDerivAt_id T).div_const (2 * π))
  convert h using 1
  · funext x
    rfl
  · ring

/-- Counting error times an integrable derivative is integrable on every positive interval. -/
theorem integrableOn_xiZeroCountingRemainder_mul {a b : ℝ} {g : ℝ → ℝ}
    (ha : 0 < a) (hg : IntegrableOn g (Icc a b)) :
    IntegrableOn (fun x => xiZeroCountingRemainder x * g x) (Icc a b) := by
  have hP : ContinuousOn xiZeroCountingMainTerm (Icc a b) :=
    fun x hx =>
      (hasDerivAt_xiZeroCountingMainTerm (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  apply ((integrableOn_xiZeroCount_mul hg).sub
    (IntegrableOn.continuousOn_mul hP hg isCompact_Icc)).congr_fun _ measurableSet_Icc
  intro x _
  simp only [Pi.sub_apply, xiZeroCountingRemainder, sub_mul]

/-- Exact error in replacing a finite zero sum by its logarithmic-density integral. -/
theorem sum_xi_height_window_sub_main_eq_remainder {a b : ℝ} {f g : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : IntegrableOn g (Icc a b)) :
    (∑ p ∈ xiHeightWindowIndices a b, f (riemannXiDivisorZeroValue p).im) -
        (∫ x in Icc a b, ((1 / (2 * π)) * Real.log (x / (2 * π))) * f x) =
      xiZeroCountingRemainder b * f b - xiZeroCountingRemainder a * f a -
        ∫ x in Icc a b, xiZeroCountingRemainder x * g x := by
  have hP (x : ℝ) (hx : x ∈ Icc a b) := hasDerivAt_xiZeroCountingMainTerm (ha.trans_le hx.1)
  have hPc : ContinuousOn xiZeroCountingMainTerm (Icc a b) :=
    fun x hx => (hP x hx).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hDc : ContinuousOn (fun x => (1 / (2 * π)) * Real.log (x / (2 * π))) (Icc a b) := by
    apply continuousOn_const.mul
    apply ContinuousOn.log (continuousOn_id.div_const _)
    intro x hx
    exact div_ne_zero (ne_of_gt (ha.trans_le hx.1)) (by positivity)
  have hD : IntegrableOn
      (fun x => ((1 / (2 * π)) * Real.log (x / (2 * π))) * f x) (Icc a b) :=
    (hDc.mul hfc).integrableOn_Icc
  have hPg := IntegrableOn.continuousOn_mul hPc hg isCompact_Icc
  have hprod :
      (∫ x in Icc a b, ((1 / (2 * π)) * Real.log (x / (2 * π))) * f x +
        xiZeroCountingMainTerm x * g x) =
      xiZeroCountingMainTerm b * f b - xiZeroCountingMainTerm a * f a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hab] at hx
      exact (hP x hx).mul (hf x hx)
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hD.add hPg)
  rw [integral_add hD hPg] at hprod
  rw [sum_xi_height_window_eq_boundary_sub_integral hab hf hg]
  simp only [xiZeroCountingRemainder, sub_mul]
  rw [integral_sub (integrableOn_xiZeroCount_mul hg) hPg]
  linarith

end

end PrimeFactorUnimodality
