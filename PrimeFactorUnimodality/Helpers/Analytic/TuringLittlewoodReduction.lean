import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalDerivative
import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalLower
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.FiniteExceptions

/-! # Littlewood's identity reduced to continuity through zero heights

The exceptional ordinates on a bounded positive interval form a finite
image of actual divisor labels. The finite-exception fundamental theorem
of calculus proves the horizontal endpoint identity once continuity at
those heights is supplied. No numerical zero enumeration or bound on
their number is needed. Continuity on arbitrary positive intervals remains
an explicit analytic obligation, not an almost-everywhere inference.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- Actual divisor finiteness removes every exceptional derivative point once continuity is known. -/
theorem integral_turingZetaArgument_eq_horizontal_sub_of_continuous {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 0 < a) (hab : a ≤ b)
    (hc : ContinuousOn turingHorizontalIntegral (Icc a b)) :
    (∫ T in a..b, turingZetaArgument σ T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a := by
  classical
  let s := (xiPositiveHeightIndices b).image (fun p => (riemannXiDivisorZeroValue p).im)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_off_finset s hab hc _
    (intervalIntegrable_turingZetaArgument hσ ha hab)
  intro T hT hTs
  apply hasDerivAt_turingHorizontalIntegral hσ (ha.trans hT.1)
  intro z hz hzero
  obtain ⟨p, hp⟩ := exists_xi_divisor_index_of_zero hzero
  have hpim : (riemannXiDivisorZeroValue p).im = T := by rw [hp, hz]
  have hpS : p ∈ xiPositiveHeightIndices b :=
    (mem_xiPositiveHeightIndices b p).mpr (by rw [hpim]; exact ⟨ha.trans hT.1, hT.2.le⟩)
  exact hTs (Finset.mem_image.mpr ⟨p, hpS, hpim⟩)

/-- The complete identity already holds on any closed positive interval of regular heights. -/
theorem integral_turingZetaArgument_eq_horizontal_sub_of_regular {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 0 < a) (hab : a ≤ b)
    (hreg : ∀ T ∈ Icc a b, ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    (∫ T in a..b, turingZetaArgument σ T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a :=
  integral_turingZetaArgument_eq_horizontal_sub_of_continuous hσ ha hab
    (continuousOn_turingHorizontalIntegral_of_regular ha hreg)

/-- The true closed-count discrepancy retains its exact smooth phase in the endpoint formula. -/
theorem pi_mul_integral_xiZeroCountingRemainder_eq_horizontal_of_continuous {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : ContinuousOn turingHorizontalIntegral (Icc a b)) :
    Real.pi * (∫ T in a..b, xiZeroCountingRemainder T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a +
        (∫ T in a..b, turingCountingPhase T) -
          Real.pi * (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) := by
  rw [pi_mul_integral_xiZeroCountingRemainder (by norm_num : (1 : ℝ) < 2) ha hab,
    integral_turingZetaArgument_eq_horizontal_sub_of_continuous (by norm_num) ha hab hc]

/-- The complete endpoint bounds give an explicit argument budget after the continuity obligation. -/
theorem abs_integral_turingZetaArgument_le_of_continuous {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hc : ContinuousOn turingHorizontalIntegral (Icc a b)) :
    |∫ T in a..b, turingZetaArgument σ T| ≤ (19 / 2 : ℝ) * Real.log (5 * b) + 95 := by
  have ha0 : 0 < a := by linarith
  have hup {T : ℝ} (hT : a ≤ T) (hTb : T ≤ b) :
      turingHorizontalIntegral T ≤ (3 / 2 : ℝ) * Real.log (5 * b) + 1 := by
    have hpos := ha0.trans_le hT
    have h := turingHorizontalIntegral_le (T := T) (by simpa [abs_of_pos hpos] using ha.trans hT)
    rw [abs_of_pos hpos] at h
    have hl := Real.log_le_log (by positivity : 0 < 5 * T)
      (mul_le_mul_of_nonneg_left hTb (by norm_num : (0 : ℝ) ≤ 5))
    linarith
  have hlo {T : ℝ} (hT : a ≤ T) (hTb : T ≤ b) :
      -(8 * Real.log (5 * b) + 94) ≤ turingHorizontalIntegral T := by
    have hpos := ha0.trans_le hT
    have h := turingHorizontalIntegral_ge hpos.ne'
    rw [abs_of_pos hpos] at h
    have hl := Real.log_le_log (by positivity : 0 < T / 2 + 3)
      (show T / 2 + 3 ≤ 5 * b by linarith)
    linarith
  rw [integral_turingZetaArgument_eq_horizontal_sub_of_continuous hσ ha0 hab hc, abs_le]
  constructor <;> linarith [hup le_rfl hab, hup hab le_rfl, hlo le_rfl hab, hlo hab le_rfl]

end

end PrimeFactorUnimodality
