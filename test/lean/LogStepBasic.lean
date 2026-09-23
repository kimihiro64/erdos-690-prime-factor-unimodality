import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.Basic

/-! # Exact interfaces and boundary cases for LogStepBasic -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory

example (w : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖(x : ℂ) - w‖) volume a b :=
  Complex.intervalIntegrable_log_norm_real_sub w a b

example (w : ℂ) (a b : ℝ) : IntervalIntegrable (logNormStep w) volume a b :=
  intervalIntegrable_logNormStep w a b

example (w : ℂ) (x : ℝ) : ‖(x : ℂ) - w‖ ^ 2 = (x - w.re) ^ 2 + w.im ^ 2 :=
  norm_real_sub_sq w x

example {w : ℂ} (hw : w.re ≤ 1 / 2) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ logNormStep w x := logNormStep_nonneg hw hx

example {w : ℂ} (hw : w.re ≤ 1 / 2) : 0 ≤ logNormStepIntegral w :=
  logNormStepIntegral_nonneg hw

example (w : ℂ) (x : ℝ) : logNormStep (star w) x = logNormStep w x :=
  logNormStep_conj w x

example (w : ℂ) : logNormStepIntegral (star w) = logNormStepIntegral w :=
  logNormStepIntegral_conj w

example : logNormStep (1 / 2 : ℂ) (1 / 2) = 0 := by
  norm_num [logNormStep]

example : 0 ≤ logNormStepIntegral (-10 : ℂ) :=
  logNormStepIntegral_nonneg (by norm_num)

end

end PrimeFactorUnimodality.Tests
