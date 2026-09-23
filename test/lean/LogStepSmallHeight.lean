import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.SmallHeight

/-! # Exact interfaces and boundary cases for LogStepSmallHeight -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory

example {w : ℂ} (hw : |w.re| ≤ 1 / 2) (hv : |w.im| ≤ 1) :
    logNormStepIntegral w ≤ 4 := logNormStepIntegral_le_four hw hv

example : logNormStepIntegral (1 / 2 : ℂ) ≤ 4 :=
  logNormStepIntegral_le_four (by norm_num) (by norm_num)

example : logNormStepIntegral (-1 / 2 : ℂ) ≤ 4 :=
  logNormStepIntegral_le_four (by norm_num) (by norm_num)

example : logNormStepIntegral ((1 / 2 : ℂ) + I) ≤ 4 :=
  logNormStepIntegral_le_four (by norm_num) (by norm_num)

example : logNormStepIntegral ((-1 / 2 : ℂ) - I) ≤ 4 :=
  logNormStepIntegral_le_four (by norm_num) (by norm_num)

end

end PrimeFactorUnimodality.Tests
