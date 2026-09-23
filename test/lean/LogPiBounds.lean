import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.PiBounds

/-! # Regression checks for explicit endpoint estimates and their hypotheses -/

namespace Real.Tests

open Real

example : (5061 / 2000 : ℝ) < Real.log (4 * π) :=
  log_four_mul_pi_gt_5061_div_2000

example : (1837 / 1000 : ℝ) < Real.log (2 * π) :=
  log_two_mul_pi_gt_1837_div_1000

example : (57 / 50 : ℝ) < Real.log π := log_pi_gt_57_div_50

end Real.Tests
