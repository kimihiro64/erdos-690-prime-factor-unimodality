import PrimeFactorUnimodality.Mathlib.NumberTheory.Harmonic.EulerMascheroniBounds

/-! # Regression checks for explicit endpoint estimates and their hypotheses -/

namespace Real.Tests

open Real

example : eulerMascheroniConstant < (59 / 100 : ℝ) :=
  eulerMascheroniConstant_lt_59_div_100

end Real.Tests
