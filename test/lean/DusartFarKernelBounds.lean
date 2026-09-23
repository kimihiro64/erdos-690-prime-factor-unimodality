import PrimeFactorUnimodality.Helpers.Analytic.DusartFarKernelBounds

/-! # Regression statements for the far-ray Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {X : ℝ} (hX : 28 ≤ X) :
    2 * xiRosserNuWindowBound X (4 / 5) ≤ 16 * X * exp (-(5 / 4 : ℝ) * X) := by
  apply PrimeFactorUnimodality.xiRosserNuWindowBound_four_fifths_le <;> assumption

example {X : ℝ} (hX : 28 ≤ X) :
    xiRosserSharpTailBound X 3 (4 / 5) ≤ 16 * X * exp (-(73 / 20 : ℝ) * X) := by
  apply PrimeFactorUnimodality.xiRosserSharpTailBound_four_fifths_le <;> assumption

end PrimeFactorUnimodality.Tests
