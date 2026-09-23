import PrimeFactorUnimodality.Helpers.Analytic.XiRosserNuTail
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSharpTail

/-! # Comparing the sharp Rosser tail with the power majorant

The reciprocal correction and counting boundary agree exactly. The
density coefficient is smaller after multiplication by positive factors.
The paper's parameter condition is exposed as a lower bound on `X`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The sharp scalar tail never exceeds the previous power-majorant tail. -/
theorem xiRosserSharpTailBound_le_nu {X m ν : ℝ}
    (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2) :
    xiRosserSharpTailBound X m ν ≤ xiRosserNuTailBound X (m + 1) ν := by
  have he : exp (-m * (ν * X) - X / ν) =
      exp (-(m + 1) * (ν * X) - X / ν) * exp (ν * X) := by
    rw [← exp_add]
    congr 1
    ring
  have hf := logDampedTail_factor_le_power (L := ν * X - Real.log (2 * π)) hν hmargin
  have hc := mul_le_mul_of_nonneg_left hf
    (by positivity : 0 ≤ 2 * exp (-(m + 1) * (ν * X) - X / ν) * (exp (ν * X) / (2 * π)))
  unfold xiRosserSharpTailBound xiRosserNuTailBound logDampedNuIntegralFactor
  rw [he, show m + 1 - 1 / ν ^ 2 - 1 = m - 1 / ν ^ 2 by ring]
  linear_combination hc

/-- The actual tail estimate can use the paper's explicit lower bound on the root parameter. -/
theorem xiRosserAbsoluteTail_le_sharp_of_parameter {X m ν : ℝ}
    (hX : 0 < X) (hm : 1 ≤ m) (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2)
    (hparam : (m * Real.log (2 * π) - 1) / sqrt m ≤ X)
    (hT : 10 < exp (ν * X)) :
    xiRosserAbsoluteTail (X ^ 2) (m + 1) (exp (ν * X)) ≤ xiRosserSharpTailBound X m ν :=
  xiRosserAbsoluteTail_le_sharp hX hm hν hmargin
    ((logDampedTail_parameter_iff hX.le (by linarith)).mpr hparam) hT

end

end PrimeFactorUnimodality
