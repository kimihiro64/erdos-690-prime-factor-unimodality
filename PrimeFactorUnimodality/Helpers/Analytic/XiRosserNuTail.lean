import PrimeFactorUnimodality.Helpers.Analytic.XiRosserClosedBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedParameter

/-! # The complete Rosser tail at an exponential cutoff

Choosing `p=q-1/nu^2` discharges the free-exponent and turning-height
conditions. The exact closed expression retains both signs and every
cutoff multiplicity through the previously proved whole-tail theorem.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The elementary two-sided tail at `T=exp(nu*X)`, without an auxiliary exponent. -/
def xiRosserNuTailBound (X q ν : ℝ) : ℝ :=
  2 * exp (-q * (ν * X) - X / ν) *
    (logDampedNuIntegralFactor q ν X (2 * π) + 2 * (ν * X + 17))

/-- The exponential parameterization is an exact simplification of the closed majorant. -/
theorem xiRosserClosedTailBound_eq_nu {X q ν : ℝ}
    (hX : 0 < X) (hν : 0 < ν) (hmargin : 1 < (q - 1) * ν ^ 2) :
    xiRosserClosedTailBound (X ^ 2) q (q - 1 / ν ^ 2) (exp (ν * X)) =
      xiRosserNuTailBound X q ν := by
  unfold xiRosserClosedTailBound xiRosserNuTailBound
  rw [logDampedPowerMajorant_nu_mul_integralFactor hX hν (by positivity) hmargin,
    logDampedPower_nu hX hν, log_exp]
  ring

/-- The actual complete tail satisfies the parameterized estimate with its peak condition proved. -/
theorem xiRosserAbsoluteTail_le_nu {X q ν : ℝ}
    (hX : 0 < X) (hq : 2 ≤ q) (hν : 0 < ν) (hmargin : 1 < (q - 1) * ν ^ 2)
    (hT : 10 < exp (ν * X)) :
    xiRosserAbsoluteTail (X ^ 2) q (exp (ν * X)) ≤ xiRosserNuTailBound X q ν := by
  have hp := logDampedPower_nu_exponent_mem hν hmargin
  exact (xiRosserAbsoluteTail_le_closed (sq_nonneg X) hq hp.1 hp.2 hT
    (logDampedPower_nu_turn_le hX hν hmargin)).trans_eq
      (xiRosserClosedTailBound_eq_nu hX hν hmargin)

/-- The scalar bound is nonnegative on its complete parameter domain. -/
theorem xiRosserNuTailBound_nonneg {X q ν : ℝ}
    (hX : 0 < X) (hν : 0 < ν) (hmargin : 1 < (q - 1) * ν ^ 2)
    (hT : 10 < exp (ν * X)) : 0 ≤ xiRosserNuTailBound X q ν := by
  rw [← xiRosserClosedTailBound_eq_nu hX hν hmargin]
  exact xiRosserClosedTailBound_nonneg (logDampedPower_nu_exponent_mem hν hmargin).1 hT

end

end PrimeFactorUnimodality
