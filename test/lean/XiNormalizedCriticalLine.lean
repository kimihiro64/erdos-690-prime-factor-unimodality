import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiNormalizedCriticalLine

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example (t : ℝ) : 0 < xiCriticalLineScale t := by
  exact PrimeFactorUnimodality.xiCriticalLineScale_pos t

example (t : ℝ) :
    riemannXi ((1 / 2 : ℂ) + t * I) = (xiCriticalLineScale t : ℂ) *
      (exp (I * turingCountingPhase t) * riemannZeta ((1 / 2 : ℂ) + t * I)) := by
  exact PrimeFactorUnimodality.riemannXi_criticalLine_eq_scale_mul t

example (t : ℝ) :
    xiCriticalLineValue t = xiCriticalLineScale t * xiNormalizedValue t := by
  exact PrimeFactorUnimodality.xiCriticalLineValue_eq_scale_mul t

example (t : ℝ) :
    0 < xiCriticalLineValue t ↔ 0 < xiNormalizedValue t := by
  exact PrimeFactorUnimodality.xiCriticalLineValue_pos_iff_normalized t

example (t : ℝ) :
    xiCriticalLineValue t < 0 ↔ xiNormalizedValue t < 0 := by
  exact PrimeFactorUnimodality.xiCriticalLineValue_neg_iff_normalized t

example : 0 < xiCriticalLineScale 0 := xiCriticalLineScale_pos 0

example : 0 < xiCriticalLineScale (-14) := xiCriticalLineScale_pos (-14)

end

end PrimeFactorUnimodality.Tests
