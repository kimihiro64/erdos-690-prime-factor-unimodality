import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSharpTail

/-! # Regression tests for sharp Rosser tail estimates -/

namespace PrimeFactorUnimodality.Tests

open Real

example {X m ν : ℝ}
    (hX : 0 < X) (hm : 1 ≤ m) (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / m + sqrt (X ^ 2 / m))
    (hT : 10 < exp (ν * X)) :
    2 * (xiRosserTailIntegral (X ^ 2) (m + 1) (exp (ν * X)) +
      2 * (Real.log (exp (ν * X)) + 17) *
        logDampedPower (X ^ 2) (m + 1) (exp (ν * X))) ≤
      xiRosserSharpTailBound X m ν :=
  xiRosserTailIntegral_boundary_le_sharp hX hm hν hmargin hparam hT

example {X m ν : ℝ}
    (hX : 0 < X) (hm : 1 ≤ m) (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / m + sqrt (X ^ 2 / m))
    (hT : 10 < exp (ν * X)) :
    xiRosserAbsoluteTail (X ^ 2) (m + 1) (exp (ν * X)) ≤ xiRosserSharpTailBound X m ν :=
  xiRosserAbsoluteTail_le_sharp hX hm hν hmargin hparam hT

example {X m ν : ℝ}
    (hX : 0 < X) (hm : 1 ≤ m) (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / m + sqrt (X ^ 2 / m))
    (hT : 10 < exp (ν * X)) : 0 ≤ xiRosserSharpTailBound X m ν :=
  xiRosserSharpTailBound_nonneg hX hm hν hmargin hparam hT

-- Unlike the finite increasing band, a tail alone does not require nu <= 1.
example {X : ℝ} (hX : 0 < X)
    (hparam : Real.log (2 * π) ≤ 1 + sqrt (X ^ 2)) (hT : 10 < exp (2 * X)) :
    xiRosserAbsoluteTail (X ^ 2) 2 (exp (2 * X)) ≤ xiRosserSharpTailBound X 1 2 := by
  have h := xiRosserAbsoluteTail_le_sharp (m := 1) (ν := 2) hX (by norm_num)
    (by norm_num) (by norm_num) (by simpa using hparam) hT
  norm_num at h
  exact h

-- The singular turning-height boundary cannot satisfy the strict margin.
example {X m ν : ℝ} (he : m * ν ^ 2 = 1) :
    ¬ X ^ 2 < m * Real.log (exp (ν * X)) ^ 2 := by
  rw [Real.log_exp]
  have he' : m * (ν * X) ^ 2 = X ^ 2 := by
    calc
      _ = (m * ν ^ 2) * X ^ 2 := by ring
      _ = _ := by rw [he, one_mul]
  rw [he']
  exact lt_irrefl _

end PrimeFactorUnimodality.Tests
