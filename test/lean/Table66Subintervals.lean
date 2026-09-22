import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosedPart01
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66EndpointFacts

set_option autoImplicit false

/-! # Regression checks for the theta-table coverage boundary

These cells test only coverage, not theta values. Valid theta enclosures
remain a separate obligation and cannot follow from coverage alone.
-/

namespace PrimeFactorUnimodality.Tests

private def first : DusartThetaTable66Cell := ⟨10, 20, 0, 0⟩
private def second : DusartThetaTable66Cell := ⟨20, 30, 0, 0⟩
private def gap : DusartThetaTable66Cell := ⟨21, 30, 0, 0⟩
private def overlap : DusartThetaTable66Cell := ⟨19, 30, 0, 0⟩

example : dusartThetaTable66CellsChain 10 30 [first, second] = true := by decide
example : dusartThetaTable66CellsChain 10 30 [first, gap] = false := by decide
example : dusartThetaTable66CellsChain 10 30 [first, overlap] = false := by decide
example : dusartThetaTable66CellsChain 10 30 [second, first] = false := by decide
example : dusartThetaTable66CellsChain 10 20 [first] = true := by decide
example : dusartThetaTable66CellsChain 10 30 [] = false := by decide

example {x : Real} (hx : 10 ≤ x) (hy : x ≤ 30) :
    ∃ cell ∈ [first, second], (cell.left : Real) ≤ x ∧ x ≤ cell.right :=
  dusartThetaTable66CellsChain_covers (by decide) hx hy

example :
    ¬ (Chebyshev.theta (100000000 : Real) ≤ (99998 / 100000 : Real) * 100000000 ∧
      (200000000 : Real) - (275 / 100000 : Real) * 200000000 /
        Real.log 200000000 ≤ Chebyshev.theta (100000000 : Real)) :=
  dusartTable66_first_row_whole_endpoint_impossible

example : |Chebyshev.theta (5 / 2) - 5 / 2| <
    (12323 / 10000 : Real) * (5 / 2) / Real.log (5 / 2) :=
  dusartThetaBoundsBelow_three.2 _ (by norm_num) (by norm_num)

example {x : Real} (hx : 0 < x) (hX : x ≤ 29) : Chebyshev.theta x < x :=
  wangCrapis_strictThetaPrefix_twenty_nine x hx hX

example {x : Real} (hx : 2 < x) (hX : x ≤ 7) :
    |Chebyshev.theta x - x| < (12323 / 10000 : Real) * x / Real.log x :=
  wangCrapis_thetaBoundsBelow_7.2 x hx hX

example : ∃ data ∈ dusartThetaTable6_6CoefficientData,
    (data.left : Real) ≤ 399999999 / 2 ∧ (399999999 / 2 : Real) ≤ data.right :=
  dusartThetaTable6_6CoefficientData_cover_real _ (by norm_num) (by norm_num)

end PrimeFactorUnimodality.Tests
