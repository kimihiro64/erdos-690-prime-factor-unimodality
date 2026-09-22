import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Subintervals

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

end PrimeFactorUnimodality.Tests
