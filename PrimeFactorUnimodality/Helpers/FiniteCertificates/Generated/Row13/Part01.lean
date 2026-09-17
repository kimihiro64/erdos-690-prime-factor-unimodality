import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes

/-! Generated segment 1 of the bounded selection row for endpoint 13. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow13_2 :
    selectionRowBounded 3 primePrefix2 =
      [1, 0, 0, 0] := by
  rfl

set_option linter.style.longLine false in
theorem numericalRow13_3 :
    selectionRowBounded 3 primePrefix3 =
      [1, 1, 0, 0] := by
  rw [primePrefix3, selectionRowBounded, numericalRow13_2]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow13_5 :
    selectionRowBounded 3 primePrefix5 =
      [2, 3, 1, 0] := by
  rw [primePrefix5, selectionRowBounded, numericalRow13_3]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow13_7 :
    selectionRowBounded 3 primePrefix7 =
      [8, 14, 7, 1] := by
  rw [primePrefix7, selectionRowBounded, numericalRow13_5]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow13_11 :
    selectionRowBounded 3 primePrefix11 =
      [48, 92, 56, 13] := by
  rw [primePrefix11, selectionRowBounded, numericalRow13_7]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow13_13 :
    selectionRowBounded 3 primePrefix13 =
      [480, 968, 652, 186] := by
  rw [primePrefix13, selectionRowBounded, numericalRow13_11]
  norm_num [selectionRowStep, selectionRowTail]

end PrimeFactorUnimodality
