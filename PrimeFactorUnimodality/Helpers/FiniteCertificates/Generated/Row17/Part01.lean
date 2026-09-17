import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes

/-! Generated segment 1 of the bounded selection row for endpoint 17. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow17_2 :
    selectionRowBounded 3 primePrefix2 =
      [1, 0, 0, 0] := by
  rfl

set_option linter.style.longLine false in
theorem numericalRow17_3 :
    selectionRowBounded 3 primePrefix3 =
      [1, 1, 0, 0] := by
  rw [primePrefix3, selectionRowBounded, numericalRow17_2]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow17_5 :
    selectionRowBounded 3 primePrefix5 =
      [2, 3, 1, 0] := by
  rw [primePrefix5, selectionRowBounded, numericalRow17_3]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow17_7 :
    selectionRowBounded 3 primePrefix7 =
      [8, 14, 7, 1] := by
  rw [primePrefix7, selectionRowBounded, numericalRow17_5]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow17_11 :
    selectionRowBounded 3 primePrefix11 =
      [48, 92, 56, 13] := by
  rw [primePrefix11, selectionRowBounded, numericalRow17_7]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow17_13 :
    selectionRowBounded 3 primePrefix13 =
      [480, 968, 652, 186] := by
  rw [primePrefix13, selectionRowBounded, numericalRow17_11]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow17_17 :
    selectionRowBounded 3 primePrefix17 =
      [5760, 12096, 8792, 2884] := by
  rw [primePrefix17, selectionRowBounded, numericalRow17_13]
  norm_num [selectionRowStep, selectionRowTail]

end PrimeFactorUnimodality
