import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes

/-! Generated segment 1 of the bounded selection row for endpoint 23. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow23_2 :
    selectionRowBounded 4 primePrefix2 =
      [1, 0, 0, 0, 0] := by
  rfl

set_option linter.style.longLine false in
theorem numericalRow23_3 :
    selectionRowBounded 4 primePrefix3 =
      [1, 1, 0, 0, 0] := by
  rw [primePrefix3, selectionRowBounded, numericalRow23_2]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow23_5 :
    selectionRowBounded 4 primePrefix5 =
      [2, 3, 1, 0, 0] := by
  rw [primePrefix5, selectionRowBounded, numericalRow23_3]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow23_7 :
    selectionRowBounded 4 primePrefix7 =
      [8, 14, 7, 1, 0] := by
  rw [primePrefix7, selectionRowBounded, numericalRow23_5]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow23_11 :
    selectionRowBounded 4 primePrefix11 =
      [48, 92, 56, 13, 1] := by
  rw [primePrefix11, selectionRowBounded, numericalRow23_7]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow23_13 :
    selectionRowBounded 4 primePrefix13 =
      [480, 968, 652, 186, 23] := by
  rw [primePrefix13, selectionRowBounded, numericalRow23_11]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow23_17 :
    selectionRowBounded 4 primePrefix17 =
      [5760, 12096, 8792, 2884, 462] := by
  rw [primePrefix17, selectionRowBounded, numericalRow23_13]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow23_19 :
    selectionRowBounded 4 primePrefix19 =
      [92160, 199296, 152768, 54936, 10276] := by
  rw [primePrefix19, selectionRowBounded, numericalRow23_17]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow23_23 :
    selectionRowBounded 4 primePrefix23 =
      [1658880, 3679488, 2949120, 1141616, 239904] := by
  rw [primePrefix23, selectionRowBounded, numericalRow23_19]
  norm_num [selectionRowStep, selectionRowTail]

end PrimeFactorUnimodality
