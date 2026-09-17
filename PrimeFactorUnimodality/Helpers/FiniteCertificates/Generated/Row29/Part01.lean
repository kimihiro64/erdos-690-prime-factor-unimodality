import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes

/-! Generated segment 1 of the bounded selection row for endpoint 29. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow29_2 :
    selectionRowBounded 4 primePrefix2 =
      [1, 0, 0, 0, 0] := by
  rfl

set_option linter.style.longLine false in
theorem numericalRow29_3 :
    selectionRowBounded 4 primePrefix3 =
      [1, 1, 0, 0, 0] := by
  rw [primePrefix3, selectionRowBounded, numericalRow29_2]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow29_5 :
    selectionRowBounded 4 primePrefix5 =
      [2, 3, 1, 0, 0] := by
  rw [primePrefix5, selectionRowBounded, numericalRow29_3]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow29_7 :
    selectionRowBounded 4 primePrefix7 =
      [8, 14, 7, 1, 0] := by
  rw [primePrefix7, selectionRowBounded, numericalRow29_5]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow29_11 :
    selectionRowBounded 4 primePrefix11 =
      [48, 92, 56, 13, 1] := by
  rw [primePrefix11, selectionRowBounded, numericalRow29_7]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow29_13 :
    selectionRowBounded 4 primePrefix13 =
      [480, 968, 652, 186, 23] := by
  rw [primePrefix13, selectionRowBounded, numericalRow29_11]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow29_17 :
    selectionRowBounded 4 primePrefix17 =
      [5760, 12096, 8792, 2884, 462] := by
  rw [primePrefix17, selectionRowBounded, numericalRow29_13]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow29_19 :
    selectionRowBounded 4 primePrefix19 =
      [92160, 199296, 152768, 54936, 10276] := by
  rw [primePrefix19, selectionRowBounded, numericalRow29_17]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow29_23 :
    selectionRowBounded 4 primePrefix23 =
      [1658880, 3679488, 2949120, 1141616, 239904] := by
  rw [primePrefix23, selectionRowBounded, numericalRow29_19]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow29_29 :
    selectionRowBounded 4 primePrefix29 =
      [36495360, 82607616, 68560128, 28064672, 6419504] := by
  rw [primePrefix29, selectionRowBounded, numericalRow29_23]
  norm_num [selectionRowStep, selectionRowTail]

end PrimeFactorUnimodality
