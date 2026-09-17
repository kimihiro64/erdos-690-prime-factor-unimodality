import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes

/-! Generated segment 1 of the bounded selection row for endpoint 31. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow31_2 :
    selectionRowBounded 5 primePrefix2 =
      [1, 0, 0, 0, 0, 0] := by
  rfl

set_option linter.style.longLine false in
theorem numericalRow31_3 :
    selectionRowBounded 5 primePrefix3 =
      [1, 1, 0, 0, 0, 0] := by
  rw [primePrefix3, selectionRowBounded, numericalRow31_2]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_5 :
    selectionRowBounded 5 primePrefix5 =
      [2, 3, 1, 0, 0, 0] := by
  rw [primePrefix5, selectionRowBounded, numericalRow31_3]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_7 :
    selectionRowBounded 5 primePrefix7 =
      [8, 14, 7, 1, 0, 0] := by
  rw [primePrefix7, selectionRowBounded, numericalRow31_5]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_11 :
    selectionRowBounded 5 primePrefix11 =
      [48, 92, 56, 13, 1, 0] := by
  rw [primePrefix11, selectionRowBounded, numericalRow31_7]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_13 :
    selectionRowBounded 5 primePrefix13 =
      [480, 968, 652, 186, 23, 1] := by
  rw [primePrefix13, selectionRowBounded, numericalRow31_11]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_17 :
    selectionRowBounded 5 primePrefix17 =
      [5760, 12096, 8792, 2884, 462, 35] := by
  rw [primePrefix17, selectionRowBounded, numericalRow31_13]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_19 :
    selectionRowBounded 5 primePrefix19 =
      [92160, 199296, 152768, 54936, 10276, 1022] := by
  rw [primePrefix19, selectionRowBounded, numericalRow31_17]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_23 :
    selectionRowBounded 5 primePrefix23 =
      [1658880, 3679488, 2949120, 1141616, 239904, 28672] := by
  rw [primePrefix23, selectionRowBounded, numericalRow31_19]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_29 :
    selectionRowBounded 5 primePrefix29 =
      [36495360, 82607616, 68560128, 28064672, 6419504, 870688] := by
  rw [primePrefix29, selectionRowBounded, numericalRow31_23]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow31_31 :
    selectionRowBounded 5 primePrefix31 =
      [1021870080, 2349508608, 2002291200, 854370944, 207810784, 30798768] := by
  rw [primePrefix31, selectionRowBounded, numericalRow31_29]
  norm_num [selectionRowStep, selectionRowTail]

end PrimeFactorUnimodality
