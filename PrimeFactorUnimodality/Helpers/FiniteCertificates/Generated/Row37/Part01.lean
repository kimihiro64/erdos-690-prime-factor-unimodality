import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes

/-! Generated segment 1 of the bounded selection row for endpoint 37. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option linter.style.longLine false in
theorem numericalRow37_2 :
    selectionRowBounded 5 primePrefix2 =
      [1, 0, 0, 0, 0, 0] := by
  rfl

set_option linter.style.longLine false in
theorem numericalRow37_3 :
    selectionRowBounded 5 primePrefix3 =
      [1, 1, 0, 0, 0, 0] := by
  rw [primePrefix3, selectionRowBounded, numericalRow37_2]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_5 :
    selectionRowBounded 5 primePrefix5 =
      [2, 3, 1, 0, 0, 0] := by
  rw [primePrefix5, selectionRowBounded, numericalRow37_3]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_7 :
    selectionRowBounded 5 primePrefix7 =
      [8, 14, 7, 1, 0, 0] := by
  rw [primePrefix7, selectionRowBounded, numericalRow37_5]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_11 :
    selectionRowBounded 5 primePrefix11 =
      [48, 92, 56, 13, 1, 0] := by
  rw [primePrefix11, selectionRowBounded, numericalRow37_7]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_13 :
    selectionRowBounded 5 primePrefix13 =
      [480, 968, 652, 186, 23, 1] := by
  rw [primePrefix13, selectionRowBounded, numericalRow37_11]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_17 :
    selectionRowBounded 5 primePrefix17 =
      [5760, 12096, 8792, 2884, 462, 35] := by
  rw [primePrefix17, selectionRowBounded, numericalRow37_13]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_19 :
    selectionRowBounded 5 primePrefix19 =
      [92160, 199296, 152768, 54936, 10276, 1022] := by
  rw [primePrefix19, selectionRowBounded, numericalRow37_17]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_23 :
    selectionRowBounded 5 primePrefix23 =
      [1658880, 3679488, 2949120, 1141616, 239904, 28672] := by
  rw [primePrefix23, selectionRowBounded, numericalRow37_19]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_29 :
    selectionRowBounded 5 primePrefix29 =
      [36495360, 82607616, 68560128, 28064672, 6419504, 870688] := by
  rw [primePrefix29, selectionRowBounded, numericalRow37_23]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_31 :
    selectionRowBounded 5 primePrefix31 =
      [1021870080, 2349508608, 2002291200, 854370944, 207810784, 30798768] := by
  rw [primePrefix31, selectionRowBounded, numericalRow37_29]
  norm_num [selectionRowStep, selectionRowTail]

set_option linter.style.longLine false in
theorem numericalRow37_37 :
    selectionRowBounded 5 primePrefix37 =
      [30656102400, 71507128320, 62418244608, 27633419520, 7088694464, 1131773824] := by
  rw [primePrefix37, selectionRowBounded, numericalRow37_31]
  norm_num [selectionRowStep, selectionRowTail]

end PrimeFactorUnimodality
