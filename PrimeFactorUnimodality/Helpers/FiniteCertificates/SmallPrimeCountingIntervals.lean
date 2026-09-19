import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting

set_option autoImplicit false

namespace PrimeFactorUnimodality

/-! First compact small-range Dusart row.  The file is intentionally organized
as a list-row certificate surface: later rows can be appended without
duplicating the interval propagation proof. -/
theorem dusartSmallUpperIntervalRow10_16 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 16 = 6 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 10) (right := 16) (a := 1) (b := 0) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

end PrimeFactorUnimodality
