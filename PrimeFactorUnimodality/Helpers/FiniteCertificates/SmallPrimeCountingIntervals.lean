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

theorem dusartSmallUpperIntervalRow17_22 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 22 = 8 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 17) (right := 22) (a := 1) (b := 2) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow23_30 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 30 = 10 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 23) (right := 30) (a := 0) (b := 0) (c := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow31_40 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 40 = 12 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 31) (right := 40) (a := 5) (b := 0) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow41_46 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 46 = 14 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 41) (right := 46) (a := 0) (b := 2) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow47_58 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 58 = 16 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 47) (right := 58) (a := 4) (b := 1) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow59_66 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 66 = 18 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 59) (right := 66) (a := 6) (b := 0) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow67_72 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 72 = 20 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 67) (right := 72) (a := 0) (b := 1) (c := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow73_82 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 82 = 22 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 73) (right := 82) (a := 0) (b := 1) (c := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow83_96 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 96 = 24 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 83) (right := 96) (a := 5) (b := 1) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow97_106 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 106 = 27 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 97) (right := 106) (a := 2) (b := 0) (c := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow107_112 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 112 = 29 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 107) (right := 112) (a := 0) (b := 0) (c := 3)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow113_126 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 126 = 30 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 113) (right := 126) (a := 0) (b := 0) (c := 3)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

theorem dusartSmallUpperIntervalRow127_138 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 138 = 33 := by decide
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 127) (right := 138) (a := 0) (b := 3) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

end PrimeFactorUnimodality
