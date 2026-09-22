import Mathlib.Tactic
import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartPrimeCountingPrefix

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace PrimeFactorUnimodality

noncomputable section

/-! First compact small-range Dusart row.  The file is intentionally organized
as a list-row certificate surface: later rows can be appended without
duplicating the interval propagation proof. -/
def dusartSmallUpperIntervalRow10_16 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 16 = 6 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 10) (right := 16) (a := 1) (b := 0) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow17_22 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 22 = 8 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 17) (right := 22) (a := 1) (b := 2) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow23_30 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 30 = 10 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 23) (right := 30) (a := 3) (b := 1) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow31_40 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 40 = 12 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 31) (right := 40) (a := 5) (b := 0) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow41_46 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 46 = 14 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 41) (right := 46) (a := 0) (b := 2) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow47_58 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 58 = 16 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 47) (right := 58) (a := 4) (b := 1) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow59_66 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 66 = 18 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 59) (right := 66) (a := 6) (b := 0) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow67_72 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 72 = 20 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 67) (right := 72) (a := 0) (b := 1) (c := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow73_78 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 78 = 21 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 73) (right := 78) (a := 0) (b := 1) (c := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow79_88 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 88 = 23 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 79) (right := 88) (a := 4) (b := 0) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow89_100 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 100 = 25 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 89) (right := 100) (a := 1) (b := 2) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow107_112 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 112 = 29 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 107) (right := 112) (a := 2) (b := 3) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow101_106 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 106 = 27 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 101) (right := 106) (a := 0) (b := 1) (c := 1) (d := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow113 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  let U : Real := 4736228 / 1000000
  have hcount : Nat.primeCounting 113 = 30 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  refine {
    left := 113
    right := 113
    left_large := by norm_num
    left_le_right := by norm_num
    logUpper := U
    logUpper_pos := by norm_num [U]
    log_bound := ?_
    numerical := ?_ }
  · dsimp [U]
    have h := Real.log_lt_log (by norm_num : (0 : Real) < 113)
      (by norm_num : (113 : Real) < 114)
    rw [show (114 : Real) = 2 * (3 * 19) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)] at h
    nlinarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_19_lt]
  · rw [hcount]
    norm_num [U]

def dusartSmallUpperIntervalRow114_126 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 126 = 30 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 114) (right := 126) (a := 3) (b := 1) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow127_138 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 138 = 33 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 127) (right := 138) (a := 7) (b := 0) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow139_150 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 150 = 35 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 139) (right := 150) (a := 4) (b := 2) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow151_162 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 162 = 37 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 151) (right := 162) (a := 5) (b := 0) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow163_170 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 170 = 39 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 163) (right := 170) (a := 2) (b := 2) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow171_178 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 178 = 40 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 171) (right := 178) (a := 2) (b := 2) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow179_190 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 190 = 42 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 179) (right := 190) (a := 6) (b := 1) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow191_198 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 198 = 45 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 191) (right := 198) (a := 6) (b := 1) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow199_210 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 210 = 46 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 199) (right := 210) (a := 3) (b := 0) (c := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow211_226 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 226 = 48 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 211) (right := 226) (a := 0) (b := 2) (c := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow227_238 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 238 = 51 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 227) (right := 238) (a := 4) (b := 1) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow239_250 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 250 = 53 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 239) (right := 250) (a := 1) (b := 0) (c := 3)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow251_262 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 262 = 55 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 251) (right := 262) (a := 1) (b := 3) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow263_270 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 270 = 57 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 263) (right := 270) (a := 1) (b := 3) (c := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow277_282 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  let U : Real :=
    (3 : Real) * (693148 / 1000000 : Real) +
      (1609438 / 1000000 : Real) +
      (1946044 / 1000000 : Real)
  have hcount : Nat.primeCounting 282 = 60 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  refine {
    left := 277
    right := 282
    left_large := by norm_num
    left_le_right := by norm_num
    logUpper := U
    logUpper_pos := by dsimp [U]; norm_num
    log_bound := ?_
    numerical := ?_ }
  · dsimp [U]
    simpa using log_nat_le_smooth_upper_with_seven
      (n := 277) (a := 3) (b := 0) (c := 1) (d := 1) (by norm_num) (by norm_num)
  · rw [hcount]
    norm_num [U]

def dusartSmallUpperIntervalRow271_276 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 276 = 58 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 271) (right := 276) (a := 5) (b := 2) (c := 0) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow283_292 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 292 = 61 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    (left := 283) (right := 292) (a := 5) (b := 2) (c := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow293_310 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 310 = 63 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 293) (right := 310) (a := 1) (b := 1) (c := 0) (d := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow311_330 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 330 = 66 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 311) (right := 330) (a := 0) (b := 2) (c := 1) (d := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow331_348 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 348 = 69 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 331) (right := 348) (a := 4) (b := 1) (c := 0) (d := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow349_366 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 366 = 72 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 349) (right := 366) (a := 1) (b := 0) (c := 2) (d := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow367_382 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 382 = 75 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 367) (right := 382) (a := 0) (b := 1) (c := 3) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow383_400 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 400 = 78 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 383) (right := 400) (a := 7) (b := 1) (c := 0) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow401_418 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 418 = 80 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 401) (right := 418) (a := 0) (b := 4) (c := 1) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow419_438 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 438 = 84 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 419) (right := 438) (a := 2) (b := 1) (c := 1) (d := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow439_456 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 456 = 87 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 439) (right := 456) (a := 0) (b := 2) (c := 0) (d := 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow457_462 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 462 = 89 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 457) (right := 462) (a := 5) (b := 1) (c := 1) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow463_466 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 466 = 90 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 463) (right := 466) (a := 5) (b := 1) (c := 1) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow467_478 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 478 = 91 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 467) (right := 478) (a := 5) (b := 1) (c := 1) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow479_490 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 490 = 93 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 479) (right := 490) (a := 5) (b := 1) (c := 1) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow491_502 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 502 = 95 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 491) (right := 502) (a := 2) (b := 0) (c := 3) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow503_520 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 520 = 97 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 503) (right := 520) (a := 3) (b := 2) (c := 0) (d := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow521_546 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 546 = 100 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 521) (right := 546) (a := 0) (b := 1) (c := 2) (d := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow547_568 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 568 = 103 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 547) (right := 568) (a := 4) (b := 0) (c := 1) (d := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow569_592 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 592 = 107 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 569) (right := 592) (a := 6) (b := 2) (c := 0) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRow593_598 :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  have hcount : Nat.primeCounting 598 = 108 := by
    rw [dusart_primeCounting_eq_filtered_1000 (by decide)]
    decide +kernel
  apply dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    (left := 593) (right := 598) (a := 3) (b := 1) (c := 2) (d := 0)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [hcount]
    norm_num

def dusartSmallUpperIntervalRows :
    List DusartPrimeCountingUpperIntegerIntervalRow :=
  [ dusartSmallUpperIntervalRow10_16
  , dusartSmallUpperIntervalRow17_22
  , dusartSmallUpperIntervalRow23_30
  , dusartSmallUpperIntervalRow31_40
  , dusartSmallUpperIntervalRow41_46
  , dusartSmallUpperIntervalRow47_58
  , dusartSmallUpperIntervalRow59_66
  , dusartSmallUpperIntervalRow67_72
  , dusartSmallUpperIntervalRow73_78
  , dusartSmallUpperIntervalRow79_88
  , dusartSmallUpperIntervalRow89_100
  , dusartSmallUpperIntervalRow101_106
  , dusartSmallUpperIntervalRow107_112
  , dusartSmallUpperIntervalRow113
  , dusartSmallUpperIntervalRow114_126
  , dusartSmallUpperIntervalRow127_138
  , dusartSmallUpperIntervalRow139_150
  , dusartSmallUpperIntervalRow151_162
  , dusartSmallUpperIntervalRow163_170
  , dusartSmallUpperIntervalRow171_178
  , dusartSmallUpperIntervalRow179_190
  , dusartSmallUpperIntervalRow191_198
  , dusartSmallUpperIntervalRow199_210
  , dusartSmallUpperIntervalRow211_226
  , dusartSmallUpperIntervalRow227_238
  , dusartSmallUpperIntervalRow239_250
  , dusartSmallUpperIntervalRow251_262
  , dusartSmallUpperIntervalRow263_270
  , dusartSmallUpperIntervalRow271_276
  , dusartSmallUpperIntervalRow277_282
  , dusartSmallUpperIntervalRow283_292
  , dusartSmallUpperIntervalRow293_310
  , dusartSmallUpperIntervalRow311_330
  , dusartSmallUpperIntervalRow331_348
  , dusartSmallUpperIntervalRow349_366
  , dusartSmallUpperIntervalRow367_382
  , dusartSmallUpperIntervalRow383_400
  , dusartSmallUpperIntervalRow401_418
  , dusartSmallUpperIntervalRow419_438
  , dusartSmallUpperIntervalRow439_456
  , dusartSmallUpperIntervalRow457_462
  , dusartSmallUpperIntervalRow463_466
  , dusartSmallUpperIntervalRow467_478
  , dusartSmallUpperIntervalRow479_490
  , dusartSmallUpperIntervalRow491_502
  , dusartSmallUpperIntervalRow503_520
  , dusartSmallUpperIntervalRow521_546
  , dusartSmallUpperIntervalRow547_568
  , dusartSmallUpperIntervalRow569_592
  , dusartSmallUpperIntervalRow593_598 ]

theorem dusartSmallUpperIntervalRows_cover :
    DusartPrimeCountingUpperIntegerIntervalRowsCover dusartSmallUpperIntervalRows := by
  have chain : natClosedIntervalChain 10 598
      (dusartSmallUpperIntervalRows.map (fun row => (row.left, row.right))) = true := by
    decide +kernel
  intro n hn10 hn599
  obtain ⟨pair, hpair, hleft, hright⟩ := natClosedIntervalChain_covers chain hn10 (by omega)
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hpair
  exact ⟨row, hrow, hleft, hright⟩

theorem dusartSmallUpperIntervalRows_provide :
    ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x := by
  exact real_primeCounting_upper_of_integer_interval_rows
    dusartSmallUpperIntervalRows_cover

end

end PrimeFactorUnimodality
