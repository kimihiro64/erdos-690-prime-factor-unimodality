import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapPrimeList

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Generated modular residues for the certified record-gap center. -/

namespace PrimeFactorUnimodality

theorem recordGapCenter_mod_two : recordGapCenter % 2 = 1 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_three : recordGapCenter % 3 = 2 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_five : recordGapCenter % 5 = 1 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_seven : recordGapCenter % 7 = 1 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_eleven : recordGapCenter % 11 = 4 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_44983 : recordGapCenter % 44983 = 39717 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_45541 : recordGapCenter % 45541 = 37619 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_52103 : recordGapCenter % 52103 = 32377 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_228523 : recordGapCenter % 228523 = 85050 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_550631 : recordGapCenter % 550631 = 86302 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_1129577 : recordGapCenter % 1129577 = 82320 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_1291193 : recordGapCenter % 1291193 = 82500 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

theorem recordGapCenter_mod_3020411447 :
    recordGapCenter % 3020411447 = 85750 := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList, Nat.mul_mod]

end PrimeFactorUnimodality
