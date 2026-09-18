import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00134_values : List Nat :=
  [fullRecordGapCenterValue + 507230,
    fullRecordGapCenterValue + 507278,
    fullRecordGapCenterValue + 507302,
    fullRecordGapCenterValue + 507306,
    fullRecordGapCenterValue + 507308,
    fullRecordGapCenterValue + 507356,
    fullRecordGapCenterValue + 507482,
    fullRecordGapCenterValue + 507512,
    fullRecordGapCenterValue + 507770,
    fullRecordGapCenterValue + 507890,
    fullRecordGapCenterValue + 507938,
    fullRecordGapCenterValue + 507956,
    fullRecordGapCenterValue + 507986,
    fullRecordGapCenterValue + 507992,
    fullRecordGapCenterValue + 508032,
    fullRecordGapCenterValue + 508082,
    fullRecordGapCenterValue + 508166,
    fullRecordGapCenterValue + 508278,
    fullRecordGapCenterValue + 508418,
    fullRecordGapCenterValue + 508490,
    fullRecordGapCenterValue + 508506,
    fullRecordGapCenterValue + 508562,
    fullRecordGapCenterValue + 508616,
    fullRecordGapCenterValue + 508652,
    fullRecordGapCenterValue + 508670,
    fullRecordGapCenterValue + 508712,
    fullRecordGapCenterValue + 508722,
    fullRecordGapCenterValue + 508730,
    fullRecordGapCenterValue + 508758,
    fullRecordGapCenterValue + 508778,
    fullRecordGapCenterValue + 508866,
    fullRecordGapCenterValue + 508868,
    fullRecordGapCenterValue + 509372,
    fullRecordGapCenterValue + 509426,
    fullRecordGapCenterValue + 509462,
    fullRecordGapCenterValue + 509672,
    fullRecordGapCenterValue + 509766,
    fullRecordGapCenterValue + 509822,
    fullRecordGapCenterValue + 509862,
    fullRecordGapCenterValue + 509918,
    fullRecordGapCenterValue + 509946,
    fullRecordGapCenterValue + 509948,
    fullRecordGapCenterValue + 509972,
    fullRecordGapCenterValue + 510038,
    fullRecordGapCenterValue + 510086,
    fullRecordGapCenterValue + 510126,
    fullRecordGapCenterValue + 510266,
    fullRecordGapCenterValue + 510300,
    fullRecordGapCenterValue + 510332,
    fullRecordGapCenterValue + 510366,
    fullRecordGapCenterValue + 510386,
    fullRecordGapCenterValue + 510392,
    fullRecordGapCenterValue + 510428,
    fullRecordGapCenterValue + 510470,
    fullRecordGapCenterValue + 510522,
    fullRecordGapCenterValue + 510546,
    fullRecordGapCenterValue + 510590,
    fullRecordGapCenterValue + 510618,
    fullRecordGapCenterValue + 510710,
    fullRecordGapCenterValue + 510722,
    fullRecordGapCenterValue + 510728,
    fullRecordGapCenterValue + 510812,
    fullRecordGapCenterValue + 510998,
    fullRecordGapCenterValue + 511022]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00134_fermat : ∀ n ∈ fullRecordGapRow00134_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08513_not_prime : ¬(recordGapCenter + 507230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507230]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08514_not_prime : ¬(recordGapCenter + 507278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507278]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08515_not_prime : ¬(recordGapCenter + 507302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507302]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08516_not_prime : ¬(recordGapCenter + 507306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507306]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08517_not_prime : ¬(recordGapCenter + 507308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507308]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08518_not_prime : ¬(recordGapCenter + 507356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507356]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08519_not_prime : ¬(recordGapCenter + 507482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507482]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08520_not_prime : ¬(recordGapCenter + 507512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507512]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08521_not_prime : ¬(recordGapCenter + 507770).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507770]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08522_not_prime : ¬(recordGapCenter + 507890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507890]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08523_not_prime : ¬(recordGapCenter + 507938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507938]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08524_not_prime : ¬(recordGapCenter + 507956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507956]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08525_not_prime : ¬(recordGapCenter + 507986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507986]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08526_not_prime : ¬(recordGapCenter + 507992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507992]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08527_not_prime : ¬(recordGapCenter + 508032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508032]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08528_not_prime : ¬(recordGapCenter + 508082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508082]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08529_not_prime : ¬(recordGapCenter + 508166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508166]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08530_not_prime : ¬(recordGapCenter + 508278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508278]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08531_not_prime : ¬(recordGapCenter + 508418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508418]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08532_not_prime : ¬(recordGapCenter + 508490).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508490]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08533_not_prime : ¬(recordGapCenter + 508506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508506]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08534_not_prime : ¬(recordGapCenter + 508562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508562]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08535_not_prime : ¬(recordGapCenter + 508616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508616]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08536_not_prime : ¬(recordGapCenter + 508652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508652]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08537_not_prime : ¬(recordGapCenter + 508670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508670]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08538_not_prime : ¬(recordGapCenter + 508712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508712]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08539_not_prime : ¬(recordGapCenter + 508722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508722]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08540_not_prime : ¬(recordGapCenter + 508730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508730]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08541_not_prime : ¬(recordGapCenter + 508758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508758]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08542_not_prime : ¬(recordGapCenter + 508778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508778]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08543_not_prime : ¬(recordGapCenter + 508866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508866]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08544_not_prime : ¬(recordGapCenter + 508868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 508868]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08545_not_prime : ¬(recordGapCenter + 509372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509372]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08546_not_prime : ¬(recordGapCenter + 509426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509426]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08547_not_prime : ¬(recordGapCenter + 509462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509462]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08548_not_prime : ¬(recordGapCenter + 509672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509672]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08549_not_prime : ¬(recordGapCenter + 509766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509766]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08550_not_prime : ¬(recordGapCenter + 509822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509822]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08551_not_prime : ¬(recordGapCenter + 509862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509862]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08552_not_prime : ¬(recordGapCenter + 509918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509918]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08553_not_prime : ¬(recordGapCenter + 509946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509946]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08554_not_prime : ¬(recordGapCenter + 509948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509948]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08555_not_prime : ¬(recordGapCenter + 509972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 509972]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08556_not_prime : ¬(recordGapCenter + 510038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510038]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08557_not_prime : ¬(recordGapCenter + 510086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510086]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08558_not_prime : ¬(recordGapCenter + 510126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510126]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08559_not_prime : ¬(recordGapCenter + 510266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510266]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08560_not_prime : ¬(recordGapCenter + 510300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510300]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08561_not_prime : ¬(recordGapCenter + 510332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510332]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08562_not_prime : ¬(recordGapCenter + 510366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510366]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08563_not_prime : ¬(recordGapCenter + 510386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510386]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08564_not_prime : ¬(recordGapCenter + 510392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510392]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08565_not_prime : ¬(recordGapCenter + 510428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510428]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08566_not_prime : ¬(recordGapCenter + 510470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510470]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08567_not_prime : ¬(recordGapCenter + 510522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510522]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08568_not_prime : ¬(recordGapCenter + 510546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510546]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08569_not_prime : ¬(recordGapCenter + 510590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510590]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08570_not_prime : ¬(recordGapCenter + 510618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510618]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08571_not_prime : ¬(recordGapCenter + 510710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510710]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08572_not_prime : ¬(recordGapCenter + 510722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510722]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08573_not_prime : ¬(recordGapCenter + 510728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510728]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08574_not_prime : ¬(recordGapCenter + 510812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510812]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08575_not_prime : ¬(recordGapCenter + 510998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 510998]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

theorem fullRecordGapTerm08576_not_prime : ¬(recordGapCenter + 511022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511022]
  · apply fullRecordGapRow00134_fermat
    simp [fullRecordGapRow00134_values]

end PrimeFactorUnimodality
