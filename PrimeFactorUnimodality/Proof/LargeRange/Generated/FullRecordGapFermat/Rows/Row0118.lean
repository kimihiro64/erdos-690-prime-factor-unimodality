import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00118_values : List Nat :=
  [fullRecordGapCenterValue + 433038,
    fullRecordGapCenterValue + 433052,
    fullRecordGapCenterValue + 433106,
    fullRecordGapCenterValue + 433148,
    fullRecordGapCenterValue + 433190,
    fullRecordGapCenterValue + 433298,
    fullRecordGapCenterValue + 433406,
    fullRecordGapCenterValue + 433626,
    fullRecordGapCenterValue + 433658,
    fullRecordGapCenterValue + 433662,
    fullRecordGapCenterValue + 433718,
    fullRecordGapCenterValue + 433722,
    fullRecordGapCenterValue + 433802,
    fullRecordGapCenterValue + 433910,
    fullRecordGapCenterValue + 433970,
    fullRecordGapCenterValue + 434022,
    fullRecordGapCenterValue + 434046,
    fullRecordGapCenterValue + 434162,
    fullRecordGapCenterValue + 434222,
    fullRecordGapCenterValue + 434270,
    fullRecordGapCenterValue + 434438,
    fullRecordGapCenterValue + 434570,
    fullRecordGapCenterValue + 434702,
    fullRecordGapCenterValue + 434802,
    fullRecordGapCenterValue + 434822,
    fullRecordGapCenterValue + 434886,
    fullRecordGapCenterValue + 435146,
    fullRecordGapCenterValue + 435170,
    fullRecordGapCenterValue + 435282,
    fullRecordGapCenterValue + 435362,
    fullRecordGapCenterValue + 435542,
    fullRecordGapCenterValue + 435572,
    fullRecordGapCenterValue + 435668,
    fullRecordGapCenterValue + 435692,
    fullRecordGapCenterValue + 435716,
    fullRecordGapCenterValue + 435738,
    fullRecordGapCenterValue + 435752,
    fullRecordGapCenterValue + 435818,
    fullRecordGapCenterValue + 435836,
    fullRecordGapCenterValue + 435866,
    fullRecordGapCenterValue + 436026,
    fullRecordGapCenterValue + 436052,
    fullRecordGapCenterValue + 436070,
    fullRecordGapCenterValue + 436166,
    fullRecordGapCenterValue + 436242,
    fullRecordGapCenterValue + 436298,
    fullRecordGapCenterValue + 436466,
    fullRecordGapCenterValue + 436472,
    fullRecordGapCenterValue + 436490,
    fullRecordGapCenterValue + 436532,
    fullRecordGapCenterValue + 436556,
    fullRecordGapCenterValue + 436578,
    fullRecordGapCenterValue + 436602,
    fullRecordGapCenterValue + 436616,
    fullRecordGapCenterValue + 436782,
    fullRecordGapCenterValue + 436808,
    fullRecordGapCenterValue + 436838,
    fullRecordGapCenterValue + 437012,
    fullRecordGapCenterValue + 437042,
    fullRecordGapCenterValue + 437102,
    fullRecordGapCenterValue + 437252,
    fullRecordGapCenterValue + 437336,
    fullRecordGapCenterValue + 437406,
    fullRecordGapCenterValue + 437432]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00118_fermat : ∀ n ∈ fullRecordGapRow00118_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07489_not_prime : ¬(recordGapCenter + 433038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433038]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07490_not_prime : ¬(recordGapCenter + 433052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433052]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07491_not_prime : ¬(recordGapCenter + 433106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433106]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07492_not_prime : ¬(recordGapCenter + 433148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433148]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07493_not_prime : ¬(recordGapCenter + 433190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433190]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07494_not_prime : ¬(recordGapCenter + 433298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433298]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07495_not_prime : ¬(recordGapCenter + 433406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433406]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07496_not_prime : ¬(recordGapCenter + 433626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433626]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07497_not_prime : ¬(recordGapCenter + 433658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433658]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07498_not_prime : ¬(recordGapCenter + 433662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433662]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07499_not_prime : ¬(recordGapCenter + 433718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433718]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07500_not_prime : ¬(recordGapCenter + 433722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433722]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07501_not_prime : ¬(recordGapCenter + 433802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433802]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07502_not_prime : ¬(recordGapCenter + 433910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433910]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07503_not_prime : ¬(recordGapCenter + 433970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 433970]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07504_not_prime : ¬(recordGapCenter + 434022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434022]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07505_not_prime : ¬(recordGapCenter + 434046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434046]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07506_not_prime : ¬(recordGapCenter + 434162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434162]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07507_not_prime : ¬(recordGapCenter + 434222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434222]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07508_not_prime : ¬(recordGapCenter + 434270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434270]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07509_not_prime : ¬(recordGapCenter + 434438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434438]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07510_not_prime : ¬(recordGapCenter + 434570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434570]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07511_not_prime : ¬(recordGapCenter + 434702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434702]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07512_not_prime : ¬(recordGapCenter + 434802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434802]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07513_not_prime : ¬(recordGapCenter + 434822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434822]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07514_not_prime : ¬(recordGapCenter + 434886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 434886]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07515_not_prime : ¬(recordGapCenter + 435146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435146]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07516_not_prime : ¬(recordGapCenter + 435170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435170]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07517_not_prime : ¬(recordGapCenter + 435282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435282]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07518_not_prime : ¬(recordGapCenter + 435362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435362]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07519_not_prime : ¬(recordGapCenter + 435542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435542]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07520_not_prime : ¬(recordGapCenter + 435572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435572]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07521_not_prime : ¬(recordGapCenter + 435668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435668]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07522_not_prime : ¬(recordGapCenter + 435692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435692]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07523_not_prime : ¬(recordGapCenter + 435716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435716]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07524_not_prime : ¬(recordGapCenter + 435738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435738]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07525_not_prime : ¬(recordGapCenter + 435752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435752]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07526_not_prime : ¬(recordGapCenter + 435818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435818]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07527_not_prime : ¬(recordGapCenter + 435836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435836]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07528_not_prime : ¬(recordGapCenter + 435866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 435866]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07529_not_prime : ¬(recordGapCenter + 436026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436026]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07530_not_prime : ¬(recordGapCenter + 436052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436052]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07531_not_prime : ¬(recordGapCenter + 436070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436070]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07532_not_prime : ¬(recordGapCenter + 436166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436166]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07533_not_prime : ¬(recordGapCenter + 436242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436242]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07534_not_prime : ¬(recordGapCenter + 436298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436298]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07535_not_prime : ¬(recordGapCenter + 436466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436466]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07536_not_prime : ¬(recordGapCenter + 436472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436472]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07537_not_prime : ¬(recordGapCenter + 436490).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436490]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07538_not_prime : ¬(recordGapCenter + 436532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436532]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07539_not_prime : ¬(recordGapCenter + 436556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436556]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07540_not_prime : ¬(recordGapCenter + 436578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436578]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07541_not_prime : ¬(recordGapCenter + 436602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436602]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07542_not_prime : ¬(recordGapCenter + 436616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436616]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07543_not_prime : ¬(recordGapCenter + 436782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436782]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07544_not_prime : ¬(recordGapCenter + 436808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436808]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07545_not_prime : ¬(recordGapCenter + 436838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 436838]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07546_not_prime : ¬(recordGapCenter + 437012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437012]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07547_not_prime : ¬(recordGapCenter + 437042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437042]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07548_not_prime : ¬(recordGapCenter + 437102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437102]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07549_not_prime : ¬(recordGapCenter + 437252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437252]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07550_not_prime : ¬(recordGapCenter + 437336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437336]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07551_not_prime : ¬(recordGapCenter + 437406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437406]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

theorem fullRecordGapTerm07552_not_prime : ¬(recordGapCenter + 437432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437432]
  · apply fullRecordGapRow00118_fermat
    simp [fullRecordGapRow00118_values]

end PrimeFactorUnimodality
