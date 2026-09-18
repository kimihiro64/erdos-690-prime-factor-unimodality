import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00106_values : List Nat :=
  [fullRecordGapCenterValue + 373242,
    fullRecordGapCenterValue + 373278,
    fullRecordGapCenterValue + 373448,
    fullRecordGapCenterValue + 373508,
    fullRecordGapCenterValue + 373532,
    fullRecordGapCenterValue + 373586,
    fullRecordGapCenterValue + 373628,
    fullRecordGapCenterValue + 373676,
    fullRecordGapCenterValue + 373718,
    fullRecordGapCenterValue + 373766,
    fullRecordGapCenterValue + 373866,
    fullRecordGapCenterValue + 373938,
    fullRecordGapCenterValue + 373962,
    fullRecordGapCenterValue + 374082,
    fullRecordGapCenterValue + 374138,
    fullRecordGapCenterValue + 374162,
    fullRecordGapCenterValue + 374222,
    fullRecordGapCenterValue + 374228,
    fullRecordGapCenterValue + 374246,
    fullRecordGapCenterValue + 374298,
    fullRecordGapCenterValue + 374406,
    fullRecordGapCenterValue + 374456,
    fullRecordGapCenterValue + 374732,
    fullRecordGapCenterValue + 374862,
    fullRecordGapCenterValue + 374936,
    fullRecordGapCenterValue + 375006,
    fullRecordGapCenterValue + 375026,
    fullRecordGapCenterValue + 375236,
    fullRecordGapCenterValue + 375302,
    fullRecordGapCenterValue + 375546,
    fullRecordGapCenterValue + 375548,
    fullRecordGapCenterValue + 375656,
    fullRecordGapCenterValue + 375722,
    fullRecordGapCenterValue + 375798,
    fullRecordGapCenterValue + 375842,
    fullRecordGapCenterValue + 375902,
    fullRecordGapCenterValue + 376098,
    fullRecordGapCenterValue + 376122,
    fullRecordGapCenterValue + 376136,
    fullRecordGapCenterValue + 376338,
    fullRecordGapCenterValue + 376358,
    fullRecordGapCenterValue + 376386,
    fullRecordGapCenterValue + 376458,
    fullRecordGapCenterValue + 376472,
    fullRecordGapCenterValue + 376518,
    fullRecordGapCenterValue + 376622,
    fullRecordGapCenterValue + 376638,
    fullRecordGapCenterValue + 376646,
    fullRecordGapCenterValue + 376806,
    fullRecordGapCenterValue + 376862,
    fullRecordGapCenterValue + 377066,
    fullRecordGapCenterValue + 377106,
    fullRecordGapCenterValue + 377300,
    fullRecordGapCenterValue + 377372,
    fullRecordGapCenterValue + 377382,
    fullRecordGapCenterValue + 377402,
    fullRecordGapCenterValue + 377438,
    fullRecordGapCenterValue + 377588,
    fullRecordGapCenterValue + 377708,
    fullRecordGapCenterValue + 377738,
    fullRecordGapCenterValue + 377756,
    fullRecordGapCenterValue + 377822,
    fullRecordGapCenterValue + 377826,
    fullRecordGapCenterValue + 377898]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00106_fermat : ∀ n ∈ fullRecordGapRow00106_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06721_not_prime : ¬(recordGapCenter + 373242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373242]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06722_not_prime : ¬(recordGapCenter + 373278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373278]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06723_not_prime : ¬(recordGapCenter + 373448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373448]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06724_not_prime : ¬(recordGapCenter + 373508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373508]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06725_not_prime : ¬(recordGapCenter + 373532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373532]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06726_not_prime : ¬(recordGapCenter + 373586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373586]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06727_not_prime : ¬(recordGapCenter + 373628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373628]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06728_not_prime : ¬(recordGapCenter + 373676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373676]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06729_not_prime : ¬(recordGapCenter + 373718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373718]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06730_not_prime : ¬(recordGapCenter + 373766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373766]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06731_not_prime : ¬(recordGapCenter + 373866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373866]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06732_not_prime : ¬(recordGapCenter + 373938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373938]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06733_not_prime : ¬(recordGapCenter + 373962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373962]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06734_not_prime : ¬(recordGapCenter + 374082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374082]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06735_not_prime : ¬(recordGapCenter + 374138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374138]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06736_not_prime : ¬(recordGapCenter + 374162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374162]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06737_not_prime : ¬(recordGapCenter + 374222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374222]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06738_not_prime : ¬(recordGapCenter + 374228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374228]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06739_not_prime : ¬(recordGapCenter + 374246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374246]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06740_not_prime : ¬(recordGapCenter + 374298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374298]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06741_not_prime : ¬(recordGapCenter + 374406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374406]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06742_not_prime : ¬(recordGapCenter + 374456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374456]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06743_not_prime : ¬(recordGapCenter + 374732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374732]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06744_not_prime : ¬(recordGapCenter + 374862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374862]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06745_not_prime : ¬(recordGapCenter + 374936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374936]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06746_not_prime : ¬(recordGapCenter + 375006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375006]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06747_not_prime : ¬(recordGapCenter + 375026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375026]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06748_not_prime : ¬(recordGapCenter + 375236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375236]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06749_not_prime : ¬(recordGapCenter + 375302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375302]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06750_not_prime : ¬(recordGapCenter + 375546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375546]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06751_not_prime : ¬(recordGapCenter + 375548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375548]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06752_not_prime : ¬(recordGapCenter + 375656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375656]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06753_not_prime : ¬(recordGapCenter + 375722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375722]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06754_not_prime : ¬(recordGapCenter + 375798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375798]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06755_not_prime : ¬(recordGapCenter + 375842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375842]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06756_not_prime : ¬(recordGapCenter + 375902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375902]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06757_not_prime : ¬(recordGapCenter + 376098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376098]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06758_not_prime : ¬(recordGapCenter + 376122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376122]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06759_not_prime : ¬(recordGapCenter + 376136).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376136]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06760_not_prime : ¬(recordGapCenter + 376338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376338]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06761_not_prime : ¬(recordGapCenter + 376358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376358]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06762_not_prime : ¬(recordGapCenter + 376386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376386]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06763_not_prime : ¬(recordGapCenter + 376458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376458]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06764_not_prime : ¬(recordGapCenter + 376472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376472]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06765_not_prime : ¬(recordGapCenter + 376518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376518]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06766_not_prime : ¬(recordGapCenter + 376622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376622]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06767_not_prime : ¬(recordGapCenter + 376638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376638]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06768_not_prime : ¬(recordGapCenter + 376646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376646]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06769_not_prime : ¬(recordGapCenter + 376806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376806]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06770_not_prime : ¬(recordGapCenter + 376862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376862]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06771_not_prime : ¬(recordGapCenter + 377066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377066]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06772_not_prime : ¬(recordGapCenter + 377106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377106]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06773_not_prime : ¬(recordGapCenter + 377300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377300]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06774_not_prime : ¬(recordGapCenter + 377372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377372]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06775_not_prime : ¬(recordGapCenter + 377382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377382]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06776_not_prime : ¬(recordGapCenter + 377402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377402]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06777_not_prime : ¬(recordGapCenter + 377438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377438]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06778_not_prime : ¬(recordGapCenter + 377588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377588]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06779_not_prime : ¬(recordGapCenter + 377708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377708]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06780_not_prime : ¬(recordGapCenter + 377738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377738]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06781_not_prime : ¬(recordGapCenter + 377756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377756]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06782_not_prime : ¬(recordGapCenter + 377822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377822]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06783_not_prime : ¬(recordGapCenter + 377826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377826]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

theorem fullRecordGapTerm06784_not_prime : ¬(recordGapCenter + 377898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377898]
  · apply fullRecordGapRow00106_fermat
    simp [fullRecordGapRow00106_values]

end PrimeFactorUnimodality
