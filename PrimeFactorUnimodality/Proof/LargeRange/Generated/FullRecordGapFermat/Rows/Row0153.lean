import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00153_values : List Nat :=
  [fullRecordGapCenterValue + 584538,
    fullRecordGapCenterValue + 584718,
    fullRecordGapCenterValue + 584726,
    fullRecordGapCenterValue + 584762,
    fullRecordGapCenterValue + 584810,
    fullRecordGapCenterValue + 584882,
    fullRecordGapCenterValue + 584978,
    fullRecordGapCenterValue + 585006,
    fullRecordGapCenterValue + 585012,
    fullRecordGapCenterValue + 585062,
    fullRecordGapCenterValue + 585098,
    fullRecordGapCenterValue + 585138,
    fullRecordGapCenterValue + 585146,
    fullRecordGapCenterValue + 585188,
    fullRecordGapCenterValue + 585348,
    fullRecordGapCenterValue + 585426,
    fullRecordGapCenterValue + 585498,
    fullRecordGapCenterValue + 585506,
    fullRecordGapCenterValue + 585512,
    fullRecordGapCenterValue + 585588,
    fullRecordGapCenterValue + 585642,
    fullRecordGapCenterValue + 585692,
    fullRecordGapCenterValue + 585758,
    fullRecordGapCenterValue + 585818,
    fullRecordGapCenterValue + 585866,
    fullRecordGapCenterValue + 585876,
    fullRecordGapCenterValue + 585896,
    fullRecordGapCenterValue + 585938,
    fullRecordGapCenterValue + 585986,
    fullRecordGapCenterValue + 586052,
    fullRecordGapCenterValue + 586122,
    fullRecordGapCenterValue + 586266,
    fullRecordGapCenterValue + 586310,
    fullRecordGapCenterValue + 586328,
    fullRecordGapCenterValue + 586412,
    fullRecordGapCenterValue + 586436,
    fullRecordGapCenterValue + 586442,
    fullRecordGapCenterValue + 586526,
    fullRecordGapCenterValue + 586596,
    fullRecordGapCenterValue + 586616,
    fullRecordGapCenterValue + 586622,
    fullRecordGapCenterValue + 586668,
    fullRecordGapCenterValue + 586722,
    fullRecordGapCenterValue + 586826,
    fullRecordGapCenterValue + 586862,
    fullRecordGapCenterValue + 587058,
    fullRecordGapCenterValue + 587228,
    fullRecordGapCenterValue + 587402,
    fullRecordGapCenterValue + 587436,
    fullRecordGapCenterValue + 587546,
    fullRecordGapCenterValue + 587658,
    fullRecordGapCenterValue + 587816,
    fullRecordGapCenterValue + 587966,
    fullRecordGapCenterValue + 588000,
    fullRecordGapCenterValue + 588036,
    fullRecordGapCenterValue + 588066,
    fullRecordGapCenterValue + 588108,
    fullRecordGapCenterValue + 588206,
    fullRecordGapCenterValue + 588282,
    fullRecordGapCenterValue + 588332,
    fullRecordGapCenterValue + 588362,
    fullRecordGapCenterValue + 588396,
    fullRecordGapCenterValue + 588422,
    fullRecordGapCenterValue + 588446]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00153_fermat : ∀ n ∈ fullRecordGapRow00153_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09729_not_prime : ¬(recordGapCenter + 584538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584538]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09730_not_prime : ¬(recordGapCenter + 584718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584718]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09731_not_prime : ¬(recordGapCenter + 584726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584726]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09732_not_prime : ¬(recordGapCenter + 584762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584762]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09733_not_prime : ¬(recordGapCenter + 584810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584810]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09734_not_prime : ¬(recordGapCenter + 584882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584882]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09735_not_prime : ¬(recordGapCenter + 584978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584978]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09736_not_prime : ¬(recordGapCenter + 585006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585006]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09737_not_prime : ¬(recordGapCenter + 585012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585012]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09738_not_prime : ¬(recordGapCenter + 585062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585062]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09739_not_prime : ¬(recordGapCenter + 585098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585098]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09740_not_prime : ¬(recordGapCenter + 585138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585138]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09741_not_prime : ¬(recordGapCenter + 585146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585146]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09742_not_prime : ¬(recordGapCenter + 585188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585188]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09743_not_prime : ¬(recordGapCenter + 585348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585348]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09744_not_prime : ¬(recordGapCenter + 585426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585426]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09745_not_prime : ¬(recordGapCenter + 585498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585498]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09746_not_prime : ¬(recordGapCenter + 585506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585506]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09747_not_prime : ¬(recordGapCenter + 585512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585512]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09748_not_prime : ¬(recordGapCenter + 585588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585588]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09749_not_prime : ¬(recordGapCenter + 585642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585642]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09750_not_prime : ¬(recordGapCenter + 585692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585692]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09751_not_prime : ¬(recordGapCenter + 585758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585758]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09752_not_prime : ¬(recordGapCenter + 585818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585818]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09753_not_prime : ¬(recordGapCenter + 585866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585866]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09754_not_prime : ¬(recordGapCenter + 585876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585876]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09755_not_prime : ¬(recordGapCenter + 585896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585896]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09756_not_prime : ¬(recordGapCenter + 585938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585938]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09757_not_prime : ¬(recordGapCenter + 585986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 585986]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09758_not_prime : ¬(recordGapCenter + 586052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586052]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09759_not_prime : ¬(recordGapCenter + 586122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586122]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09760_not_prime : ¬(recordGapCenter + 586266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586266]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09761_not_prime : ¬(recordGapCenter + 586310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586310]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09762_not_prime : ¬(recordGapCenter + 586328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586328]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09763_not_prime : ¬(recordGapCenter + 586412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586412]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09764_not_prime : ¬(recordGapCenter + 586436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586436]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09765_not_prime : ¬(recordGapCenter + 586442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586442]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09766_not_prime : ¬(recordGapCenter + 586526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586526]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09767_not_prime : ¬(recordGapCenter + 586596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586596]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09768_not_prime : ¬(recordGapCenter + 586616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586616]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09769_not_prime : ¬(recordGapCenter + 586622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586622]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09770_not_prime : ¬(recordGapCenter + 586668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586668]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09771_not_prime : ¬(recordGapCenter + 586722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586722]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09772_not_prime : ¬(recordGapCenter + 586826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586826]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09773_not_prime : ¬(recordGapCenter + 586862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 586862]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09774_not_prime : ¬(recordGapCenter + 587058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 587058]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09775_not_prime : ¬(recordGapCenter + 587228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 587228]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09776_not_prime : ¬(recordGapCenter + 587402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 587402]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09777_not_prime : ¬(recordGapCenter + 587436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 587436]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09778_not_prime : ¬(recordGapCenter + 587546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 587546]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09779_not_prime : ¬(recordGapCenter + 587658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 587658]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09780_not_prime : ¬(recordGapCenter + 587816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 587816]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09781_not_prime : ¬(recordGapCenter + 587966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 587966]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09782_not_prime : ¬(recordGapCenter + 588000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588000]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09783_not_prime : ¬(recordGapCenter + 588036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588036]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09784_not_prime : ¬(recordGapCenter + 588066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588066]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09785_not_prime : ¬(recordGapCenter + 588108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588108]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09786_not_prime : ¬(recordGapCenter + 588206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588206]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09787_not_prime : ¬(recordGapCenter + 588282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588282]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09788_not_prime : ¬(recordGapCenter + 588332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588332]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09789_not_prime : ¬(recordGapCenter + 588362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588362]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09790_not_prime : ¬(recordGapCenter + 588396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588396]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09791_not_prime : ¬(recordGapCenter + 588422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588422]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

theorem fullRecordGapTerm09792_not_prime : ¬(recordGapCenter + 588446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588446]
  · apply fullRecordGapRow00153_fermat
    simp [fullRecordGapRow00153_values]

end PrimeFactorUnimodality
