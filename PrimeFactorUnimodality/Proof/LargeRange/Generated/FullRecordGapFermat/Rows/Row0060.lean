import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00060_values : List Nat :=
  [fullRecordGapCenterValue - 1728,
    fullRecordGapCenterValue - 1620,
    fullRecordGapCenterValue - 1600,
    fullRecordGapCenterValue - 1584,
    fullRecordGapCenterValue - 1540,
    fullRecordGapCenterValue - 1470,
    fullRecordGapCenterValue - 1458,
    fullRecordGapCenterValue - 1372,
    fullRecordGapCenterValue - 1188,
    fullRecordGapCenterValue - 1152,
    fullRecordGapCenterValue - 1078,
    fullRecordGapCenterValue - 1000,
    fullRecordGapCenterValue - 880,
    fullRecordGapCenterValue - 810,
    fullRecordGapCenterValue - 768,
    fullRecordGapCenterValue - 648,
    fullRecordGapCenterValue - 600,
    fullRecordGapCenterValue - 594,
    fullRecordGapCenterValue - 588,
    fullRecordGapCenterValue - 462,
    fullRecordGapCenterValue - 448,
    fullRecordGapCenterValue - 420,
    fullRecordGapCenterValue - 384,
    fullRecordGapCenterValue - 352,
    fullRecordGapCenterValue - 270,
    fullRecordGapCenterValue - 252,
    fullRecordGapCenterValue - 250,
    fullRecordGapCenterValue - 240,
    fullRecordGapCenterValue - 198,
    fullRecordGapCenterValue - 192,
    fullRecordGapCenterValue - 108,
    fullRecordGapCenterValue - 100,
    fullRecordGapCenterValue - 90,
    fullRecordGapCenterValue - 88,
    fullRecordGapCenterValue - 84,
    fullRecordGapCenterValue - 60,
    fullRecordGapCenterValue - 54,
    fullRecordGapCenterValue - 24,
    fullRecordGapCenterValue - 12,
    fullRecordGapCenterValue + 66,
    fullRecordGapCenterValue + 72,
    fullRecordGapCenterValue + 96,
    fullRecordGapCenterValue + 110,
    fullRecordGapCenterValue + 126,
    fullRecordGapCenterValue + 140,
    fullRecordGapCenterValue + 162,
    fullRecordGapCenterValue + 176,
    fullRecordGapCenterValue + 192,
    fullRecordGapCenterValue + 240,
    fullRecordGapCenterValue + 252,
    fullRecordGapCenterValue + 336,
    fullRecordGapCenterValue + 350,
    fullRecordGapCenterValue + 360,
    fullRecordGapCenterValue + 420,
    fullRecordGapCenterValue + 486,
    fullRecordGapCenterValue + 512,
    fullRecordGapCenterValue + 528,
    fullRecordGapCenterValue + 560,
    fullRecordGapCenterValue + 576,
    fullRecordGapCenterValue + 588,
    fullRecordGapCenterValue + 600,
    fullRecordGapCenterValue + 660,
    fullRecordGapCenterValue + 726,
    fullRecordGapCenterValue + 882]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00060_fermat : ∀ n ∈ fullRecordGapRow00060_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03777_not_prime : ¬(recordGapCenter - 1728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1728]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03778_not_prime : ¬(recordGapCenter - 1620).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1620]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03779_not_prime : ¬(recordGapCenter - 1600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1600]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03780_not_prime : ¬(recordGapCenter - 1584).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1584]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03781_not_prime : ¬(recordGapCenter - 1540).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1540]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03782_not_prime : ¬(recordGapCenter - 1470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1470]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03783_not_prime : ¬(recordGapCenter - 1458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1458]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03784_not_prime : ¬(recordGapCenter - 1372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1372]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03785_not_prime : ¬(recordGapCenter - 1188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1188]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03786_not_prime : ¬(recordGapCenter - 1152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1152]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03787_not_prime : ¬(recordGapCenter - 1078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1078]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03788_not_prime : ¬(recordGapCenter - 1000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1000]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03789_not_prime : ¬(recordGapCenter - 880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 880]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03790_not_prime : ¬(recordGapCenter - 810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 810]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03791_not_prime : ¬(recordGapCenter - 768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 768]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03792_not_prime : ¬(recordGapCenter - 648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 648]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03793_not_prime : ¬(recordGapCenter - 600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 600]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03794_not_prime : ¬(recordGapCenter - 594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 594]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03795_not_prime : ¬(recordGapCenter - 588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 588]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03796_not_prime : ¬(recordGapCenter - 462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 462]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03797_not_prime : ¬(recordGapCenter - 448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03798_not_prime : ¬(recordGapCenter - 420).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03799_not_prime : ¬(recordGapCenter - 384).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03800_not_prime : ¬(recordGapCenter - 352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03801_not_prime : ¬(recordGapCenter - 270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03802_not_prime : ¬(recordGapCenter - 252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03803_not_prime : ¬(recordGapCenter - 250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03804_not_prime : ¬(recordGapCenter - 240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03805_not_prime : ¬(recordGapCenter - 198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03806_not_prime : ¬(recordGapCenter - 192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03807_not_prime : ¬(recordGapCenter - 108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03808_not_prime : ¬(recordGapCenter - 100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03809_not_prime : ¬(recordGapCenter - 90).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03810_not_prime : ¬(recordGapCenter - 88).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03811_not_prime : ¬(recordGapCenter - 84).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 84]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03812_not_prime : ¬(recordGapCenter - 60).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 60]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03813_not_prime : ¬(recordGapCenter - 54).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 54]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03814_not_prime : ¬(recordGapCenter - 24).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03815_not_prime : ¬(recordGapCenter - 12).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03816_not_prime : ¬(recordGapCenter + 66).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 66]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03817_not_prime : ¬(recordGapCenter + 72).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 72]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03818_not_prime : ¬(recordGapCenter + 96).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03819_not_prime : ¬(recordGapCenter + 110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03820_not_prime : ¬(recordGapCenter + 126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03821_not_prime : ¬(recordGapCenter + 140).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03822_not_prime : ¬(recordGapCenter + 162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03823_not_prime : ¬(recordGapCenter + 176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 176]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03824_not_prime : ¬(recordGapCenter + 192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03825_not_prime : ¬(recordGapCenter + 240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03826_not_prime : ¬(recordGapCenter + 252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03827_not_prime : ¬(recordGapCenter + 336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03828_not_prime : ¬(recordGapCenter + 350).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03829_not_prime : ¬(recordGapCenter + 360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03830_not_prime : ¬(recordGapCenter + 420).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03831_not_prime : ¬(recordGapCenter + 486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03832_not_prime : ¬(recordGapCenter + 512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03833_not_prime : ¬(recordGapCenter + 528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03834_not_prime : ¬(recordGapCenter + 560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03835_not_prime : ¬(recordGapCenter + 576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03836_not_prime : ¬(recordGapCenter + 588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03837_not_prime : ¬(recordGapCenter + 600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03838_not_prime : ¬(recordGapCenter + 660).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 660]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03839_not_prime : ¬(recordGapCenter + 726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 726]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

theorem fullRecordGapTerm03840_not_prime : ¬(recordGapCenter + 882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 882]
  · apply fullRecordGapRow00060_fermat
    simp [fullRecordGapRow00060_values]

end PrimeFactorUnimodality
