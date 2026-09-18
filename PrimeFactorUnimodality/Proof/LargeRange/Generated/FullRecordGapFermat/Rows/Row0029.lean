import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00029_values : List Nat :=
  [fullRecordGapCenterValue - 310782,
    fullRecordGapCenterValue - 310762,
    fullRecordGapCenterValue - 310438,
    fullRecordGapCenterValue - 310348,
    fullRecordGapCenterValue - 310342,
    fullRecordGapCenterValue - 310228,
    fullRecordGapCenterValue - 310162,
    fullRecordGapCenterValue - 310098,
    fullRecordGapCenterValue - 310084,
    fullRecordGapCenterValue - 310074,
    fullRecordGapCenterValue - 310018,
    fullRecordGapCenterValue - 309882,
    fullRecordGapCenterValue - 309822,
    fullRecordGapCenterValue - 309760,
    fullRecordGapCenterValue - 309682,
    fullRecordGapCenterValue - 309678,
    fullRecordGapCenterValue - 309598,
    fullRecordGapCenterValue - 309574,
    fullRecordGapCenterValue - 309538,
    fullRecordGapCenterValue - 309382,
    fullRecordGapCenterValue - 309378,
    fullRecordGapCenterValue - 309292,
    fullRecordGapCenterValue - 308878,
    fullRecordGapCenterValue - 308874,
    fullRecordGapCenterValue - 308838,
    fullRecordGapCenterValue - 308700,
    fullRecordGapCenterValue - 308668,
    fullRecordGapCenterValue - 308622,
    fullRecordGapCenterValue - 308478,
    fullRecordGapCenterValue - 308314,
    fullRecordGapCenterValue - 308188,
    fullRecordGapCenterValue - 308164,
    fullRecordGapCenterValue - 308122,
    fullRecordGapCenterValue - 308094,
    fullRecordGapCenterValue - 308082,
    fullRecordGapCenterValue - 308068,
    fullRecordGapCenterValue - 308058,
    fullRecordGapCenterValue - 308002,
    fullRecordGapCenterValue - 307852,
    fullRecordGapCenterValue - 307774,
    fullRecordGapCenterValue - 307698,
    fullRecordGapCenterValue - 307578,
    fullRecordGapCenterValue - 307402,
    fullRecordGapCenterValue - 307348,
    fullRecordGapCenterValue - 307282,
    fullRecordGapCenterValue - 307158,
    fullRecordGapCenterValue - 307114,
    fullRecordGapCenterValue - 307018,
    fullRecordGapCenterValue - 306942,
    fullRecordGapCenterValue - 306814,
    fullRecordGapCenterValue - 306798,
    fullRecordGapCenterValue - 306742,
    fullRecordGapCenterValue - 306654,
    fullRecordGapCenterValue - 306604,
    fullRecordGapCenterValue - 306562,
    fullRecordGapCenterValue - 306388,
    fullRecordGapCenterValue - 306274,
    fullRecordGapCenterValue - 306214,
    fullRecordGapCenterValue - 306154,
    fullRecordGapCenterValue - 306142,
    fullRecordGapCenterValue - 306028,
    fullRecordGapCenterValue - 305962,
    fullRecordGapCenterValue - 305934,
    fullRecordGapCenterValue - 305884]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00029_fermat : ∀ n ∈ fullRecordGapRow00029_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01793_not_prime : ¬(recordGapCenter - 310782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310782]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01794_not_prime : ¬(recordGapCenter - 310762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310762]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01795_not_prime : ¬(recordGapCenter - 310438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310438]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01796_not_prime : ¬(recordGapCenter - 310348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310348]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01797_not_prime : ¬(recordGapCenter - 310342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310342]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01798_not_prime : ¬(recordGapCenter - 310228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310228]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01799_not_prime : ¬(recordGapCenter - 310162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310162]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01800_not_prime : ¬(recordGapCenter - 310098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310098]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01801_not_prime : ¬(recordGapCenter - 310084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310084]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01802_not_prime : ¬(recordGapCenter - 310074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310074]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01803_not_prime : ¬(recordGapCenter - 310018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310018]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01804_not_prime : ¬(recordGapCenter - 309882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309882]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01805_not_prime : ¬(recordGapCenter - 309822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309822]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01806_not_prime : ¬(recordGapCenter - 309760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309760]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01807_not_prime : ¬(recordGapCenter - 309682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309682]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01808_not_prime : ¬(recordGapCenter - 309678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309678]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01809_not_prime : ¬(recordGapCenter - 309598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309598]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01810_not_prime : ¬(recordGapCenter - 309574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309574]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01811_not_prime : ¬(recordGapCenter - 309538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309538]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01812_not_prime : ¬(recordGapCenter - 309382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309382]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01813_not_prime : ¬(recordGapCenter - 309378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309378]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01814_not_prime : ¬(recordGapCenter - 309292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309292]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01815_not_prime : ¬(recordGapCenter - 308878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308878]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01816_not_prime : ¬(recordGapCenter - 308874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308874]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01817_not_prime : ¬(recordGapCenter - 308838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308838]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01818_not_prime : ¬(recordGapCenter - 308700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308700]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01819_not_prime : ¬(recordGapCenter - 308668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308668]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01820_not_prime : ¬(recordGapCenter - 308622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308622]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01821_not_prime : ¬(recordGapCenter - 308478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308478]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01822_not_prime : ¬(recordGapCenter - 308314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308314]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01823_not_prime : ¬(recordGapCenter - 308188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308188]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01824_not_prime : ¬(recordGapCenter - 308164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308164]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01825_not_prime : ¬(recordGapCenter - 308122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308122]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01826_not_prime : ¬(recordGapCenter - 308094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308094]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01827_not_prime : ¬(recordGapCenter - 308082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308082]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01828_not_prime : ¬(recordGapCenter - 308068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308068]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01829_not_prime : ¬(recordGapCenter - 308058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308058]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01830_not_prime : ¬(recordGapCenter - 308002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308002]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01831_not_prime : ¬(recordGapCenter - 307852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307852]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01832_not_prime : ¬(recordGapCenter - 307774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307774]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01833_not_prime : ¬(recordGapCenter - 307698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307698]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01834_not_prime : ¬(recordGapCenter - 307578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307578]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01835_not_prime : ¬(recordGapCenter - 307402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307402]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01836_not_prime : ¬(recordGapCenter - 307348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307348]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01837_not_prime : ¬(recordGapCenter - 307282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307282]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01838_not_prime : ¬(recordGapCenter - 307158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307158]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01839_not_prime : ¬(recordGapCenter - 307114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307114]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01840_not_prime : ¬(recordGapCenter - 307018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307018]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01841_not_prime : ¬(recordGapCenter - 306942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306942]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01842_not_prime : ¬(recordGapCenter - 306814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306814]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01843_not_prime : ¬(recordGapCenter - 306798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306798]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01844_not_prime : ¬(recordGapCenter - 306742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306742]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01845_not_prime : ¬(recordGapCenter - 306654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306654]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01846_not_prime : ¬(recordGapCenter - 306604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306604]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01847_not_prime : ¬(recordGapCenter - 306562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306562]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01848_not_prime : ¬(recordGapCenter - 306388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306388]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01849_not_prime : ¬(recordGapCenter - 306274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306274]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01850_not_prime : ¬(recordGapCenter - 306214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306214]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01851_not_prime : ¬(recordGapCenter - 306154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306154]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01852_not_prime : ¬(recordGapCenter - 306142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306142]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01853_not_prime : ¬(recordGapCenter - 306028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306028]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01854_not_prime : ¬(recordGapCenter - 305962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305962]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01855_not_prime : ¬(recordGapCenter - 305934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305934]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

theorem fullRecordGapTerm01856_not_prime : ¬(recordGapCenter - 305884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305884]
  · apply fullRecordGapRow00029_fermat
    simp [fullRecordGapRow00029_values]

end PrimeFactorUnimodality
