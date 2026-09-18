import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00154_values : List Nat :=
  [fullRecordGapCenterValue + 588486,
    fullRecordGapCenterValue + 588488,
    fullRecordGapCenterValue + 588788,
    fullRecordGapCenterValue + 588806,
    fullRecordGapCenterValue + 588872,
    fullRecordGapCenterValue + 588908,
    fullRecordGapCenterValue + 588998,
    fullRecordGapCenterValue + 589010,
    fullRecordGapCenterValue + 589052,
    fullRecordGapCenterValue + 589172,
    fullRecordGapCenterValue + 589208,
    fullRecordGapCenterValue + 589298,
    fullRecordGapCenterValue + 589326,
    fullRecordGapCenterValue + 589346,
    fullRecordGapCenterValue + 589370,
    fullRecordGapCenterValue + 589388,
    fullRecordGapCenterValue + 589412,
    fullRecordGapCenterValue + 589430,
    fullRecordGapCenterValue + 589502,
    fullRecordGapCenterValue + 589542,
    fullRecordGapCenterValue + 589562,
    fullRecordGapCenterValue + 589592,
    fullRecordGapCenterValue + 589718,
    fullRecordGapCenterValue + 589782,
    fullRecordGapCenterValue + 589790,
    fullRecordGapCenterValue + 589796,
    fullRecordGapCenterValue + 589962,
    fullRecordGapCenterValue + 589982,
    fullRecordGapCenterValue + 590012,
    fullRecordGapCenterValue + 590028,
    fullRecordGapCenterValue + 590052,
    fullRecordGapCenterValue + 590066,
    fullRecordGapCenterValue + 590082,
    fullRecordGapCenterValue + 590222,
    fullRecordGapCenterValue + 590228,
    fullRecordGapCenterValue + 590258,
    fullRecordGapCenterValue + 590412,
    fullRecordGapCenterValue + 590438,
    fullRecordGapCenterValue + 590552,
    fullRecordGapCenterValue + 590658,
    fullRecordGapCenterValue + 590822,
    fullRecordGapCenterValue + 590838,
    fullRecordGapCenterValue + 590858,
    fullRecordGapCenterValue + 590936,
    fullRecordGapCenterValue + 590972,
    fullRecordGapCenterValue + 591036,
    fullRecordGapCenterValue + 591116,
    fullRecordGapCenterValue + 591176,
    fullRecordGapCenterValue + 591230,
    fullRecordGapCenterValue + 591258,
    fullRecordGapCenterValue + 591348,
    fullRecordGapCenterValue + 591360,
    fullRecordGapCenterValue + 591410,
    fullRecordGapCenterValue + 591512,
    fullRecordGapCenterValue + 591518,
    fullRecordGapCenterValue + 591608,
    fullRecordGapCenterValue + 591830,
    fullRecordGapCenterValue + 591986,
    fullRecordGapCenterValue + 592068,
    fullRecordGapCenterValue + 592070,
    fullRecordGapCenterValue + 592142,
    fullRecordGapCenterValue + 592166,
    fullRecordGapCenterValue + 592292,
    fullRecordGapCenterValue + 592316]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00154_fermat : ∀ n ∈ fullRecordGapRow00154_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09793_not_prime : ¬(recordGapCenter + 588486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588486]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09794_not_prime : ¬(recordGapCenter + 588488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588488]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09795_not_prime : ¬(recordGapCenter + 588788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588788]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09796_not_prime : ¬(recordGapCenter + 588806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588806]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09797_not_prime : ¬(recordGapCenter + 588872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588872]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09798_not_prime : ¬(recordGapCenter + 588908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588908]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09799_not_prime : ¬(recordGapCenter + 588998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588998]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09800_not_prime : ¬(recordGapCenter + 589010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589010]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09801_not_prime : ¬(recordGapCenter + 589052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589052]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09802_not_prime : ¬(recordGapCenter + 589172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589172]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09803_not_prime : ¬(recordGapCenter + 589208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589208]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09804_not_prime : ¬(recordGapCenter + 589298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589298]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09805_not_prime : ¬(recordGapCenter + 589326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589326]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09806_not_prime : ¬(recordGapCenter + 589346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589346]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09807_not_prime : ¬(recordGapCenter + 589370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589370]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09808_not_prime : ¬(recordGapCenter + 589388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589388]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09809_not_prime : ¬(recordGapCenter + 589412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589412]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09810_not_prime : ¬(recordGapCenter + 589430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589430]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09811_not_prime : ¬(recordGapCenter + 589502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589502]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09812_not_prime : ¬(recordGapCenter + 589542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589542]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09813_not_prime : ¬(recordGapCenter + 589562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589562]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09814_not_prime : ¬(recordGapCenter + 589592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589592]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09815_not_prime : ¬(recordGapCenter + 589718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589718]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09816_not_prime : ¬(recordGapCenter + 589782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589782]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09817_not_prime : ¬(recordGapCenter + 589790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589790]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09818_not_prime : ¬(recordGapCenter + 589796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589796]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09819_not_prime : ¬(recordGapCenter + 589962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589962]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09820_not_prime : ¬(recordGapCenter + 589982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 589982]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09821_not_prime : ¬(recordGapCenter + 590012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590012]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09822_not_prime : ¬(recordGapCenter + 590028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590028]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09823_not_prime : ¬(recordGapCenter + 590052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590052]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09824_not_prime : ¬(recordGapCenter + 590066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590066]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09825_not_prime : ¬(recordGapCenter + 590082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590082]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09826_not_prime : ¬(recordGapCenter + 590222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590222]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09827_not_prime : ¬(recordGapCenter + 590228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590228]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09828_not_prime : ¬(recordGapCenter + 590258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590258]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09829_not_prime : ¬(recordGapCenter + 590412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590412]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09830_not_prime : ¬(recordGapCenter + 590438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590438]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09831_not_prime : ¬(recordGapCenter + 590552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590552]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09832_not_prime : ¬(recordGapCenter + 590658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590658]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09833_not_prime : ¬(recordGapCenter + 590822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590822]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09834_not_prime : ¬(recordGapCenter + 590838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590838]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09835_not_prime : ¬(recordGapCenter + 590858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590858]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09836_not_prime : ¬(recordGapCenter + 590936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590936]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09837_not_prime : ¬(recordGapCenter + 590972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 590972]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09838_not_prime : ¬(recordGapCenter + 591036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591036]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09839_not_prime : ¬(recordGapCenter + 591116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591116]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09840_not_prime : ¬(recordGapCenter + 591176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591176]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09841_not_prime : ¬(recordGapCenter + 591230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591230]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09842_not_prime : ¬(recordGapCenter + 591258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591258]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09843_not_prime : ¬(recordGapCenter + 591348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591348]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09844_not_prime : ¬(recordGapCenter + 591360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591360]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09845_not_prime : ¬(recordGapCenter + 591410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591410]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09846_not_prime : ¬(recordGapCenter + 591512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591512]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09847_not_prime : ¬(recordGapCenter + 591518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591518]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09848_not_prime : ¬(recordGapCenter + 591608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591608]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09849_not_prime : ¬(recordGapCenter + 591830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591830]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09850_not_prime : ¬(recordGapCenter + 591986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 591986]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09851_not_prime : ¬(recordGapCenter + 592068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592068]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09852_not_prime : ¬(recordGapCenter + 592070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592070]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09853_not_prime : ¬(recordGapCenter + 592142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592142]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09854_not_prime : ¬(recordGapCenter + 592166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592166]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09855_not_prime : ¬(recordGapCenter + 592292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592292]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

theorem fullRecordGapTerm09856_not_prime : ¬(recordGapCenter + 592316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592316]
  · apply fullRecordGapRow00154_fermat
    simp [fullRecordGapRow00154_values]

end PrimeFactorUnimodality
