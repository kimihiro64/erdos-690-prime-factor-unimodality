import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00076_values : List Nat :=
  [fullRecordGapCenterValue + 200378,
    fullRecordGapCenterValue + 200426,
    fullRecordGapCenterValue + 200516,
    fullRecordGapCenterValue + 200666,
    fullRecordGapCenterValue + 200708,
    fullRecordGapCenterValue + 200726,
    fullRecordGapCenterValue + 200786,
    fullRecordGapCenterValue + 200828,
    fullRecordGapCenterValue + 200918,
    fullRecordGapCenterValue + 201218,
    fullRecordGapCenterValue + 201332,
    fullRecordGapCenterValue + 201338,
    fullRecordGapCenterValue + 201602,
    fullRecordGapCenterValue + 201668,
    fullRecordGapCenterValue + 201836,
    fullRecordGapCenterValue + 202298,
    fullRecordGapCenterValue + 202406,
    fullRecordGapCenterValue + 202500,
    fullRecordGapCenterValue + 202562,
    fullRecordGapCenterValue + 202718,
    fullRecordGapCenterValue + 202898,
    fullRecordGapCenterValue + 203066,
    fullRecordGapCenterValue + 203108,
    fullRecordGapCenterValue + 203280,
    fullRecordGapCenterValue + 203402,
    fullRecordGapCenterValue + 203438,
    fullRecordGapCenterValue + 203492,
    fullRecordGapCenterValue + 203726,
    fullRecordGapCenterValue + 203742,
    fullRecordGapCenterValue + 203828,
    fullRecordGapCenterValue + 203876,
    fullRecordGapCenterValue + 204026,
    fullRecordGapCenterValue + 204122,
    fullRecordGapCenterValue + 204158,
    fullRecordGapCenterValue + 204188,
    fullRecordGapCenterValue + 204362,
    fullRecordGapCenterValue + 204482,
    fullRecordGapCenterValue + 204506,
    fullRecordGapCenterValue + 204998,
    fullRecordGapCenterValue + 205028,
    fullRecordGapCenterValue + 205046,
    fullRecordGapCenterValue + 205118,
    fullRecordGapCenterValue + 205286,
    fullRecordGapCenterValue + 205346,
    fullRecordGapCenterValue + 205538,
    fullRecordGapCenterValue + 205622,
    fullRecordGapCenterValue + 205628,
    fullRecordGapCenterValue + 205658,
    fullRecordGapCenterValue + 205682,
    fullRecordGapCenterValue + 206252,
    fullRecordGapCenterValue + 206372,
    fullRecordGapCenterValue + 206582,
    fullRecordGapCenterValue + 206636,
    fullRecordGapCenterValue + 206666,
    fullRecordGapCenterValue + 206798,
    fullRecordGapCenterValue + 206846,
    fullRecordGapCenterValue + 206942,
    fullRecordGapCenterValue + 207068,
    fullRecordGapCenterValue + 207182,
    fullRecordGapCenterValue + 207212,
    fullRecordGapCenterValue + 207338,
    fullRecordGapCenterValue + 207362,
    fullRecordGapCenterValue + 207572,
    fullRecordGapCenterValue + 207926]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00076_fermat : ∀ n ∈ fullRecordGapRow00076_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04801_not_prime : ¬(recordGapCenter + 200378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200378]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04802_not_prime : ¬(recordGapCenter + 200426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200426]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04803_not_prime : ¬(recordGapCenter + 200516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200516]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04804_not_prime : ¬(recordGapCenter + 200666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200666]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04805_not_prime : ¬(recordGapCenter + 200708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200708]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04806_not_prime : ¬(recordGapCenter + 200726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200726]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04807_not_prime : ¬(recordGapCenter + 200786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200786]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04808_not_prime : ¬(recordGapCenter + 200828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200828]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04809_not_prime : ¬(recordGapCenter + 200918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200918]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04810_not_prime : ¬(recordGapCenter + 201218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 201218]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04811_not_prime : ¬(recordGapCenter + 201332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 201332]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04812_not_prime : ¬(recordGapCenter + 201338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 201338]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04813_not_prime : ¬(recordGapCenter + 201602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 201602]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04814_not_prime : ¬(recordGapCenter + 201668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 201668]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04815_not_prime : ¬(recordGapCenter + 201836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 201836]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04816_not_prime : ¬(recordGapCenter + 202298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 202298]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04817_not_prime : ¬(recordGapCenter + 202406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 202406]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04818_not_prime : ¬(recordGapCenter + 202500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 202500]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04819_not_prime : ¬(recordGapCenter + 202562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 202562]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04820_not_prime : ¬(recordGapCenter + 202718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 202718]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04821_not_prime : ¬(recordGapCenter + 202898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 202898]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04822_not_prime : ¬(recordGapCenter + 203066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203066]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04823_not_prime : ¬(recordGapCenter + 203108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203108]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04824_not_prime : ¬(recordGapCenter + 203280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203280]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04825_not_prime : ¬(recordGapCenter + 203402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203402]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04826_not_prime : ¬(recordGapCenter + 203438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203438]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04827_not_prime : ¬(recordGapCenter + 203492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203492]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04828_not_prime : ¬(recordGapCenter + 203726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203726]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04829_not_prime : ¬(recordGapCenter + 203742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203742]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04830_not_prime : ¬(recordGapCenter + 203828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203828]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04831_not_prime : ¬(recordGapCenter + 203876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 203876]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04832_not_prime : ¬(recordGapCenter + 204026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 204026]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04833_not_prime : ¬(recordGapCenter + 204122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 204122]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04834_not_prime : ¬(recordGapCenter + 204158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 204158]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04835_not_prime : ¬(recordGapCenter + 204188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 204188]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04836_not_prime : ¬(recordGapCenter + 204362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 204362]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04837_not_prime : ¬(recordGapCenter + 204482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 204482]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04838_not_prime : ¬(recordGapCenter + 204506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 204506]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04839_not_prime : ¬(recordGapCenter + 204998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 204998]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04840_not_prime : ¬(recordGapCenter + 205028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205028]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04841_not_prime : ¬(recordGapCenter + 205046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205046]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04842_not_prime : ¬(recordGapCenter + 205118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205118]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04843_not_prime : ¬(recordGapCenter + 205286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205286]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04844_not_prime : ¬(recordGapCenter + 205346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205346]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04845_not_prime : ¬(recordGapCenter + 205538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205538]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04846_not_prime : ¬(recordGapCenter + 205622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205622]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04847_not_prime : ¬(recordGapCenter + 205628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205628]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04848_not_prime : ¬(recordGapCenter + 205658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205658]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04849_not_prime : ¬(recordGapCenter + 205682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 205682]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04850_not_prime : ¬(recordGapCenter + 206252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 206252]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04851_not_prime : ¬(recordGapCenter + 206372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 206372]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04852_not_prime : ¬(recordGapCenter + 206582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 206582]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04853_not_prime : ¬(recordGapCenter + 206636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 206636]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04854_not_prime : ¬(recordGapCenter + 206666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 206666]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04855_not_prime : ¬(recordGapCenter + 206798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 206798]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04856_not_prime : ¬(recordGapCenter + 206846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 206846]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04857_not_prime : ¬(recordGapCenter + 206942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 206942]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04858_not_prime : ¬(recordGapCenter + 207068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207068]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04859_not_prime : ¬(recordGapCenter + 207182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207182]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04860_not_prime : ¬(recordGapCenter + 207212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207212]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04861_not_prime : ¬(recordGapCenter + 207338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207338]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04862_not_prime : ¬(recordGapCenter + 207362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207362]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04863_not_prime : ¬(recordGapCenter + 207572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207572]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

theorem fullRecordGapTerm04864_not_prime : ¬(recordGapCenter + 207926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207926]
  · apply fullRecordGapRow00076_fermat
    simp [fullRecordGapRow00076_values]

end PrimeFactorUnimodality
