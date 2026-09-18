import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00107_values : List Nat :=
  [fullRecordGapCenterValue + 377906,
    fullRecordGapCenterValue + 377966,
    fullRecordGapCenterValue + 378008,
    fullRecordGapCenterValue + 378038,
    fullRecordGapCenterValue + 378086,
    fullRecordGapCenterValue + 378278,
    fullRecordGapCenterValue + 378296,
    fullRecordGapCenterValue + 378402,
    fullRecordGapCenterValue + 378438,
    fullRecordGapCenterValue + 378458,
    fullRecordGapCenterValue + 378536,
    fullRecordGapCenterValue + 378542,
    fullRecordGapCenterValue + 378582,
    fullRecordGapCenterValue + 378722,
    fullRecordGapCenterValue + 378786,
    fullRecordGapCenterValue + 378866,
    fullRecordGapCenterValue + 378878,
    fullRecordGapCenterValue + 378908,
    fullRecordGapCenterValue + 378926,
    fullRecordGapCenterValue + 379058,
    fullRecordGapCenterValue + 379172,
    fullRecordGapCenterValue + 379292,
    fullRecordGapCenterValue + 379352,
    fullRecordGapCenterValue + 379388,
    fullRecordGapCenterValue + 379446,
    fullRecordGapCenterValue + 379466,
    fullRecordGapCenterValue + 379598,
    fullRecordGapCenterValue + 379646,
    fullRecordGapCenterValue + 379718,
    fullRecordGapCenterValue + 379878,
    fullRecordGapCenterValue + 379902,
    fullRecordGapCenterValue + 379928,
    fullRecordGapCenterValue + 380012,
    fullRecordGapCenterValue + 380126,
    fullRecordGapCenterValue + 380168,
    fullRecordGapCenterValue + 380186,
    fullRecordGapCenterValue + 380252,
    fullRecordGapCenterValue + 380258,
    fullRecordGapCenterValue + 380348,
    fullRecordGapCenterValue + 380642,
    fullRecordGapCenterValue + 380648,
    fullRecordGapCenterValue + 380852,
    fullRecordGapCenterValue + 380958,
    fullRecordGapCenterValue + 381032,
    fullRecordGapCenterValue + 381068,
    fullRecordGapCenterValue + 381126,
    fullRecordGapCenterValue + 381246,
    fullRecordGapCenterValue + 381272,
    fullRecordGapCenterValue + 381308,
    fullRecordGapCenterValue + 381356,
    fullRecordGapCenterValue + 381522,
    fullRecordGapCenterValue + 381566,
    fullRecordGapCenterValue + 381572,
    fullRecordGapCenterValue + 381606,
    fullRecordGapCenterValue + 381782,
    fullRecordGapCenterValue + 381882,
    fullRecordGapCenterValue + 381896,
    fullRecordGapCenterValue + 382002,
    fullRecordGapCenterValue + 382142,
    fullRecordGapCenterValue + 382218,
    fullRecordGapCenterValue + 382232,
    fullRecordGapCenterValue + 382238,
    fullRecordGapCenterValue + 382286,
    fullRecordGapCenterValue + 382362]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00107_fermat : ∀ n ∈ fullRecordGapRow00107_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06785_not_prime : ¬(recordGapCenter + 377906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377906]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06786_not_prime : ¬(recordGapCenter + 377966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377966]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06787_not_prime : ¬(recordGapCenter + 378008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378008]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06788_not_prime : ¬(recordGapCenter + 378038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378038]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06789_not_prime : ¬(recordGapCenter + 378086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378086]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06790_not_prime : ¬(recordGapCenter + 378278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378278]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06791_not_prime : ¬(recordGapCenter + 378296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378296]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06792_not_prime : ¬(recordGapCenter + 378402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378402]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06793_not_prime : ¬(recordGapCenter + 378438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378438]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06794_not_prime : ¬(recordGapCenter + 378458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378458]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06795_not_prime : ¬(recordGapCenter + 378536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378536]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06796_not_prime : ¬(recordGapCenter + 378542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378542]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06797_not_prime : ¬(recordGapCenter + 378582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378582]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06798_not_prime : ¬(recordGapCenter + 378722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378722]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06799_not_prime : ¬(recordGapCenter + 378786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378786]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06800_not_prime : ¬(recordGapCenter + 378866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378866]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06801_not_prime : ¬(recordGapCenter + 378878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378878]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06802_not_prime : ¬(recordGapCenter + 378908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378908]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06803_not_prime : ¬(recordGapCenter + 378926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378926]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06804_not_prime : ¬(recordGapCenter + 379058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379058]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06805_not_prime : ¬(recordGapCenter + 379172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379172]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06806_not_prime : ¬(recordGapCenter + 379292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379292]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06807_not_prime : ¬(recordGapCenter + 379352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379352]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06808_not_prime : ¬(recordGapCenter + 379388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379388]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06809_not_prime : ¬(recordGapCenter + 379446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379446]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06810_not_prime : ¬(recordGapCenter + 379466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379466]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06811_not_prime : ¬(recordGapCenter + 379598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379598]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06812_not_prime : ¬(recordGapCenter + 379646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379646]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06813_not_prime : ¬(recordGapCenter + 379718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379718]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06814_not_prime : ¬(recordGapCenter + 379878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379878]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06815_not_prime : ¬(recordGapCenter + 379902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379902]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06816_not_prime : ¬(recordGapCenter + 379928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379928]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06817_not_prime : ¬(recordGapCenter + 380012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380012]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06818_not_prime : ¬(recordGapCenter + 380126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380126]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06819_not_prime : ¬(recordGapCenter + 380168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380168]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06820_not_prime : ¬(recordGapCenter + 380186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380186]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06821_not_prime : ¬(recordGapCenter + 380252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380252]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06822_not_prime : ¬(recordGapCenter + 380258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380258]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06823_not_prime : ¬(recordGapCenter + 380348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380348]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06824_not_prime : ¬(recordGapCenter + 380642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380642]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06825_not_prime : ¬(recordGapCenter + 380648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380648]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06826_not_prime : ¬(recordGapCenter + 380852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380852]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06827_not_prime : ¬(recordGapCenter + 380958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380958]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06828_not_prime : ¬(recordGapCenter + 381032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381032]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06829_not_prime : ¬(recordGapCenter + 381068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381068]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06830_not_prime : ¬(recordGapCenter + 381126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381126]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06831_not_prime : ¬(recordGapCenter + 381246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381246]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06832_not_prime : ¬(recordGapCenter + 381272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381272]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06833_not_prime : ¬(recordGapCenter + 381308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381308]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06834_not_prime : ¬(recordGapCenter + 381356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381356]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06835_not_prime : ¬(recordGapCenter + 381522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381522]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06836_not_prime : ¬(recordGapCenter + 381566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381566]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06837_not_prime : ¬(recordGapCenter + 381572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381572]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06838_not_prime : ¬(recordGapCenter + 381606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381606]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06839_not_prime : ¬(recordGapCenter + 381782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381782]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06840_not_prime : ¬(recordGapCenter + 381882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381882]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06841_not_prime : ¬(recordGapCenter + 381896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381896]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06842_not_prime : ¬(recordGapCenter + 382002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382002]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06843_not_prime : ¬(recordGapCenter + 382142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382142]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06844_not_prime : ¬(recordGapCenter + 382218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382218]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06845_not_prime : ¬(recordGapCenter + 382232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382232]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06846_not_prime : ¬(recordGapCenter + 382238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382238]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06847_not_prime : ¬(recordGapCenter + 382286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382286]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

theorem fullRecordGapTerm06848_not_prime : ¬(recordGapCenter + 382362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382362]
  · apply fullRecordGapRow00107_fermat
    simp [fullRecordGapRow00107_values]

end PrimeFactorUnimodality
