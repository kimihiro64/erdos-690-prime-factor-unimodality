import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00014_values : List Nat :=
  [fullRecordGapCenterValue - 389014,
    fullRecordGapCenterValue - 388924,
    fullRecordGapCenterValue - 388902,
    fullRecordGapCenterValue - 388758,
    fullRecordGapCenterValue - 388684,
    fullRecordGapCenterValue - 388618,
    fullRecordGapCenterValue - 388468,
    fullRecordGapCenterValue - 388302,
    fullRecordGapCenterValue - 388080,
    fullRecordGapCenterValue - 388012,
    fullRecordGapCenterValue - 388002,
    fullRecordGapCenterValue - 387988,
    fullRecordGapCenterValue - 387978,
    fullRecordGapCenterValue - 387874,
    fullRecordGapCenterValue - 387832,
    fullRecordGapCenterValue - 387784,
    fullRecordGapCenterValue - 387762,
    fullRecordGapCenterValue - 387742,
    fullRecordGapCenterValue - 387694,
    fullRecordGapCenterValue - 387592,
    fullRecordGapCenterValue - 387298,
    fullRecordGapCenterValue - 387238,
    fullRecordGapCenterValue - 387154,
    fullRecordGapCenterValue - 387118,
    fullRecordGapCenterValue - 387082,
    fullRecordGapCenterValue - 386994,
    fullRecordGapCenterValue - 386938,
    fullRecordGapCenterValue - 386934,
    fullRecordGapCenterValue - 386788,
    fullRecordGapCenterValue - 386734,
    fullRecordGapCenterValue - 386728,
    fullRecordGapCenterValue - 386668,
    fullRecordGapCenterValue - 386572,
    fullRecordGapCenterValue - 386494,
    fullRecordGapCenterValue - 386488,
    fullRecordGapCenterValue - 386418,
    fullRecordGapCenterValue - 386392,
    fullRecordGapCenterValue - 386362,
    fullRecordGapCenterValue - 386278,
    fullRecordGapCenterValue - 386248,
    fullRecordGapCenterValue - 386238,
    fullRecordGapCenterValue - 386068,
    fullRecordGapCenterValue - 385998,
    fullRecordGapCenterValue - 385948,
    fullRecordGapCenterValue - 385942,
    fullRecordGapCenterValue - 385912,
    fullRecordGapCenterValue - 385698,
    fullRecordGapCenterValue - 385674,
    fullRecordGapCenterValue - 385432,
    fullRecordGapCenterValue - 385348,
    fullRecordGapCenterValue - 385338,
    fullRecordGapCenterValue - 385324,
    fullRecordGapCenterValue - 385222,
    fullRecordGapCenterValue - 384918,
    fullRecordGapCenterValue - 384912,
    fullRecordGapCenterValue - 384862,
    fullRecordGapCenterValue - 384814,
    fullRecordGapCenterValue - 384694,
    fullRecordGapCenterValue - 384634,
    fullRecordGapCenterValue - 384628,
    fullRecordGapCenterValue - 384502,
    fullRecordGapCenterValue - 384478,
    fullRecordGapCenterValue - 384382,
    fullRecordGapCenterValue - 384232]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00014_fermat : ∀ n ∈ fullRecordGapRow00014_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00833_not_prime : ¬(recordGapCenter - 389014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389014]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00834_not_prime : ¬(recordGapCenter - 388924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388924]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00835_not_prime : ¬(recordGapCenter - 388902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388902]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00836_not_prime : ¬(recordGapCenter - 388758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388758]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00837_not_prime : ¬(recordGapCenter - 388684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388684]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00838_not_prime : ¬(recordGapCenter - 388618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388618]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00839_not_prime : ¬(recordGapCenter - 388468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388468]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00840_not_prime : ¬(recordGapCenter - 388302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388302]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00841_not_prime : ¬(recordGapCenter - 388080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388080]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00842_not_prime : ¬(recordGapCenter - 388012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388012]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00843_not_prime : ¬(recordGapCenter - 388002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388002]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00844_not_prime : ¬(recordGapCenter - 387988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387988]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00845_not_prime : ¬(recordGapCenter - 387978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387978]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00846_not_prime : ¬(recordGapCenter - 387874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387874]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00847_not_prime : ¬(recordGapCenter - 387832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387832]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00848_not_prime : ¬(recordGapCenter - 387784).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387784]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00849_not_prime : ¬(recordGapCenter - 387762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387762]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00850_not_prime : ¬(recordGapCenter - 387742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387742]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00851_not_prime : ¬(recordGapCenter - 387694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387694]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00852_not_prime : ¬(recordGapCenter - 387592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387592]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00853_not_prime : ¬(recordGapCenter - 387298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387298]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00854_not_prime : ¬(recordGapCenter - 387238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387238]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00855_not_prime : ¬(recordGapCenter - 387154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387154]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00856_not_prime : ¬(recordGapCenter - 387118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387118]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00857_not_prime : ¬(recordGapCenter - 387082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387082]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00858_not_prime : ¬(recordGapCenter - 386994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386994]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00859_not_prime : ¬(recordGapCenter - 386938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386938]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00860_not_prime : ¬(recordGapCenter - 386934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386934]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00861_not_prime : ¬(recordGapCenter - 386788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386788]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00862_not_prime : ¬(recordGapCenter - 386734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386734]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00863_not_prime : ¬(recordGapCenter - 386728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386728]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00864_not_prime : ¬(recordGapCenter - 386668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386668]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00865_not_prime : ¬(recordGapCenter - 386572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386572]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00866_not_prime : ¬(recordGapCenter - 386494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386494]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00867_not_prime : ¬(recordGapCenter - 386488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386488]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00868_not_prime : ¬(recordGapCenter - 386418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386418]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00869_not_prime : ¬(recordGapCenter - 386392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386392]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00870_not_prime : ¬(recordGapCenter - 386362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386362]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00871_not_prime : ¬(recordGapCenter - 386278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386278]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00872_not_prime : ¬(recordGapCenter - 386248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386248]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00873_not_prime : ¬(recordGapCenter - 386238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386238]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00874_not_prime : ¬(recordGapCenter - 386068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386068]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00875_not_prime : ¬(recordGapCenter - 385998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385998]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00876_not_prime : ¬(recordGapCenter - 385948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385948]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00877_not_prime : ¬(recordGapCenter - 385942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385942]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00878_not_prime : ¬(recordGapCenter - 385912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385912]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00879_not_prime : ¬(recordGapCenter - 385698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385698]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00880_not_prime : ¬(recordGapCenter - 385674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385674]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00881_not_prime : ¬(recordGapCenter - 385432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385432]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00882_not_prime : ¬(recordGapCenter - 385348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385348]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00883_not_prime : ¬(recordGapCenter - 385338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385338]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00884_not_prime : ¬(recordGapCenter - 385324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385324]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00885_not_prime : ¬(recordGapCenter - 385222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385222]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00886_not_prime : ¬(recordGapCenter - 384918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384918]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00887_not_prime : ¬(recordGapCenter - 384912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384912]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00888_not_prime : ¬(recordGapCenter - 384862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384862]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00889_not_prime : ¬(recordGapCenter - 384814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384814]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00890_not_prime : ¬(recordGapCenter - 384694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384694]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00891_not_prime : ¬(recordGapCenter - 384634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384634]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00892_not_prime : ¬(recordGapCenter - 384628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384628]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00893_not_prime : ¬(recordGapCenter - 384502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384502]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00894_not_prime : ¬(recordGapCenter - 384478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384478]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00895_not_prime : ¬(recordGapCenter - 384382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384382]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm00896_not_prime : ¬(recordGapCenter - 384232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384232]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

end PrimeFactorUnimodality
