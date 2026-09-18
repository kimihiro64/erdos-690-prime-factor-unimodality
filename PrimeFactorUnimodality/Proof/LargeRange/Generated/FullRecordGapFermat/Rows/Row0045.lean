import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00045_values : List Nat :=
  [fullRecordGapCenterValue - 205222,
    fullRecordGapCenterValue - 205174,
    fullRecordGapCenterValue - 204994,
    fullRecordGapCenterValue - 204658,
    fullRecordGapCenterValue - 204634,
    fullRecordGapCenterValue - 204298,
    fullRecordGapCenterValue - 204214,
    fullRecordGapCenterValue - 204154,
    fullRecordGapCenterValue - 203758,
    fullRecordGapCenterValue - 203742,
    fullRecordGapCenterValue - 203254,
    fullRecordGapCenterValue - 203074,
    fullRecordGapCenterValue - 203068,
    fullRecordGapCenterValue - 203062,
    fullRecordGapCenterValue - 202858,
    fullRecordGapCenterValue - 202828,
    fullRecordGapCenterValue - 202534,
    fullRecordGapCenterValue - 202348,
    fullRecordGapCenterValue - 202324,
    fullRecordGapCenterValue - 202222,
    fullRecordGapCenterValue - 202012,
    fullRecordGapCenterValue - 201988,
    fullRecordGapCenterValue - 201862,
    fullRecordGapCenterValue - 201814,
    fullRecordGapCenterValue - 201694,
    fullRecordGapCenterValue - 201532,
    fullRecordGapCenterValue - 201364,
    fullRecordGapCenterValue - 201298,
    fullRecordGapCenterValue - 200542,
    fullRecordGapCenterValue - 200338,
    fullRecordGapCenterValue - 200218,
    fullRecordGapCenterValue - 200212,
    fullRecordGapCenterValue - 199978,
    fullRecordGapCenterValue - 199650,
    fullRecordGapCenterValue - 199414,
    fullRecordGapCenterValue - 199204,
    fullRecordGapCenterValue - 198988,
    fullRecordGapCenterValue - 198844,
    fullRecordGapCenterValue - 198742,
    fullRecordGapCenterValue - 198634,
    fullRecordGapCenterValue - 198508,
    fullRecordGapCenterValue - 198382,
    fullRecordGapCenterValue - 198274,
    fullRecordGapCenterValue - 198238,
    fullRecordGapCenterValue - 198148,
    fullRecordGapCenterValue - 198082,
    fullRecordGapCenterValue - 198034,
    fullRecordGapCenterValue - 197908,
    fullRecordGapCenterValue - 197878,
    fullRecordGapCenterValue - 197854,
    fullRecordGapCenterValue - 197818,
    fullRecordGapCenterValue - 197734,
    fullRecordGapCenterValue - 197668,
    fullRecordGapCenterValue - 197644,
    fullRecordGapCenterValue - 197614,
    fullRecordGapCenterValue - 197602,
    fullRecordGapCenterValue - 197452,
    fullRecordGapCenterValue - 197332,
    fullRecordGapCenterValue - 197194,
    fullRecordGapCenterValue - 197188,
    fullRecordGapCenterValue - 197122,
    fullRecordGapCenterValue - 196858,
    fullRecordGapCenterValue - 196830,
    fullRecordGapCenterValue - 196828]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00045_fermat : ∀ n ∈ fullRecordGapRow00045_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02817_not_prime : ¬(recordGapCenter - 205222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 205222]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02818_not_prime : ¬(recordGapCenter - 205174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 205174]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02819_not_prime : ¬(recordGapCenter - 204994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204994]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02820_not_prime : ¬(recordGapCenter - 204658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204658]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02821_not_prime : ¬(recordGapCenter - 204634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204634]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02822_not_prime : ¬(recordGapCenter - 204298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204298]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02823_not_prime : ¬(recordGapCenter - 204214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204214]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02824_not_prime : ¬(recordGapCenter - 204154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204154]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02825_not_prime : ¬(recordGapCenter - 203758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203758]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02826_not_prime : ¬(recordGapCenter - 203742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203742]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02827_not_prime : ¬(recordGapCenter - 203254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203254]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02828_not_prime : ¬(recordGapCenter - 203074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203074]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02829_not_prime : ¬(recordGapCenter - 203068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203068]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02830_not_prime : ¬(recordGapCenter - 203062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203062]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02831_not_prime : ¬(recordGapCenter - 202858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202858]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02832_not_prime : ¬(recordGapCenter - 202828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202828]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02833_not_prime : ¬(recordGapCenter - 202534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202534]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02834_not_prime : ¬(recordGapCenter - 202348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202348]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02835_not_prime : ¬(recordGapCenter - 202324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202324]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02836_not_prime : ¬(recordGapCenter - 202222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202222]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02837_not_prime : ¬(recordGapCenter - 202012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202012]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02838_not_prime : ¬(recordGapCenter - 201988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201988]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02839_not_prime : ¬(recordGapCenter - 201862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201862]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02840_not_prime : ¬(recordGapCenter - 201814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201814]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02841_not_prime : ¬(recordGapCenter - 201694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201694]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02842_not_prime : ¬(recordGapCenter - 201532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201532]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02843_not_prime : ¬(recordGapCenter - 201364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201364]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02844_not_prime : ¬(recordGapCenter - 201298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201298]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02845_not_prime : ¬(recordGapCenter - 200542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 200542]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02846_not_prime : ¬(recordGapCenter - 200338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 200338]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02847_not_prime : ¬(recordGapCenter - 200218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 200218]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02848_not_prime : ¬(recordGapCenter - 200212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 200212]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02849_not_prime : ¬(recordGapCenter - 199978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 199978]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02850_not_prime : ¬(recordGapCenter - 199650).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 199650]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02851_not_prime : ¬(recordGapCenter - 199414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 199414]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02852_not_prime : ¬(recordGapCenter - 199204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 199204]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02853_not_prime : ¬(recordGapCenter - 198988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198988]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02854_not_prime : ¬(recordGapCenter - 198844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198844]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02855_not_prime : ¬(recordGapCenter - 198742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198742]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02856_not_prime : ¬(recordGapCenter - 198634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198634]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02857_not_prime : ¬(recordGapCenter - 198508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198508]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02858_not_prime : ¬(recordGapCenter - 198382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198382]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02859_not_prime : ¬(recordGapCenter - 198274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198274]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02860_not_prime : ¬(recordGapCenter - 198238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198238]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02861_not_prime : ¬(recordGapCenter - 198148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198148]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02862_not_prime : ¬(recordGapCenter - 198082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198082]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02863_not_prime : ¬(recordGapCenter - 198034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198034]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02864_not_prime : ¬(recordGapCenter - 197908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197908]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02865_not_prime : ¬(recordGapCenter - 197878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197878]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02866_not_prime : ¬(recordGapCenter - 197854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197854]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02867_not_prime : ¬(recordGapCenter - 197818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197818]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02868_not_prime : ¬(recordGapCenter - 197734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197734]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02869_not_prime : ¬(recordGapCenter - 197668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197668]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02870_not_prime : ¬(recordGapCenter - 197644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197644]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02871_not_prime : ¬(recordGapCenter - 197614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197614]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02872_not_prime : ¬(recordGapCenter - 197602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197602]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02873_not_prime : ¬(recordGapCenter - 197452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197452]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02874_not_prime : ¬(recordGapCenter - 197332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197332]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02875_not_prime : ¬(recordGapCenter - 197194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197194]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02876_not_prime : ¬(recordGapCenter - 197188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197188]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02877_not_prime : ¬(recordGapCenter - 197122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197122]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02878_not_prime : ¬(recordGapCenter - 196858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196858]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02879_not_prime : ¬(recordGapCenter - 196830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196830]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

theorem fullRecordGapTerm02880_not_prime : ¬(recordGapCenter - 196828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196828]
  · apply fullRecordGapRow00045_fermat
    simp [fullRecordGapRow00045_values]

end PrimeFactorUnimodality
