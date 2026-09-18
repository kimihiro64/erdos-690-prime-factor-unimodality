import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00092_values : List Nat :=
  [fullRecordGapCenterValue + 301178,
    fullRecordGapCenterValue + 301292,
    fullRecordGapCenterValue + 301326,
    fullRecordGapCenterValue + 301508,
    fullRecordGapCenterValue + 301722,
    fullRecordGapCenterValue + 301746,
    fullRecordGapCenterValue + 301766,
    fullRecordGapCenterValue + 301778,
    fullRecordGapCenterValue + 301802,
    fullRecordGapCenterValue + 301922,
    fullRecordGapCenterValue + 301998,
    fullRecordGapCenterValue + 302156,
    fullRecordGapCenterValue + 302178,
    fullRecordGapCenterValue + 302228,
    fullRecordGapCenterValue + 302306,
    fullRecordGapCenterValue + 302402,
    fullRecordGapCenterValue + 302466,
    fullRecordGapCenterValue + 302526,
    fullRecordGapCenterValue + 302538,
    fullRecordGapCenterValue + 302732,
    fullRecordGapCenterValue + 302766,
    fullRecordGapCenterValue + 302828,
    fullRecordGapCenterValue + 302942,
    fullRecordGapCenterValue + 302972,
    fullRecordGapCenterValue + 302982,
    fullRecordGapCenterValue + 303018,
    fullRecordGapCenterValue + 303062,
    fullRecordGapCenterValue + 303098,
    fullRecordGapCenterValue + 303206,
    fullRecordGapCenterValue + 303258,
    fullRecordGapCenterValue + 303362,
    fullRecordGapCenterValue + 303522,
    fullRecordGapCenterValue + 303542,
    fullRecordGapCenterValue + 303558,
    fullRecordGapCenterValue + 303566,
    fullRecordGapCenterValue + 303762,
    fullRecordGapCenterValue + 303906,
    fullRecordGapCenterValue + 303938,
    fullRecordGapCenterValue + 304026,
    fullRecordGapCenterValue + 304098,
    fullRecordGapCenterValue + 304316,
    fullRecordGapCenterValue + 304406,
    fullRecordGapCenterValue + 304638,
    fullRecordGapCenterValue + 304662,
    fullRecordGapCenterValue + 304778,
    fullRecordGapCenterValue + 304922,
    fullRecordGapCenterValue + 304998,
    fullRecordGapCenterValue + 305198,
    fullRecordGapCenterValue + 305258,
    fullRecordGapCenterValue + 305282,
    fullRecordGapCenterValue + 305342,
    fullRecordGapCenterValue + 305358,
    fullRecordGapCenterValue + 305618,
    fullRecordGapCenterValue + 305702,
    fullRecordGapCenterValue + 305742,
    fullRecordGapCenterValue + 305798,
    fullRecordGapCenterValue + 305852,
    fullRecordGapCenterValue + 305882,
    fullRecordGapCenterValue + 305918,
    fullRecordGapCenterValue + 305958,
    fullRecordGapCenterValue + 305978,
    fullRecordGapCenterValue + 306266,
    fullRecordGapCenterValue + 306282,
    fullRecordGapCenterValue + 306428]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00092_fermat : ∀ n ∈ fullRecordGapRow00092_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05825_not_prime : ¬(recordGapCenter + 301178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301178]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05826_not_prime : ¬(recordGapCenter + 301292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301292]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05827_not_prime : ¬(recordGapCenter + 301326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301326]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05828_not_prime : ¬(recordGapCenter + 301508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301508]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05829_not_prime : ¬(recordGapCenter + 301722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301722]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05830_not_prime : ¬(recordGapCenter + 301746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301746]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05831_not_prime : ¬(recordGapCenter + 301766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301766]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05832_not_prime : ¬(recordGapCenter + 301778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301778]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05833_not_prime : ¬(recordGapCenter + 301802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301802]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05834_not_prime : ¬(recordGapCenter + 301922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301922]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05835_not_prime : ¬(recordGapCenter + 301998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301998]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05836_not_prime : ¬(recordGapCenter + 302156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302156]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05837_not_prime : ¬(recordGapCenter + 302178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302178]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05838_not_prime : ¬(recordGapCenter + 302228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302228]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05839_not_prime : ¬(recordGapCenter + 302306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302306]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05840_not_prime : ¬(recordGapCenter + 302402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302402]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05841_not_prime : ¬(recordGapCenter + 302466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302466]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05842_not_prime : ¬(recordGapCenter + 302526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302526]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05843_not_prime : ¬(recordGapCenter + 302538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302538]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05844_not_prime : ¬(recordGapCenter + 302732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302732]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05845_not_prime : ¬(recordGapCenter + 302766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302766]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05846_not_prime : ¬(recordGapCenter + 302828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302828]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05847_not_prime : ¬(recordGapCenter + 302942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302942]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05848_not_prime : ¬(recordGapCenter + 302972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302972]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05849_not_prime : ¬(recordGapCenter + 302982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 302982]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05850_not_prime : ¬(recordGapCenter + 303018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303018]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05851_not_prime : ¬(recordGapCenter + 303062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303062]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05852_not_prime : ¬(recordGapCenter + 303098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303098]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05853_not_prime : ¬(recordGapCenter + 303206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303206]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05854_not_prime : ¬(recordGapCenter + 303258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303258]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05855_not_prime : ¬(recordGapCenter + 303362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303362]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05856_not_prime : ¬(recordGapCenter + 303522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303522]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05857_not_prime : ¬(recordGapCenter + 303542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303542]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05858_not_prime : ¬(recordGapCenter + 303558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303558]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05859_not_prime : ¬(recordGapCenter + 303566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303566]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05860_not_prime : ¬(recordGapCenter + 303762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303762]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05861_not_prime : ¬(recordGapCenter + 303906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303906]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05862_not_prime : ¬(recordGapCenter + 303938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 303938]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05863_not_prime : ¬(recordGapCenter + 304026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304026]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05864_not_prime : ¬(recordGapCenter + 304098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304098]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05865_not_prime : ¬(recordGapCenter + 304316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304316]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05866_not_prime : ¬(recordGapCenter + 304406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304406]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05867_not_prime : ¬(recordGapCenter + 304638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304638]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05868_not_prime : ¬(recordGapCenter + 304662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304662]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05869_not_prime : ¬(recordGapCenter + 304778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304778]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05870_not_prime : ¬(recordGapCenter + 304922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304922]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05871_not_prime : ¬(recordGapCenter + 304998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 304998]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05872_not_prime : ¬(recordGapCenter + 305198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305198]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05873_not_prime : ¬(recordGapCenter + 305258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305258]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05874_not_prime : ¬(recordGapCenter + 305282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305282]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05875_not_prime : ¬(recordGapCenter + 305342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305342]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05876_not_prime : ¬(recordGapCenter + 305358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305358]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05877_not_prime : ¬(recordGapCenter + 305618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305618]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05878_not_prime : ¬(recordGapCenter + 305702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305702]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05879_not_prime : ¬(recordGapCenter + 305742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305742]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05880_not_prime : ¬(recordGapCenter + 305798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305798]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05881_not_prime : ¬(recordGapCenter + 305852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305852]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05882_not_prime : ¬(recordGapCenter + 305882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305882]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05883_not_prime : ¬(recordGapCenter + 305918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305918]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05884_not_prime : ¬(recordGapCenter + 305958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305958]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05885_not_prime : ¬(recordGapCenter + 305978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 305978]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05886_not_prime : ¬(recordGapCenter + 306266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306266]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05887_not_prime : ¬(recordGapCenter + 306282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306282]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

theorem fullRecordGapTerm05888_not_prime : ¬(recordGapCenter + 306428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306428]
  · apply fullRecordGapRow00092_fermat
    simp [fullRecordGapRow00092_values]

end PrimeFactorUnimodality
