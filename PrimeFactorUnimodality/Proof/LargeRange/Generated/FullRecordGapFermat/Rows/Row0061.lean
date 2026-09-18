import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00061_values : List Nat :=
  [fullRecordGapCenterValue + 968,
    fullRecordGapCenterValue + 990,
    fullRecordGapCenterValue + 1050,
    fullRecordGapCenterValue + 1200,
    fullRecordGapCenterValue + 1260,
    fullRecordGapCenterValue + 1320,
    fullRecordGapCenterValue + 1386,
    fullRecordGapCenterValue + 1452,
    fullRecordGapCenterValue + 1500,
    fullRecordGapCenterValue + 1620,
    fullRecordGapCenterValue + 1650,
    fullRecordGapCenterValue + 1680,
    fullRecordGapCenterValue + 1782,
    fullRecordGapCenterValue + 1848,
    fullRecordGapCenterValue + 2016,
    fullRecordGapCenterValue + 2048,
    fullRecordGapCenterValue + 2058,
    fullRecordGapCenterValue + 2100,
    fullRecordGapCenterValue + 2112,
    fullRecordGapCenterValue + 2156,
    fullRecordGapCenterValue + 2160,
    fullRecordGapCenterValue + 2178,
    fullRecordGapCenterValue + 2352,
    fullRecordGapCenterValue + 2376,
    fullRecordGapCenterValue + 2430,
    fullRecordGapCenterValue + 2450,
    fullRecordGapCenterValue + 2640,
    fullRecordGapCenterValue + 2646,
    fullRecordGapCenterValue + 2772,
    fullRecordGapCenterValue + 2816,
    fullRecordGapCenterValue + 2916,
    fullRecordGapCenterValue + 2940,
    fullRecordGapCenterValue + 2970,
    fullRecordGapCenterValue + 3168,
    fullRecordGapCenterValue + 3200,
    fullRecordGapCenterValue + 3360,
    fullRecordGapCenterValue + 3402,
    fullRecordGapCenterValue + 3456,
    fullRecordGapCenterValue + 3500,
    fullRecordGapCenterValue + 3630,
    fullRecordGapCenterValue + 3696,
    fullRecordGapCenterValue + 3750,
    fullRecordGapCenterValue + 3872,
    fullRecordGapCenterValue + 3920,
    fullRecordGapCenterValue + 3960,
    fullRecordGapCenterValue + 4158,
    fullRecordGapCenterValue + 4320,
    fullRecordGapCenterValue + 4536,
    fullRecordGapCenterValue + 4608,
    fullRecordGapCenterValue + 4860,
    fullRecordGapCenterValue + 4928,
    fullRecordGapCenterValue + 4950,
    fullRecordGapCenterValue + 5000,
    fullRecordGapCenterValue + 5120,
    fullRecordGapCenterValue + 5280,
    fullRecordGapCenterValue + 5292,
    fullRecordGapCenterValue + 5346,
    fullRecordGapCenterValue + 5390,
    fullRecordGapCenterValue + 5670,
    fullRecordGapCenterValue + 5808,
    fullRecordGapCenterValue + 5832,
    fullRecordGapCenterValue + 5880,
    fullRecordGapCenterValue + 6300,
    fullRecordGapCenterValue + 6336]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00061_fermat : ∀ n ∈ fullRecordGapRow00061_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03841_not_prime : ¬(recordGapCenter + 968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 968]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03842_not_prime : ¬(recordGapCenter + 990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 990]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03843_not_prime : ¬(recordGapCenter + 1050).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1050]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03844_not_prime : ¬(recordGapCenter + 1200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1200]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03845_not_prime : ¬(recordGapCenter + 1260).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1260]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03846_not_prime : ¬(recordGapCenter + 1320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1320]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03847_not_prime : ¬(recordGapCenter + 1386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1386]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03848_not_prime : ¬(recordGapCenter + 1452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1452]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03849_not_prime : ¬(recordGapCenter + 1500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1500]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03850_not_prime : ¬(recordGapCenter + 1620).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1620]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03851_not_prime : ¬(recordGapCenter + 1650).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1650]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03852_not_prime : ¬(recordGapCenter + 1680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1680]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03853_not_prime : ¬(recordGapCenter + 1782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1782]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03854_not_prime : ¬(recordGapCenter + 1848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1848]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03855_not_prime : ¬(recordGapCenter + 2016).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2016]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03856_not_prime : ¬(recordGapCenter + 2048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2048]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03857_not_prime : ¬(recordGapCenter + 2058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2058]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03858_not_prime : ¬(recordGapCenter + 2100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2100]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03859_not_prime : ¬(recordGapCenter + 2112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2112]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03860_not_prime : ¬(recordGapCenter + 2156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2156]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03861_not_prime : ¬(recordGapCenter + 2160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2160]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03862_not_prime : ¬(recordGapCenter + 2178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2178]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03863_not_prime : ¬(recordGapCenter + 2352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2352]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03864_not_prime : ¬(recordGapCenter + 2376).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2376]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03865_not_prime : ¬(recordGapCenter + 2430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2430]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03866_not_prime : ¬(recordGapCenter + 2450).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2450]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03867_not_prime : ¬(recordGapCenter + 2640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2640]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03868_not_prime : ¬(recordGapCenter + 2646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2646]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03869_not_prime : ¬(recordGapCenter + 2772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2772]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03870_not_prime : ¬(recordGapCenter + 2816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2816]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03871_not_prime : ¬(recordGapCenter + 2916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2916]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03872_not_prime : ¬(recordGapCenter + 2940).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2940]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03873_not_prime : ¬(recordGapCenter + 2970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2970]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03874_not_prime : ¬(recordGapCenter + 3168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3168]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03875_not_prime : ¬(recordGapCenter + 3200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3200]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03876_not_prime : ¬(recordGapCenter + 3360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3360]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03877_not_prime : ¬(recordGapCenter + 3402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3402]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03878_not_prime : ¬(recordGapCenter + 3456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3456]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03879_not_prime : ¬(recordGapCenter + 3500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3500]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03880_not_prime : ¬(recordGapCenter + 3630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3630]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03881_not_prime : ¬(recordGapCenter + 3696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3696]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03882_not_prime : ¬(recordGapCenter + 3750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3750]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03883_not_prime : ¬(recordGapCenter + 3872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3872]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03884_not_prime : ¬(recordGapCenter + 3920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3920]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03885_not_prime : ¬(recordGapCenter + 3960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3960]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03886_not_prime : ¬(recordGapCenter + 4158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4158]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03887_not_prime : ¬(recordGapCenter + 4320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4320]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03888_not_prime : ¬(recordGapCenter + 4536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4536]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03889_not_prime : ¬(recordGapCenter + 4608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4608]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03890_not_prime : ¬(recordGapCenter + 4860).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4860]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03891_not_prime : ¬(recordGapCenter + 4928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4928]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03892_not_prime : ¬(recordGapCenter + 4950).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4950]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03893_not_prime : ¬(recordGapCenter + 5000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5000]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03894_not_prime : ¬(recordGapCenter + 5120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5120]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03895_not_prime : ¬(recordGapCenter + 5280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5280]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03896_not_prime : ¬(recordGapCenter + 5292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5292]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03897_not_prime : ¬(recordGapCenter + 5346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5346]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03898_not_prime : ¬(recordGapCenter + 5390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5390]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03899_not_prime : ¬(recordGapCenter + 5670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5670]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03900_not_prime : ¬(recordGapCenter + 5808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5808]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03901_not_prime : ¬(recordGapCenter + 5832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5832]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03902_not_prime : ¬(recordGapCenter + 5880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5880]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03903_not_prime : ¬(recordGapCenter + 6300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 6300]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

theorem fullRecordGapTerm03904_not_prime : ¬(recordGapCenter + 6336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 6336]
  · apply fullRecordGapRow00061_fermat
    simp [fullRecordGapRow00061_values]

end PrimeFactorUnimodality
