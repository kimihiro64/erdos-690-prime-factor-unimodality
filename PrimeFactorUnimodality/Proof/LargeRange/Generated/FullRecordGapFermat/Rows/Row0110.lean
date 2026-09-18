import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00110_values : List Nat :=
  [fullRecordGapCenterValue + 391946,
    fullRecordGapCenterValue + 391962,
    fullRecordGapCenterValue + 392040,
    fullRecordGapCenterValue + 392142,
    fullRecordGapCenterValue + 392222,
    fullRecordGapCenterValue + 392226,
    fullRecordGapCenterValue + 392358,
    fullRecordGapCenterValue + 392582,
    fullRecordGapCenterValue + 392648,
    fullRecordGapCenterValue + 392682,
    fullRecordGapCenterValue + 392858,
    fullRecordGapCenterValue + 392936,
    fullRecordGapCenterValue + 393086,
    fullRecordGapCenterValue + 393188,
    fullRecordGapCenterValue + 393258,
    fullRecordGapCenterValue + 393306,
    fullRecordGapCenterValue + 393416,
    fullRecordGapCenterValue + 393522,
    fullRecordGapCenterValue + 393702,
    fullRecordGapCenterValue + 393716,
    fullRecordGapCenterValue + 393746,
    fullRecordGapCenterValue + 394062,
    fullRecordGapCenterValue + 394076,
    fullRecordGapCenterValue + 394088,
    fullRecordGapCenterValue + 394172,
    fullRecordGapCenterValue + 394178,
    fullRecordGapCenterValue + 394206,
    fullRecordGapCenterValue + 394242,
    fullRecordGapCenterValue + 394278,
    fullRecordGapCenterValue + 394292,
    fullRecordGapCenterValue + 394322,
    fullRecordGapCenterValue + 394556,
    fullRecordGapCenterValue + 394586,
    fullRecordGapCenterValue + 394622,
    fullRecordGapCenterValue + 394662,
    fullRecordGapCenterValue + 394682,
    fullRecordGapCenterValue + 394712,
    fullRecordGapCenterValue + 394718,
    fullRecordGapCenterValue + 394766,
    fullRecordGapCenterValue + 394868,
    fullRecordGapCenterValue + 394916,
    fullRecordGapCenterValue + 394952,
    fullRecordGapCenterValue + 394986,
    fullRecordGapCenterValue + 395022,
    fullRecordGapCenterValue + 395078,
    fullRecordGapCenterValue + 395106,
    fullRecordGapCenterValue + 395202,
    fullRecordGapCenterValue + 395286,
    fullRecordGapCenterValue + 395288,
    fullRecordGapCenterValue + 395378,
    fullRecordGapCenterValue + 395526,
    fullRecordGapCenterValue + 395636,
    fullRecordGapCenterValue + 395816,
    fullRecordGapCenterValue + 395852,
    fullRecordGapCenterValue + 395942,
    fullRecordGapCenterValue + 395958,
    fullRecordGapCenterValue + 396000,
    fullRecordGapCenterValue + 396026,
    fullRecordGapCenterValue + 396068,
    fullRecordGapCenterValue + 396086,
    fullRecordGapCenterValue + 396212,
    fullRecordGapCenterValue + 396218,
    fullRecordGapCenterValue + 396246,
    fullRecordGapCenterValue + 396278]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00110_fermat : ∀ n ∈ fullRecordGapRow00110_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06977_not_prime : ¬(recordGapCenter + 391946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391946]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06978_not_prime : ¬(recordGapCenter + 391962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391962]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06979_not_prime : ¬(recordGapCenter + 392040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392040]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06980_not_prime : ¬(recordGapCenter + 392142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392142]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06981_not_prime : ¬(recordGapCenter + 392222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392222]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06982_not_prime : ¬(recordGapCenter + 392226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392226]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06983_not_prime : ¬(recordGapCenter + 392358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392358]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06984_not_prime : ¬(recordGapCenter + 392582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392582]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06985_not_prime : ¬(recordGapCenter + 392648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392648]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06986_not_prime : ¬(recordGapCenter + 392682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392682]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06987_not_prime : ¬(recordGapCenter + 392858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392858]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06988_not_prime : ¬(recordGapCenter + 392936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392936]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06989_not_prime : ¬(recordGapCenter + 393086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393086]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06990_not_prime : ¬(recordGapCenter + 393188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393188]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06991_not_prime : ¬(recordGapCenter + 393258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393258]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06992_not_prime : ¬(recordGapCenter + 393306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393306]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06993_not_prime : ¬(recordGapCenter + 393416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393416]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06994_not_prime : ¬(recordGapCenter + 393522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393522]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06995_not_prime : ¬(recordGapCenter + 393702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393702]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06996_not_prime : ¬(recordGapCenter + 393716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393716]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06997_not_prime : ¬(recordGapCenter + 393746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393746]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06998_not_prime : ¬(recordGapCenter + 394062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394062]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm06999_not_prime : ¬(recordGapCenter + 394076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394076]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07000_not_prime : ¬(recordGapCenter + 394088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394088]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07001_not_prime : ¬(recordGapCenter + 394172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394172]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07002_not_prime : ¬(recordGapCenter + 394178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394178]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07003_not_prime : ¬(recordGapCenter + 394206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394206]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07004_not_prime : ¬(recordGapCenter + 394242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394242]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07005_not_prime : ¬(recordGapCenter + 394278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394278]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07006_not_prime : ¬(recordGapCenter + 394292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394292]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07007_not_prime : ¬(recordGapCenter + 394322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394322]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07008_not_prime : ¬(recordGapCenter + 394556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394556]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07009_not_prime : ¬(recordGapCenter + 394586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394586]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07010_not_prime : ¬(recordGapCenter + 394622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394622]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07011_not_prime : ¬(recordGapCenter + 394662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394662]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07012_not_prime : ¬(recordGapCenter + 394682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394682]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07013_not_prime : ¬(recordGapCenter + 394712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394712]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07014_not_prime : ¬(recordGapCenter + 394718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394718]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07015_not_prime : ¬(recordGapCenter + 394766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394766]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07016_not_prime : ¬(recordGapCenter + 394868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394868]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07017_not_prime : ¬(recordGapCenter + 394916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394916]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07018_not_prime : ¬(recordGapCenter + 394952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394952]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07019_not_prime : ¬(recordGapCenter + 394986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394986]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07020_not_prime : ¬(recordGapCenter + 395022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395022]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07021_not_prime : ¬(recordGapCenter + 395078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395078]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07022_not_prime : ¬(recordGapCenter + 395106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395106]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07023_not_prime : ¬(recordGapCenter + 395202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395202]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07024_not_prime : ¬(recordGapCenter + 395286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395286]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07025_not_prime : ¬(recordGapCenter + 395288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395288]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07026_not_prime : ¬(recordGapCenter + 395378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395378]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07027_not_prime : ¬(recordGapCenter + 395526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395526]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07028_not_prime : ¬(recordGapCenter + 395636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395636]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07029_not_prime : ¬(recordGapCenter + 395816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395816]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07030_not_prime : ¬(recordGapCenter + 395852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395852]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07031_not_prime : ¬(recordGapCenter + 395942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395942]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07032_not_prime : ¬(recordGapCenter + 395958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395958]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07033_not_prime : ¬(recordGapCenter + 396000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396000]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07034_not_prime : ¬(recordGapCenter + 396026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396026]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07035_not_prime : ¬(recordGapCenter + 396068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396068]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07036_not_prime : ¬(recordGapCenter + 396086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396086]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07037_not_prime : ¬(recordGapCenter + 396212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396212]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07038_not_prime : ¬(recordGapCenter + 396218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396218]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07039_not_prime : ¬(recordGapCenter + 396246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396246]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

theorem fullRecordGapTerm07040_not_prime : ¬(recordGapCenter + 396278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396278]
  · apply fullRecordGapRow00110_fermat
    simp [fullRecordGapRow00110_values]

end PrimeFactorUnimodality
