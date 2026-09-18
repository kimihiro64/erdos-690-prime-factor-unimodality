import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00085_values : List Nat :=
  [fullRecordGapCenterValue + 263786,
    fullRecordGapCenterValue + 263828,
    fullRecordGapCenterValue + 263972,
    fullRecordGapCenterValue + 264002,
    fullRecordGapCenterValue + 264218,
    fullRecordGapCenterValue + 264338,
    fullRecordGapCenterValue + 264482,
    fullRecordGapCenterValue + 264666,
    fullRecordGapCenterValue + 264692,
    fullRecordGapCenterValue + 264716,
    fullRecordGapCenterValue + 264738,
    fullRecordGapCenterValue + 264786,
    fullRecordGapCenterValue + 264806,
    fullRecordGapCenterValue + 264818,
    fullRecordGapCenterValue + 265022,
    fullRecordGapCenterValue + 265058,
    fullRecordGapCenterValue + 265178,
    fullRecordGapCenterValue + 265262,
    fullRecordGapCenterValue + 265326,
    fullRecordGapCenterValue + 265436,
    fullRecordGapCenterValue + 265508,
    fullRecordGapCenterValue + 265526,
    fullRecordGapCenterValue + 265686,
    fullRecordGapCenterValue + 266078,
    fullRecordGapCenterValue + 266106,
    fullRecordGapCenterValue + 266112,
    fullRecordGapCenterValue + 266138,
    fullRecordGapCenterValue + 266226,
    fullRecordGapCenterValue + 266298,
    fullRecordGapCenterValue + 266348,
    fullRecordGapCenterValue + 266642,
    fullRecordGapCenterValue + 266718,
    fullRecordGapCenterValue + 266852,
    fullRecordGapCenterValue + 266898,
    fullRecordGapCenterValue + 266946,
    fullRecordGapCenterValue + 266982,
    fullRecordGapCenterValue + 266996,
    fullRecordGapCenterValue + 267198,
    fullRecordGapCenterValue + 267222,
    fullRecordGapCenterValue + 267236,
    fullRecordGapCenterValue + 267258,
    fullRecordGapCenterValue + 267300,
    fullRecordGapCenterValue + 267446,
    fullRecordGapCenterValue + 267522,
    fullRecordGapCenterValue + 267702,
    fullRecordGapCenterValue + 267738,
    fullRecordGapCenterValue + 267788,
    fullRecordGapCenterValue + 267942,
    fullRecordGapCenterValue + 267986,
    fullRecordGapCenterValue + 268098,
    fullRecordGapCenterValue + 268118,
    fullRecordGapCenterValue + 268172,
    fullRecordGapCenterValue + 268196,
    fullRecordGapCenterValue + 268206,
    fullRecordGapCenterValue + 268538,
    fullRecordGapCenterValue + 268556,
    fullRecordGapCenterValue + 268662,
    fullRecordGapCenterValue + 268718,
    fullRecordGapCenterValue + 268802,
    fullRecordGapCenterValue + 268886,
    fullRecordGapCenterValue + 269006,
    fullRecordGapCenterValue + 269202,
    fullRecordGapCenterValue + 269322,
    fullRecordGapCenterValue + 269396]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00085_fermat : ∀ n ∈ fullRecordGapRow00085_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05377_not_prime : ¬(recordGapCenter + 263786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 263786]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05378_not_prime : ¬(recordGapCenter + 263828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 263828]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05379_not_prime : ¬(recordGapCenter + 263972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 263972]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05380_not_prime : ¬(recordGapCenter + 264002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264002]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05381_not_prime : ¬(recordGapCenter + 264218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264218]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05382_not_prime : ¬(recordGapCenter + 264338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264338]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05383_not_prime : ¬(recordGapCenter + 264482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264482]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05384_not_prime : ¬(recordGapCenter + 264666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264666]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05385_not_prime : ¬(recordGapCenter + 264692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264692]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05386_not_prime : ¬(recordGapCenter + 264716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264716]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05387_not_prime : ¬(recordGapCenter + 264738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264738]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05388_not_prime : ¬(recordGapCenter + 264786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264786]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05389_not_prime : ¬(recordGapCenter + 264806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264806]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05390_not_prime : ¬(recordGapCenter + 264818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 264818]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05391_not_prime : ¬(recordGapCenter + 265022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265022]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05392_not_prime : ¬(recordGapCenter + 265058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265058]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05393_not_prime : ¬(recordGapCenter + 265178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265178]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05394_not_prime : ¬(recordGapCenter + 265262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265262]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05395_not_prime : ¬(recordGapCenter + 265326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265326]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05396_not_prime : ¬(recordGapCenter + 265436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265436]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05397_not_prime : ¬(recordGapCenter + 265508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265508]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05398_not_prime : ¬(recordGapCenter + 265526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265526]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05399_not_prime : ¬(recordGapCenter + 265686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 265686]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05400_not_prime : ¬(recordGapCenter + 266078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266078]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05401_not_prime : ¬(recordGapCenter + 266106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266106]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05402_not_prime : ¬(recordGapCenter + 266112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266112]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05403_not_prime : ¬(recordGapCenter + 266138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266138]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05404_not_prime : ¬(recordGapCenter + 266226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266226]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05405_not_prime : ¬(recordGapCenter + 266298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266298]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05406_not_prime : ¬(recordGapCenter + 266348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266348]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05407_not_prime : ¬(recordGapCenter + 266642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266642]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05408_not_prime : ¬(recordGapCenter + 266718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266718]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05409_not_prime : ¬(recordGapCenter + 266852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266852]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05410_not_prime : ¬(recordGapCenter + 266898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266898]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05411_not_prime : ¬(recordGapCenter + 266946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266946]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05412_not_prime : ¬(recordGapCenter + 266982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266982]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05413_not_prime : ¬(recordGapCenter + 266996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 266996]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05414_not_prime : ¬(recordGapCenter + 267198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267198]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05415_not_prime : ¬(recordGapCenter + 267222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267222]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05416_not_prime : ¬(recordGapCenter + 267236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267236]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05417_not_prime : ¬(recordGapCenter + 267258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267258]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05418_not_prime : ¬(recordGapCenter + 267300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267300]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05419_not_prime : ¬(recordGapCenter + 267446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267446]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05420_not_prime : ¬(recordGapCenter + 267522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267522]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05421_not_prime : ¬(recordGapCenter + 267702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267702]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05422_not_prime : ¬(recordGapCenter + 267738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267738]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05423_not_prime : ¬(recordGapCenter + 267788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267788]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05424_not_prime : ¬(recordGapCenter + 267942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267942]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05425_not_prime : ¬(recordGapCenter + 267986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 267986]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05426_not_prime : ¬(recordGapCenter + 268098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268098]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05427_not_prime : ¬(recordGapCenter + 268118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268118]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05428_not_prime : ¬(recordGapCenter + 268172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268172]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05429_not_prime : ¬(recordGapCenter + 268196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268196]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05430_not_prime : ¬(recordGapCenter + 268206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268206]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05431_not_prime : ¬(recordGapCenter + 268538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268538]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05432_not_prime : ¬(recordGapCenter + 268556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268556]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05433_not_prime : ¬(recordGapCenter + 268662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268662]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05434_not_prime : ¬(recordGapCenter + 268718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268718]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05435_not_prime : ¬(recordGapCenter + 268802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268802]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05436_not_prime : ¬(recordGapCenter + 268886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 268886]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05437_not_prime : ¬(recordGapCenter + 269006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269006]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05438_not_prime : ¬(recordGapCenter + 269202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269202]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05439_not_prime : ¬(recordGapCenter + 269322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269322]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

theorem fullRecordGapTerm05440_not_prime : ¬(recordGapCenter + 269396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269396]
  · apply fullRecordGapRow00085_fermat
    simp [fullRecordGapRow00085_values]

end PrimeFactorUnimodality
