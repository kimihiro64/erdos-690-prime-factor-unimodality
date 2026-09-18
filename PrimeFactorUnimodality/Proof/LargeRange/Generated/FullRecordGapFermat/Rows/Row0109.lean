import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00109_values : List Nat :=
  [fullRecordGapCenterValue + 387462,
    fullRecordGapCenterValue + 387546,
    fullRecordGapCenterValue + 387578,
    fullRecordGapCenterValue + 387606,
    fullRecordGapCenterValue + 387626,
    fullRecordGapCenterValue + 387836,
    fullRecordGapCenterValue + 387896,
    fullRecordGapCenterValue + 387978,
    fullRecordGapCenterValue + 388028,
    fullRecordGapCenterValue + 388080,
    fullRecordGapCenterValue + 388158,
    fullRecordGapCenterValue + 388166,
    fullRecordGapCenterValue + 388202,
    fullRecordGapCenterValue + 388238,
    fullRecordGapCenterValue + 388298,
    fullRecordGapCenterValue + 388328,
    fullRecordGapCenterValue + 388412,
    fullRecordGapCenterValue + 388568,
    fullRecordGapCenterValue + 388686,
    fullRecordGapCenterValue + 388742,
    fullRecordGapCenterValue + 388748,
    fullRecordGapCenterValue + 388826,
    fullRecordGapCenterValue + 388862,
    fullRecordGapCenterValue + 388866,
    fullRecordGapCenterValue + 388902,
    fullRecordGapCenterValue + 388958,
    fullRecordGapCenterValue + 389042,
    fullRecordGapCenterValue + 389118,
    fullRecordGapCenterValue + 389432,
    fullRecordGapCenterValue + 389492,
    fullRecordGapCenterValue + 389526,
    fullRecordGapCenterValue + 389562,
    fullRecordGapCenterValue + 389678,
    fullRecordGapCenterValue + 389706,
    fullRecordGapCenterValue + 389798,
    fullRecordGapCenterValue + 389996,
    fullRecordGapCenterValue + 390086,
    fullRecordGapCenterValue + 390092,
    fullRecordGapCenterValue + 390098,
    fullRecordGapCenterValue + 390162,
    fullRecordGapCenterValue + 390206,
    fullRecordGapCenterValue + 390296,
    fullRecordGapCenterValue + 390308,
    fullRecordGapCenterValue + 390332,
    fullRecordGapCenterValue + 390506,
    fullRecordGapCenterValue + 390542,
    fullRecordGapCenterValue + 390596,
    fullRecordGapCenterValue + 390666,
    fullRecordGapCenterValue + 390686,
    fullRecordGapCenterValue + 390692,
    fullRecordGapCenterValue + 390938,
    fullRecordGapCenterValue + 390968,
    fullRecordGapCenterValue + 390986,
    fullRecordGapCenterValue + 391038,
    fullRecordGapCenterValue + 391098,
    fullRecordGapCenterValue + 391148,
    fullRecordGapCenterValue + 391218,
    fullRecordGapCenterValue + 391316,
    fullRecordGapCenterValue + 391436,
    fullRecordGapCenterValue + 391542,
    fullRecordGapCenterValue + 391602,
    fullRecordGapCenterValue + 391862,
    fullRecordGapCenterValue + 391868,
    fullRecordGapCenterValue + 391892]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00109_fermat : ∀ n ∈ fullRecordGapRow00109_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06913_not_prime : ¬(recordGapCenter + 387462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387462]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06914_not_prime : ¬(recordGapCenter + 387546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387546]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06915_not_prime : ¬(recordGapCenter + 387578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387578]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06916_not_prime : ¬(recordGapCenter + 387606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387606]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06917_not_prime : ¬(recordGapCenter + 387626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387626]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06918_not_prime : ¬(recordGapCenter + 387836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387836]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06919_not_prime : ¬(recordGapCenter + 387896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387896]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06920_not_prime : ¬(recordGapCenter + 387978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387978]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06921_not_prime : ¬(recordGapCenter + 388028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388028]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06922_not_prime : ¬(recordGapCenter + 388080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388080]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06923_not_prime : ¬(recordGapCenter + 388158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388158]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06924_not_prime : ¬(recordGapCenter + 388166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388166]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06925_not_prime : ¬(recordGapCenter + 388202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388202]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06926_not_prime : ¬(recordGapCenter + 388238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388238]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06927_not_prime : ¬(recordGapCenter + 388298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388298]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06928_not_prime : ¬(recordGapCenter + 388328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388328]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06929_not_prime : ¬(recordGapCenter + 388412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388412]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06930_not_prime : ¬(recordGapCenter + 388568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388568]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06931_not_prime : ¬(recordGapCenter + 388686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388686]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06932_not_prime : ¬(recordGapCenter + 388742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388742]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06933_not_prime : ¬(recordGapCenter + 388748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388748]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06934_not_prime : ¬(recordGapCenter + 388826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388826]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06935_not_prime : ¬(recordGapCenter + 388862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388862]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06936_not_prime : ¬(recordGapCenter + 388866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388866]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06937_not_prime : ¬(recordGapCenter + 388902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388902]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06938_not_prime : ¬(recordGapCenter + 388958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388958]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06939_not_prime : ¬(recordGapCenter + 389042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389042]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06940_not_prime : ¬(recordGapCenter + 389118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389118]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06941_not_prime : ¬(recordGapCenter + 389432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389432]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06942_not_prime : ¬(recordGapCenter + 389492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389492]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06943_not_prime : ¬(recordGapCenter + 389526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389526]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06944_not_prime : ¬(recordGapCenter + 389562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389562]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06945_not_prime : ¬(recordGapCenter + 389678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389678]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06946_not_prime : ¬(recordGapCenter + 389706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389706]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06947_not_prime : ¬(recordGapCenter + 389798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389798]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06948_not_prime : ¬(recordGapCenter + 389996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389996]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06949_not_prime : ¬(recordGapCenter + 390086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390086]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06950_not_prime : ¬(recordGapCenter + 390092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390092]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06951_not_prime : ¬(recordGapCenter + 390098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390098]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06952_not_prime : ¬(recordGapCenter + 390162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390162]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06953_not_prime : ¬(recordGapCenter + 390206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390206]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06954_not_prime : ¬(recordGapCenter + 390296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390296]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06955_not_prime : ¬(recordGapCenter + 390308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390308]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06956_not_prime : ¬(recordGapCenter + 390332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390332]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06957_not_prime : ¬(recordGapCenter + 390506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390506]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06958_not_prime : ¬(recordGapCenter + 390542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390542]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06959_not_prime : ¬(recordGapCenter + 390596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390596]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06960_not_prime : ¬(recordGapCenter + 390666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390666]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06961_not_prime : ¬(recordGapCenter + 390686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390686]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06962_not_prime : ¬(recordGapCenter + 390692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390692]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06963_not_prime : ¬(recordGapCenter + 390938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390938]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06964_not_prime : ¬(recordGapCenter + 390968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390968]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06965_not_prime : ¬(recordGapCenter + 390986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390986]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06966_not_prime : ¬(recordGapCenter + 391038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391038]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06967_not_prime : ¬(recordGapCenter + 391098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391098]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06968_not_prime : ¬(recordGapCenter + 391148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391148]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06969_not_prime : ¬(recordGapCenter + 391218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391218]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06970_not_prime : ¬(recordGapCenter + 391316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391316]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06971_not_prime : ¬(recordGapCenter + 391436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391436]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06972_not_prime : ¬(recordGapCenter + 391542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391542]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06973_not_prime : ¬(recordGapCenter + 391602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391602]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06974_not_prime : ¬(recordGapCenter + 391862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391862]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06975_not_prime : ¬(recordGapCenter + 391868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391868]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

theorem fullRecordGapTerm06976_not_prime : ¬(recordGapCenter + 391892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391892]
  · apply fullRecordGapRow00109_fermat
    simp [fullRecordGapRow00109_values]

end PrimeFactorUnimodality
