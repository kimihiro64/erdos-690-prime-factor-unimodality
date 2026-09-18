import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00157_values : List Nat :=
  [fullRecordGapCenterValue + 600308,
    fullRecordGapCenterValue + 600342,
    fullRecordGapCenterValue + 600356,
    fullRecordGapCenterValue + 600686,
    fullRecordGapCenterValue + 600890,
    fullRecordGapCenterValue + 601022,
    fullRecordGapCenterValue + 601070,
    fullRecordGapCenterValue + 601098,
    fullRecordGapCenterValue + 601316,
    fullRecordGapCenterValue + 601422,
    fullRecordGapCenterValue + 601428,
    fullRecordGapCenterValue + 601508,
    fullRecordGapCenterValue + 601532,
    fullRecordGapCenterValue + 601610,
    fullRecordGapCenterValue + 601688,
    fullRecordGapCenterValue + 601736,
    fullRecordGapCenterValue + 601746,
    fullRecordGapCenterValue + 601862,
    fullRecordGapCenterValue + 602012,
    fullRecordGapCenterValue + 602058,
    fullRecordGapCenterValue + 602078,
    fullRecordGapCenterValue + 602102,
    fullRecordGapCenterValue + 602142,
    fullRecordGapCenterValue + 602306,
    fullRecordGapCenterValue + 602348,
    fullRecordGapCenterValue + 602418,
    fullRecordGapCenterValue + 602570,
    fullRecordGapCenterValue + 602666,
    fullRecordGapCenterValue + 602726,
    fullRecordGapCenterValue + 602772,
    fullRecordGapCenterValue + 602858,
    fullRecordGapCenterValue + 602978,
    fullRecordGapCenterValue + 603062,
    fullRecordGapCenterValue + 603138,
    fullRecordGapCenterValue + 603188,
    fullRecordGapCenterValue + 603338,
    fullRecordGapCenterValue + 603362,
    fullRecordGapCenterValue + 603506,
    fullRecordGapCenterValue + 603530,
    fullRecordGapCenterValue + 603578,
    fullRecordGapCenterValue + 603680,
    fullRecordGapCenterValue + 603726,
    fullRecordGapCenterValue + 603836,
    fullRecordGapCenterValue + 603986,
    fullRecordGapCenterValue + 604052,
    fullRecordGapCenterValue + 604088,
    fullRecordGapCenterValue + 604286,
    fullRecordGapCenterValue + 604346,
    fullRecordGapCenterValue + 604356,
    fullRecordGapCenterValue + 604382,
    fullRecordGapCenterValue + 604398,
    fullRecordGapCenterValue + 604430,
    fullRecordGapCenterValue + 604478,
    fullRecordGapCenterValue + 604646,
    fullRecordGapCenterValue + 604658,
    fullRecordGapCenterValue + 604866,
    fullRecordGapCenterValue + 604938,
    fullRecordGapCenterValue + 604970,
    fullRecordGapCenterValue + 605052,
    fullRecordGapCenterValue + 605082,
    fullRecordGapCenterValue + 605090,
    fullRecordGapCenterValue + 605102,
    fullRecordGapCenterValue + 605126,
    fullRecordGapCenterValue + 605270]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00157_fermat : ∀ n ∈ fullRecordGapRow00157_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09985_not_prime : ¬(recordGapCenter + 600308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600308]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09986_not_prime : ¬(recordGapCenter + 600342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600342]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09987_not_prime : ¬(recordGapCenter + 600356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600356]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09988_not_prime : ¬(recordGapCenter + 600686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600686]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09989_not_prime : ¬(recordGapCenter + 600890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600890]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09990_not_prime : ¬(recordGapCenter + 601022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601022]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09991_not_prime : ¬(recordGapCenter + 601070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601070]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09992_not_prime : ¬(recordGapCenter + 601098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601098]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09993_not_prime : ¬(recordGapCenter + 601316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601316]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09994_not_prime : ¬(recordGapCenter + 601422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601422]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09995_not_prime : ¬(recordGapCenter + 601428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601428]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09996_not_prime : ¬(recordGapCenter + 601508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601508]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09997_not_prime : ¬(recordGapCenter + 601532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601532]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09998_not_prime : ¬(recordGapCenter + 601610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601610]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm09999_not_prime : ¬(recordGapCenter + 601688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601688]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10000_not_prime : ¬(recordGapCenter + 601736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601736]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10001_not_prime : ¬(recordGapCenter + 601746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601746]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10002_not_prime : ¬(recordGapCenter + 601862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 601862]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10003_not_prime : ¬(recordGapCenter + 602012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602012]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10004_not_prime : ¬(recordGapCenter + 602058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602058]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10005_not_prime : ¬(recordGapCenter + 602078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602078]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10006_not_prime : ¬(recordGapCenter + 602102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602102]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10007_not_prime : ¬(recordGapCenter + 602142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602142]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10008_not_prime : ¬(recordGapCenter + 602306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602306]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10009_not_prime : ¬(recordGapCenter + 602348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602348]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10010_not_prime : ¬(recordGapCenter + 602418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602418]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10011_not_prime : ¬(recordGapCenter + 602570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602570]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10012_not_prime : ¬(recordGapCenter + 602666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602666]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10013_not_prime : ¬(recordGapCenter + 602726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602726]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10014_not_prime : ¬(recordGapCenter + 602772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602772]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10015_not_prime : ¬(recordGapCenter + 602858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602858]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10016_not_prime : ¬(recordGapCenter + 602978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 602978]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10017_not_prime : ¬(recordGapCenter + 603062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603062]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10018_not_prime : ¬(recordGapCenter + 603138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603138]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10019_not_prime : ¬(recordGapCenter + 603188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603188]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10020_not_prime : ¬(recordGapCenter + 603338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603338]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10021_not_prime : ¬(recordGapCenter + 603362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603362]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10022_not_prime : ¬(recordGapCenter + 603506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603506]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10023_not_prime : ¬(recordGapCenter + 603530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603530]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10024_not_prime : ¬(recordGapCenter + 603578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603578]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10025_not_prime : ¬(recordGapCenter + 603680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603680]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10026_not_prime : ¬(recordGapCenter + 603726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603726]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10027_not_prime : ¬(recordGapCenter + 603836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603836]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10028_not_prime : ¬(recordGapCenter + 603986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 603986]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10029_not_prime : ¬(recordGapCenter + 604052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604052]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10030_not_prime : ¬(recordGapCenter + 604088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604088]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10031_not_prime : ¬(recordGapCenter + 604286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604286]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10032_not_prime : ¬(recordGapCenter + 604346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604346]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10033_not_prime : ¬(recordGapCenter + 604356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604356]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10034_not_prime : ¬(recordGapCenter + 604382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604382]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10035_not_prime : ¬(recordGapCenter + 604398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604398]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10036_not_prime : ¬(recordGapCenter + 604430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604430]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10037_not_prime : ¬(recordGapCenter + 604478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604478]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10038_not_prime : ¬(recordGapCenter + 604646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604646]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10039_not_prime : ¬(recordGapCenter + 604658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604658]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10040_not_prime : ¬(recordGapCenter + 604866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604866]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10041_not_prime : ¬(recordGapCenter + 604938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604938]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10042_not_prime : ¬(recordGapCenter + 604970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 604970]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10043_not_prime : ¬(recordGapCenter + 605052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605052]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10044_not_prime : ¬(recordGapCenter + 605082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605082]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10045_not_prime : ¬(recordGapCenter + 605090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605090]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10046_not_prime : ¬(recordGapCenter + 605102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605102]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10047_not_prime : ¬(recordGapCenter + 605126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605126]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

theorem fullRecordGapTerm10048_not_prime : ¬(recordGapCenter + 605270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605270]
  · apply fullRecordGapRow00157_fermat
    simp [fullRecordGapRow00157_values]

end PrimeFactorUnimodality
