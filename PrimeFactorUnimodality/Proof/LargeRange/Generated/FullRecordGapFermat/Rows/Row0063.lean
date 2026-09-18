import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00063_values : List Nat :=
  [fullRecordGapCenterValue + 23040,
    fullRecordGapCenterValue + 23328,
    fullRecordGapCenterValue + 24000,
    fullRecordGapCenterValue + 24192,
    fullRecordGapCenterValue + 24300,
    fullRecordGapCenterValue + 24500,
    fullRecordGapCenterValue + 24696,
    fullRecordGapCenterValue + 24750,
    fullRecordGapCenterValue + 24948,
    fullRecordGapCenterValue + 25410,
    fullRecordGapCenterValue + 26250,
    fullRecordGapCenterValue + 26460,
    fullRecordGapCenterValue + 27440,
    fullRecordGapCenterValue + 27648,
    fullRecordGapCenterValue + 27720,
    fullRecordGapCenterValue + 28800,
    fullRecordGapCenterValue + 29160,
    fullRecordGapCenterValue + 29568,
    fullRecordGapCenterValue + 30240,
    fullRecordGapCenterValue + 30720,
    fullRecordGapCenterValue + 30800,
    fullRecordGapCenterValue + 32076,
    fullRecordGapCenterValue + 32340,
    fullRecordGapCenterValue + 32400,
    fullRecordGapCenterValue + 32670,
    fullRecordGapCenterValue + 33000,
    fullRecordGapCenterValue + 33600,
    fullRecordGapCenterValue + 34020,
    fullRecordGapCenterValue + 35000,
    fullRecordGapCenterValue + 35640,
    fullRecordGapCenterValue + 35840,
    fullRecordGapCenterValue + 37500,
    fullRecordGapCenterValue + 37632,
    fullRecordGapCenterValue + 38400,
    fullRecordGapCenterValue + 38880,
    fullRecordGapCenterValue + 39600,
    fullRecordGapCenterValue + 39690,
    fullRecordGapCenterValue + 40656,
    fullRecordGapCenterValue + 41472,
    fullRecordGapCenterValue + 42000,
    fullRecordGapCenterValue + 42336,
    fullRecordGapCenterValue + 43008,
    fullRecordGapCenterValue + 43200,
    fullRecordGapCenterValue + 44000,
    fullRecordGapCenterValue + 44352,
    fullRecordGapCenterValue + 45056,
    fullRecordGapCenterValue + 45276,
    fullRecordGapCenterValue + 46200,
    fullRecordGapCenterValue + 47040,
    fullRecordGapCenterValue + 47250,
    fullRecordGapCenterValue + 47432,
    fullRecordGapCenterValue + 48510,
    fullRecordGapCenterValue + 49896,
    fullRecordGapCenterValue + 50688,
    fullRecordGapCenterValue + 50820,
    fullRecordGapCenterValue + 52272,
    fullRecordGapCenterValue + 52500,
    fullRecordGapCenterValue + 53240,
    fullRecordGapCenterValue + 53760,
    fullRecordGapCenterValue + 54000,
    fullRecordGapCenterValue + 54432,
    fullRecordGapCenterValue + 56700,
    fullRecordGapCenterValue + 57600,
    fullRecordGapCenterValue + 57750]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00063_fermat : ∀ n ∈ fullRecordGapRow00063_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03969_not_prime : ¬(recordGapCenter + 23040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 23040]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03970_not_prime : ¬(recordGapCenter + 23328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 23328]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03971_not_prime : ¬(recordGapCenter + 24000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24000]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03972_not_prime : ¬(recordGapCenter + 24192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24192]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03973_not_prime : ¬(recordGapCenter + 24300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24300]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03974_not_prime : ¬(recordGapCenter + 24500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24500]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03975_not_prime : ¬(recordGapCenter + 24696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24696]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03976_not_prime : ¬(recordGapCenter + 24750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24750]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03977_not_prime : ¬(recordGapCenter + 24948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24948]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03978_not_prime : ¬(recordGapCenter + 25410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 25410]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03979_not_prime : ¬(recordGapCenter + 26250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 26250]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03980_not_prime : ¬(recordGapCenter + 26460).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 26460]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03981_not_prime : ¬(recordGapCenter + 27440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 27440]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03982_not_prime : ¬(recordGapCenter + 27648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 27648]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03983_not_prime : ¬(recordGapCenter + 27720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 27720]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03984_not_prime : ¬(recordGapCenter + 28800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 28800]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03985_not_prime : ¬(recordGapCenter + 29160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 29160]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03986_not_prime : ¬(recordGapCenter + 29568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 29568]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03987_not_prime : ¬(recordGapCenter + 30240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 30240]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03988_not_prime : ¬(recordGapCenter + 30720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 30720]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03989_not_prime : ¬(recordGapCenter + 30800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 30800]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03990_not_prime : ¬(recordGapCenter + 32076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 32076]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03991_not_prime : ¬(recordGapCenter + 32340).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 32340]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03992_not_prime : ¬(recordGapCenter + 32400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 32400]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03993_not_prime : ¬(recordGapCenter + 32670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 32670]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03994_not_prime : ¬(recordGapCenter + 33000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 33000]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03995_not_prime : ¬(recordGapCenter + 33600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 33600]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03996_not_prime : ¬(recordGapCenter + 34020).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 34020]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03997_not_prime : ¬(recordGapCenter + 35000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 35000]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03998_not_prime : ¬(recordGapCenter + 35640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 35640]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm03999_not_prime : ¬(recordGapCenter + 35840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 35840]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04000_not_prime : ¬(recordGapCenter + 37500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 37500]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04001_not_prime : ¬(recordGapCenter + 37632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 37632]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04002_not_prime : ¬(recordGapCenter + 38400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 38400]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04003_not_prime : ¬(recordGapCenter + 38880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 38880]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04004_not_prime : ¬(recordGapCenter + 39600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 39600]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04005_not_prime : ¬(recordGapCenter + 39690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 39690]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04006_not_prime : ¬(recordGapCenter + 40656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 40656]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04007_not_prime : ¬(recordGapCenter + 41472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 41472]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04008_not_prime : ¬(recordGapCenter + 42000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 42000]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04009_not_prime : ¬(recordGapCenter + 42336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 42336]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04010_not_prime : ¬(recordGapCenter + 43008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 43008]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04011_not_prime : ¬(recordGapCenter + 43200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 43200]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04012_not_prime : ¬(recordGapCenter + 44000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 44000]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04013_not_prime : ¬(recordGapCenter + 44352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 44352]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04014_not_prime : ¬(recordGapCenter + 45056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 45056]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04015_not_prime : ¬(recordGapCenter + 45276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 45276]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04016_not_prime : ¬(recordGapCenter + 46200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 46200]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04017_not_prime : ¬(recordGapCenter + 47040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 47040]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04018_not_prime : ¬(recordGapCenter + 47250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 47250]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04019_not_prime : ¬(recordGapCenter + 47432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 47432]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04020_not_prime : ¬(recordGapCenter + 48510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 48510]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04021_not_prime : ¬(recordGapCenter + 49896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 49896]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04022_not_prime : ¬(recordGapCenter + 50688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 50688]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04023_not_prime : ¬(recordGapCenter + 50820).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 50820]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04024_not_prime : ¬(recordGapCenter + 52272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 52272]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04025_not_prime : ¬(recordGapCenter + 52500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 52500]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04026_not_prime : ¬(recordGapCenter + 53240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 53240]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04027_not_prime : ¬(recordGapCenter + 53760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 53760]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04028_not_prime : ¬(recordGapCenter + 54000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 54000]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04029_not_prime : ¬(recordGapCenter + 54432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 54432]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04030_not_prime : ¬(recordGapCenter + 56700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 56700]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04031_not_prime : ¬(recordGapCenter + 57600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 57600]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

theorem fullRecordGapTerm04032_not_prime : ¬(recordGapCenter + 57750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 57750]
  · apply fullRecordGapRow00063_fermat
    simp [fullRecordGapRow00063_values]

end PrimeFactorUnimodality
