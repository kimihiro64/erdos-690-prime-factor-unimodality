import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00047_values : List Nat :=
  [fullRecordGapCenterValue - 188794,
    fullRecordGapCenterValue - 188662,
    fullRecordGapCenterValue - 188548,
    fullRecordGapCenterValue - 188458,
    fullRecordGapCenterValue - 188218,
    fullRecordGapCenterValue - 188164,
    fullRecordGapCenterValue - 188160,
    fullRecordGapCenterValue - 188158,
    fullRecordGapCenterValue - 187822,
    fullRecordGapCenterValue - 187732,
    fullRecordGapCenterValue - 187522,
    fullRecordGapCenterValue - 187500,
    fullRecordGapCenterValue - 187438,
    fullRecordGapCenterValue - 187324,
    fullRecordGapCenterValue - 187084,
    fullRecordGapCenterValue - 186994,
    fullRecordGapCenterValue - 186988,
    fullRecordGapCenterValue - 186958,
    fullRecordGapCenterValue - 186724,
    fullRecordGapCenterValue - 186624,
    fullRecordGapCenterValue - 186574,
    fullRecordGapCenterValue - 186478,
    fullRecordGapCenterValue - 186340,
    fullRecordGapCenterValue - 186268,
    fullRecordGapCenterValue - 186262,
    fullRecordGapCenterValue - 186178,
    fullRecordGapCenterValue - 186094,
    fullRecordGapCenterValue - 186028,
    fullRecordGapCenterValue - 185908,
    fullRecordGapCenterValue - 185884,
    fullRecordGapCenterValue - 185842,
    fullRecordGapCenterValue - 185698,
    fullRecordGapCenterValue - 185404,
    fullRecordGapCenterValue - 185220,
    fullRecordGapCenterValue - 185092,
    fullRecordGapCenterValue - 185044,
    fullRecordGapCenterValue - 184800,
    fullRecordGapCenterValue - 184774,
    fullRecordGapCenterValue - 184762,
    fullRecordGapCenterValue - 184714,
    fullRecordGapCenterValue - 184588,
    fullRecordGapCenterValue - 184378,
    fullRecordGapCenterValue - 184354,
    fullRecordGapCenterValue - 184018,
    fullRecordGapCenterValue - 183994,
    fullRecordGapCenterValue - 183934,
    fullRecordGapCenterValue - 183750,
    fullRecordGapCenterValue - 183622,
    fullRecordGapCenterValue - 183412,
    fullRecordGapCenterValue - 183382,
    fullRecordGapCenterValue - 183262,
    fullRecordGapCenterValue - 183028,
    fullRecordGapCenterValue - 183004,
    fullRecordGapCenterValue - 182952,
    fullRecordGapCenterValue - 182914,
    fullRecordGapCenterValue - 182794,
    fullRecordGapCenterValue - 182788,
    fullRecordGapCenterValue - 182662,
    fullRecordGapCenterValue - 182524,
    fullRecordGapCenterValue - 182458,
    fullRecordGapCenterValue - 182254,
    fullRecordGapCenterValue - 182250,
    fullRecordGapCenterValue - 182194,
    fullRecordGapCenterValue - 181942]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00047_fermat : ∀ n ∈ fullRecordGapRow00047_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02945_not_prime : ¬(recordGapCenter - 188794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188794]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02946_not_prime : ¬(recordGapCenter - 188662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188662]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02947_not_prime : ¬(recordGapCenter - 188548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188548]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02948_not_prime : ¬(recordGapCenter - 188458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188458]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02949_not_prime : ¬(recordGapCenter - 188218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188218]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02950_not_prime : ¬(recordGapCenter - 188164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188164]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02951_not_prime : ¬(recordGapCenter - 188160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188160]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02952_not_prime : ¬(recordGapCenter - 188158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188158]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02953_not_prime : ¬(recordGapCenter - 187822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187822]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02954_not_prime : ¬(recordGapCenter - 187732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187732]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02955_not_prime : ¬(recordGapCenter - 187522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187522]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02956_not_prime : ¬(recordGapCenter - 187500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187500]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02957_not_prime : ¬(recordGapCenter - 187438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187438]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02958_not_prime : ¬(recordGapCenter - 187324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187324]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02959_not_prime : ¬(recordGapCenter - 187084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187084]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02960_not_prime : ¬(recordGapCenter - 186994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186994]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02961_not_prime : ¬(recordGapCenter - 186988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186988]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02962_not_prime : ¬(recordGapCenter - 186958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186958]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02963_not_prime : ¬(recordGapCenter - 186724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186724]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02964_not_prime : ¬(recordGapCenter - 186624).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186624]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02965_not_prime : ¬(recordGapCenter - 186574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186574]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02966_not_prime : ¬(recordGapCenter - 186478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186478]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02967_not_prime : ¬(recordGapCenter - 186340).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186340]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02968_not_prime : ¬(recordGapCenter - 186268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186268]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02969_not_prime : ¬(recordGapCenter - 186262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186262]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02970_not_prime : ¬(recordGapCenter - 186178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186178]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02971_not_prime : ¬(recordGapCenter - 186094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186094]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02972_not_prime : ¬(recordGapCenter - 186028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186028]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02973_not_prime : ¬(recordGapCenter - 185908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185908]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02974_not_prime : ¬(recordGapCenter - 185884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185884]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02975_not_prime : ¬(recordGapCenter - 185842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185842]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02976_not_prime : ¬(recordGapCenter - 185698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185698]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02977_not_prime : ¬(recordGapCenter - 185404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185404]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02978_not_prime : ¬(recordGapCenter - 185220).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185220]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02979_not_prime : ¬(recordGapCenter - 185092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185092]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02980_not_prime : ¬(recordGapCenter - 185044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185044]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02981_not_prime : ¬(recordGapCenter - 184800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184800]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02982_not_prime : ¬(recordGapCenter - 184774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184774]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02983_not_prime : ¬(recordGapCenter - 184762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184762]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02984_not_prime : ¬(recordGapCenter - 184714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184714]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02985_not_prime : ¬(recordGapCenter - 184588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184588]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02986_not_prime : ¬(recordGapCenter - 184378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184378]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02987_not_prime : ¬(recordGapCenter - 184354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184354]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02988_not_prime : ¬(recordGapCenter - 184018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184018]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02989_not_prime : ¬(recordGapCenter - 183994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183994]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02990_not_prime : ¬(recordGapCenter - 183934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183934]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02991_not_prime : ¬(recordGapCenter - 183750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183750]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02992_not_prime : ¬(recordGapCenter - 183622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183622]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02993_not_prime : ¬(recordGapCenter - 183412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183412]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02994_not_prime : ¬(recordGapCenter - 183382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183382]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02995_not_prime : ¬(recordGapCenter - 183262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183262]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02996_not_prime : ¬(recordGapCenter - 183028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183028]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02997_not_prime : ¬(recordGapCenter - 183004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183004]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02998_not_prime : ¬(recordGapCenter - 182952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182952]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm02999_not_prime : ¬(recordGapCenter - 182914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182914]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03000_not_prime : ¬(recordGapCenter - 182794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182794]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03001_not_prime : ¬(recordGapCenter - 182788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182788]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03002_not_prime : ¬(recordGapCenter - 182662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182662]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03003_not_prime : ¬(recordGapCenter - 182524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182524]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03004_not_prime : ¬(recordGapCenter - 182458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182458]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03005_not_prime : ¬(recordGapCenter - 182254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182254]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03006_not_prime : ¬(recordGapCenter - 182250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182250]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03007_not_prime : ¬(recordGapCenter - 182194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182194]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

theorem fullRecordGapTerm03008_not_prime : ¬(recordGapCenter - 181942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181942]
  · apply fullRecordGapRow00047_fermat
    simp [fullRecordGapRow00047_values]

end PrimeFactorUnimodality
