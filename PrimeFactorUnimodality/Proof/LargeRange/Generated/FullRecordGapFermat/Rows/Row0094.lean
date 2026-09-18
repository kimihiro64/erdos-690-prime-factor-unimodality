import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00094_values : List Nat :=
  [fullRecordGapCenterValue + 311666,
    fullRecordGapCenterValue + 311732,
    fullRecordGapCenterValue + 311838,
    fullRecordGapCenterValue + 311850,
    fullRecordGapCenterValue + 311876,
    fullRecordGapCenterValue + 312126,
    fullRecordGapCenterValue + 312162,
    fullRecordGapCenterValue + 312218,
    fullRecordGapCenterValue + 312236,
    fullRecordGapCenterValue + 312302,
    fullRecordGapCenterValue + 312306,
    fullRecordGapCenterValue + 312812,
    fullRecordGapCenterValue + 312882,
    fullRecordGapCenterValue + 312932,
    fullRecordGapCenterValue + 313022,
    fullRecordGapCenterValue + 313086,
    fullRecordGapCenterValue + 313178,
    fullRecordGapCenterValue + 313202,
    fullRecordGapCenterValue + 313268,
    fullRecordGapCenterValue + 313358,
    fullRecordGapCenterValue + 313388,
    fullRecordGapCenterValue + 313422,
    fullRecordGapCenterValue + 313598,
    fullRecordGapCenterValue + 313632,
    fullRecordGapCenterValue + 313868,
    fullRecordGapCenterValue + 313878,
    fullRecordGapCenterValue + 313926,
    fullRecordGapCenterValue + 313988,
    fullRecordGapCenterValue + 314162,
    fullRecordGapCenterValue + 314322,
    fullRecordGapCenterValue + 314346,
    fullRecordGapCenterValue + 314742,
    fullRecordGapCenterValue + 314786,
    fullRecordGapCenterValue + 314928,
    fullRecordGapCenterValue + 314966,
    fullRecordGapCenterValue + 315000,
    fullRecordGapCenterValue + 315038,
    fullRecordGapCenterValue + 315066,
    fullRecordGapCenterValue + 315086,
    fullRecordGapCenterValue + 315116,
    fullRecordGapCenterValue + 315158,
    fullRecordGapCenterValue + 315318,
    fullRecordGapCenterValue + 315338,
    fullRecordGapCenterValue + 315392,
    fullRecordGapCenterValue + 315572,
    fullRecordGapCenterValue + 315626,
    fullRecordGapCenterValue + 315662,
    fullRecordGapCenterValue + 315716,
    fullRecordGapCenterValue + 315786,
    fullRecordGapCenterValue + 315956,
    fullRecordGapCenterValue + 316058,
    fullRecordGapCenterValue + 316142,
    fullRecordGapCenterValue + 316146,
    fullRecordGapCenterValue + 316172,
    fullRecordGapCenterValue + 316226,
    fullRecordGapCenterValue + 316326,
    fullRecordGapCenterValue + 316538,
    fullRecordGapCenterValue + 316556,
    fullRecordGapCenterValue + 316586,
    fullRecordGapCenterValue + 316698,
    fullRecordGapCenterValue + 316748,
    fullRecordGapCenterValue + 316800,
    fullRecordGapCenterValue + 316842,
    fullRecordGapCenterValue + 316878]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00094_fermat : ∀ n ∈ fullRecordGapRow00094_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05953_not_prime : ¬(recordGapCenter + 311666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311666]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05954_not_prime : ¬(recordGapCenter + 311732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311732]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05955_not_prime : ¬(recordGapCenter + 311838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311838]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05956_not_prime : ¬(recordGapCenter + 311850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311850]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05957_not_prime : ¬(recordGapCenter + 311876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311876]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05958_not_prime : ¬(recordGapCenter + 312126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312126]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05959_not_prime : ¬(recordGapCenter + 312162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312162]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05960_not_prime : ¬(recordGapCenter + 312218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312218]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05961_not_prime : ¬(recordGapCenter + 312236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312236]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05962_not_prime : ¬(recordGapCenter + 312302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312302]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05963_not_prime : ¬(recordGapCenter + 312306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312306]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05964_not_prime : ¬(recordGapCenter + 312812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312812]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05965_not_prime : ¬(recordGapCenter + 312882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312882]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05966_not_prime : ¬(recordGapCenter + 312932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 312932]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05967_not_prime : ¬(recordGapCenter + 313022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313022]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05968_not_prime : ¬(recordGapCenter + 313086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313086]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05969_not_prime : ¬(recordGapCenter + 313178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313178]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05970_not_prime : ¬(recordGapCenter + 313202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313202]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05971_not_prime : ¬(recordGapCenter + 313268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313268]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05972_not_prime : ¬(recordGapCenter + 313358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313358]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05973_not_prime : ¬(recordGapCenter + 313388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313388]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05974_not_prime : ¬(recordGapCenter + 313422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313422]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05975_not_prime : ¬(recordGapCenter + 313598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313598]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05976_not_prime : ¬(recordGapCenter + 313632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313632]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05977_not_prime : ¬(recordGapCenter + 313868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313868]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05978_not_prime : ¬(recordGapCenter + 313878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313878]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05979_not_prime : ¬(recordGapCenter + 313926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313926]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05980_not_prime : ¬(recordGapCenter + 313988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 313988]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05981_not_prime : ¬(recordGapCenter + 314162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 314162]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05982_not_prime : ¬(recordGapCenter + 314322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 314322]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05983_not_prime : ¬(recordGapCenter + 314346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 314346]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05984_not_prime : ¬(recordGapCenter + 314742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 314742]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05985_not_prime : ¬(recordGapCenter + 314786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 314786]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05986_not_prime : ¬(recordGapCenter + 314928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 314928]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05987_not_prime : ¬(recordGapCenter + 314966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 314966]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05988_not_prime : ¬(recordGapCenter + 315000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315000]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05989_not_prime : ¬(recordGapCenter + 315038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315038]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05990_not_prime : ¬(recordGapCenter + 315066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315066]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05991_not_prime : ¬(recordGapCenter + 315086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315086]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05992_not_prime : ¬(recordGapCenter + 315116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315116]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05993_not_prime : ¬(recordGapCenter + 315158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315158]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05994_not_prime : ¬(recordGapCenter + 315318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315318]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05995_not_prime : ¬(recordGapCenter + 315338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315338]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05996_not_prime : ¬(recordGapCenter + 315392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315392]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05997_not_prime : ¬(recordGapCenter + 315572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315572]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05998_not_prime : ¬(recordGapCenter + 315626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315626]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm05999_not_prime : ¬(recordGapCenter + 315662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315662]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06000_not_prime : ¬(recordGapCenter + 315716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315716]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06001_not_prime : ¬(recordGapCenter + 315786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315786]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06002_not_prime : ¬(recordGapCenter + 315956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 315956]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06003_not_prime : ¬(recordGapCenter + 316058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316058]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06004_not_prime : ¬(recordGapCenter + 316142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316142]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06005_not_prime : ¬(recordGapCenter + 316146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316146]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06006_not_prime : ¬(recordGapCenter + 316172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316172]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06007_not_prime : ¬(recordGapCenter + 316226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316226]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06008_not_prime : ¬(recordGapCenter + 316326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316326]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06009_not_prime : ¬(recordGapCenter + 316538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316538]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06010_not_prime : ¬(recordGapCenter + 316556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316556]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06011_not_prime : ¬(recordGapCenter + 316586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316586]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06012_not_prime : ¬(recordGapCenter + 316698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316698]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06013_not_prime : ¬(recordGapCenter + 316748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316748]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06014_not_prime : ¬(recordGapCenter + 316800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316800]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06015_not_prime : ¬(recordGapCenter + 316842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316842]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

theorem fullRecordGapTerm06016_not_prime : ¬(recordGapCenter + 316878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316878]
  · apply fullRecordGapRow00094_fermat
    simp [fullRecordGapRow00094_values]

end PrimeFactorUnimodality
