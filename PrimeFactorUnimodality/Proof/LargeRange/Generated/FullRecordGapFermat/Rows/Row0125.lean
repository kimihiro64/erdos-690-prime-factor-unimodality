import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00125_values : List Nat :=
  [fullRecordGapCenterValue + 464756,
    fullRecordGapCenterValue + 465162,
    fullRecordGapCenterValue + 465176,
    fullRecordGapCenterValue + 465242,
    fullRecordGapCenterValue + 465326,
    fullRecordGapCenterValue + 465342,
    fullRecordGapCenterValue + 465368,
    fullRecordGapCenterValue + 465398,
    fullRecordGapCenterValue + 465438,
    fullRecordGapCenterValue + 465512,
    fullRecordGapCenterValue + 465638,
    fullRecordGapCenterValue + 465722,
    fullRecordGapCenterValue + 465782,
    fullRecordGapCenterValue + 465788,
    fullRecordGapCenterValue + 465848,
    fullRecordGapCenterValue + 465882,
    fullRecordGapCenterValue + 465896,
    fullRecordGapCenterValue + 466028,
    fullRecordGapCenterValue + 466086,
    fullRecordGapCenterValue + 466266,
    fullRecordGapCenterValue + 466278,
    fullRecordGapCenterValue + 466338,
    fullRecordGapCenterValue + 466386,
    fullRecordGapCenterValue + 466442,
    fullRecordGapCenterValue + 466478,
    fullRecordGapCenterValue + 466482,
    fullRecordGapCenterValue + 466560,
    fullRecordGapCenterValue + 466566,
    fullRecordGapCenterValue + 466586,
    fullRecordGapCenterValue + 466652,
    fullRecordGapCenterValue + 466706,
    fullRecordGapCenterValue + 466782,
    fullRecordGapCenterValue + 466790,
    fullRecordGapCenterValue + 467156,
    fullRecordGapCenterValue + 467178,
    fullRecordGapCenterValue + 467202,
    fullRecordGapCenterValue + 467378,
    fullRecordGapCenterValue + 467426,
    fullRecordGapCenterValue + 467486,
    fullRecordGapCenterValue + 467510,
    fullRecordGapCenterValue + 467598,
    fullRecordGapCenterValue + 467706,
    fullRecordGapCenterValue + 467708,
    fullRecordGapCenterValue + 467822,
    fullRecordGapCenterValue + 467862,
    fullRecordGapCenterValue + 467876,
    fullRecordGapCenterValue + 467972,
    fullRecordGapCenterValue + 468042,
    fullRecordGapCenterValue + 468086,
    fullRecordGapCenterValue + 468242,
    fullRecordGapCenterValue + 468246,
    fullRecordGapCenterValue + 468290,
    fullRecordGapCenterValue + 468296,
    fullRecordGapCenterValue + 468386,
    fullRecordGapCenterValue + 468476,
    fullRecordGapCenterValue + 468542,
    fullRecordGapCenterValue + 468606,
    fullRecordGapCenterValue + 468632,
    fullRecordGapCenterValue + 468638,
    fullRecordGapCenterValue + 468686,
    fullRecordGapCenterValue + 468770,
    fullRecordGapCenterValue + 468822,
    fullRecordGapCenterValue + 468836,
    fullRecordGapCenterValue + 468890]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00125_fermat : ∀ n ∈ fullRecordGapRow00125_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07937_not_prime : ¬(recordGapCenter + 464756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464756]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07938_not_prime : ¬(recordGapCenter + 465162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465162]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07939_not_prime : ¬(recordGapCenter + 465176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465176]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07940_not_prime : ¬(recordGapCenter + 465242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465242]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07941_not_prime : ¬(recordGapCenter + 465326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465326]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07942_not_prime : ¬(recordGapCenter + 465342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465342]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07943_not_prime : ¬(recordGapCenter + 465368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465368]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07944_not_prime : ¬(recordGapCenter + 465398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465398]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07945_not_prime : ¬(recordGapCenter + 465438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465438]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07946_not_prime : ¬(recordGapCenter + 465512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465512]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07947_not_prime : ¬(recordGapCenter + 465638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465638]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07948_not_prime : ¬(recordGapCenter + 465722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465722]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07949_not_prime : ¬(recordGapCenter + 465782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465782]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07950_not_prime : ¬(recordGapCenter + 465788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465788]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07951_not_prime : ¬(recordGapCenter + 465848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465848]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07952_not_prime : ¬(recordGapCenter + 465882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465882]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07953_not_prime : ¬(recordGapCenter + 465896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465896]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07954_not_prime : ¬(recordGapCenter + 466028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466028]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07955_not_prime : ¬(recordGapCenter + 466086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466086]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07956_not_prime : ¬(recordGapCenter + 466266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466266]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07957_not_prime : ¬(recordGapCenter + 466278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466278]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07958_not_prime : ¬(recordGapCenter + 466338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466338]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07959_not_prime : ¬(recordGapCenter + 466386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466386]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07960_not_prime : ¬(recordGapCenter + 466442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466442]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07961_not_prime : ¬(recordGapCenter + 466478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466478]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07962_not_prime : ¬(recordGapCenter + 466482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466482]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07963_not_prime : ¬(recordGapCenter + 466560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466560]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07964_not_prime : ¬(recordGapCenter + 466566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466566]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07965_not_prime : ¬(recordGapCenter + 466586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466586]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07966_not_prime : ¬(recordGapCenter + 466652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466652]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07967_not_prime : ¬(recordGapCenter + 466706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466706]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07968_not_prime : ¬(recordGapCenter + 466782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466782]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07969_not_prime : ¬(recordGapCenter + 466790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466790]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07970_not_prime : ¬(recordGapCenter + 467156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467156]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07971_not_prime : ¬(recordGapCenter + 467178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467178]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07972_not_prime : ¬(recordGapCenter + 467202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467202]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07973_not_prime : ¬(recordGapCenter + 467378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467378]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07974_not_prime : ¬(recordGapCenter + 467426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467426]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07975_not_prime : ¬(recordGapCenter + 467486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467486]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07976_not_prime : ¬(recordGapCenter + 467510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467510]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07977_not_prime : ¬(recordGapCenter + 467598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467598]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07978_not_prime : ¬(recordGapCenter + 467706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467706]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07979_not_prime : ¬(recordGapCenter + 467708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467708]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07980_not_prime : ¬(recordGapCenter + 467822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467822]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07981_not_prime : ¬(recordGapCenter + 467862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467862]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07982_not_prime : ¬(recordGapCenter + 467876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467876]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07983_not_prime : ¬(recordGapCenter + 467972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467972]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07984_not_prime : ¬(recordGapCenter + 468042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468042]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07985_not_prime : ¬(recordGapCenter + 468086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468086]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07986_not_prime : ¬(recordGapCenter + 468242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468242]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07987_not_prime : ¬(recordGapCenter + 468246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468246]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07988_not_prime : ¬(recordGapCenter + 468290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468290]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07989_not_prime : ¬(recordGapCenter + 468296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468296]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07990_not_prime : ¬(recordGapCenter + 468386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468386]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07991_not_prime : ¬(recordGapCenter + 468476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468476]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07992_not_prime : ¬(recordGapCenter + 468542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468542]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07993_not_prime : ¬(recordGapCenter + 468606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468606]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07994_not_prime : ¬(recordGapCenter + 468632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468632]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07995_not_prime : ¬(recordGapCenter + 468638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468638]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07996_not_prime : ¬(recordGapCenter + 468686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468686]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07997_not_prime : ¬(recordGapCenter + 468770).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468770]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07998_not_prime : ¬(recordGapCenter + 468822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468822]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm07999_not_prime : ¬(recordGapCenter + 468836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468836]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

theorem fullRecordGapTerm08000_not_prime : ¬(recordGapCenter + 468890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468890]
  · apply fullRecordGapRow00125_fermat
    simp [fullRecordGapRow00125_values]

end PrimeFactorUnimodality
