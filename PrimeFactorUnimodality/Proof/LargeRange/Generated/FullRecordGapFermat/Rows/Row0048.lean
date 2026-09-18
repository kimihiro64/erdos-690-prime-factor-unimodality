import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00048_values : List Nat :=
  [fullRecordGapCenterValue - 181894,
    fullRecordGapCenterValue - 181822,
    fullRecordGapCenterValue - 181642,
    fullRecordGapCenterValue - 181444,
    fullRecordGapCenterValue - 181348,
    fullRecordGapCenterValue - 181318,
    fullRecordGapCenterValue - 181234,
    fullRecordGapCenterValue - 180988,
    fullRecordGapCenterValue - 180802,
    fullRecordGapCenterValue - 180724,
    fullRecordGapCenterValue - 180394,
    fullRecordGapCenterValue - 180178,
    fullRecordGapCenterValue - 180142,
    fullRecordGapCenterValue - 180022,
    fullRecordGapCenterValue - 179878,
    fullRecordGapCenterValue - 179818,
    fullRecordGapCenterValue - 179794,
    fullRecordGapCenterValue - 179734,
    fullRecordGapCenterValue - 179668,
    fullRecordGapCenterValue - 179638,
    fullRecordGapCenterValue - 179548,
    fullRecordGapCenterValue - 179200,
    fullRecordGapCenterValue - 179188,
    fullRecordGapCenterValue - 179092,
    fullRecordGapCenterValue - 179038,
    fullRecordGapCenterValue - 178954,
    fullRecordGapCenterValue - 178762,
    fullRecordGapCenterValue - 178588,
    fullRecordGapCenterValue - 178378,
    fullRecordGapCenterValue - 178252,
    fullRecordGapCenterValue - 178114,
    fullRecordGapCenterValue - 178042,
    fullRecordGapCenterValue - 177870,
    fullRecordGapCenterValue - 177634,
    fullRecordGapCenterValue - 177622,
    fullRecordGapCenterValue - 177532,
    fullRecordGapCenterValue - 177408,
    fullRecordGapCenterValue - 176854,
    fullRecordGapCenterValue - 176794,
    fullRecordGapCenterValue - 176418,
    fullRecordGapCenterValue - 176284,
    fullRecordGapCenterValue - 176074,
    fullRecordGapCenterValue - 175948,
    fullRecordGapCenterValue - 175822,
    fullRecordGapCenterValue - 175774,
    fullRecordGapCenterValue - 175738,
    fullRecordGapCenterValue - 175402,
    fullRecordGapCenterValue - 175114,
    fullRecordGapCenterValue - 175018,
    fullRecordGapCenterValue - 175000,
    fullRecordGapCenterValue - 174982,
    fullRecordGapCenterValue - 174604,
    fullRecordGapCenterValue - 174562,
    fullRecordGapCenterValue - 174514,
    fullRecordGapCenterValue - 174502,
    fullRecordGapCenterValue - 174358,
    fullRecordGapCenterValue - 174292,
    fullRecordGapCenterValue - 173962,
    fullRecordGapCenterValue - 173938,
    fullRecordGapCenterValue - 173854,
    fullRecordGapCenterValue - 173764,
    fullRecordGapCenterValue - 173722,
    fullRecordGapCenterValue - 173674,
    fullRecordGapCenterValue - 173284]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00048_fermat : ∀ n ∈ fullRecordGapRow00048_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03009_not_prime : ¬(recordGapCenter - 181894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181894]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03010_not_prime : ¬(recordGapCenter - 181822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181822]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03011_not_prime : ¬(recordGapCenter - 181642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181642]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03012_not_prime : ¬(recordGapCenter - 181444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181444]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03013_not_prime : ¬(recordGapCenter - 181348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181348]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03014_not_prime : ¬(recordGapCenter - 181318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181318]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03015_not_prime : ¬(recordGapCenter - 181234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181234]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03016_not_prime : ¬(recordGapCenter - 180988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180988]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03017_not_prime : ¬(recordGapCenter - 180802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180802]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03018_not_prime : ¬(recordGapCenter - 180724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180724]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03019_not_prime : ¬(recordGapCenter - 180394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180394]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03020_not_prime : ¬(recordGapCenter - 180178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180178]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03021_not_prime : ¬(recordGapCenter - 180142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180142]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03022_not_prime : ¬(recordGapCenter - 180022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180022]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03023_not_prime : ¬(recordGapCenter - 179878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179878]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03024_not_prime : ¬(recordGapCenter - 179818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179818]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03025_not_prime : ¬(recordGapCenter - 179794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179794]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03026_not_prime : ¬(recordGapCenter - 179734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179734]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03027_not_prime : ¬(recordGapCenter - 179668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179668]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03028_not_prime : ¬(recordGapCenter - 179638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179638]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03029_not_prime : ¬(recordGapCenter - 179548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179548]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03030_not_prime : ¬(recordGapCenter - 179200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179200]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03031_not_prime : ¬(recordGapCenter - 179188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179188]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03032_not_prime : ¬(recordGapCenter - 179092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179092]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03033_not_prime : ¬(recordGapCenter - 179038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179038]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03034_not_prime : ¬(recordGapCenter - 178954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178954]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03035_not_prime : ¬(recordGapCenter - 178762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178762]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03036_not_prime : ¬(recordGapCenter - 178588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178588]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03037_not_prime : ¬(recordGapCenter - 178378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178378]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03038_not_prime : ¬(recordGapCenter - 178252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178252]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03039_not_prime : ¬(recordGapCenter - 178114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178114]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03040_not_prime : ¬(recordGapCenter - 178042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178042]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03041_not_prime : ¬(recordGapCenter - 177870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177870]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03042_not_prime : ¬(recordGapCenter - 177634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177634]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03043_not_prime : ¬(recordGapCenter - 177622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177622]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03044_not_prime : ¬(recordGapCenter - 177532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177532]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03045_not_prime : ¬(recordGapCenter - 177408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177408]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03046_not_prime : ¬(recordGapCenter - 176854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176854]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03047_not_prime : ¬(recordGapCenter - 176794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176794]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03048_not_prime : ¬(recordGapCenter - 176418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176418]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03049_not_prime : ¬(recordGapCenter - 176284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176284]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03050_not_prime : ¬(recordGapCenter - 176074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176074]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03051_not_prime : ¬(recordGapCenter - 175948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175948]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03052_not_prime : ¬(recordGapCenter - 175822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175822]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03053_not_prime : ¬(recordGapCenter - 175774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175774]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03054_not_prime : ¬(recordGapCenter - 175738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175738]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03055_not_prime : ¬(recordGapCenter - 175402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175402]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03056_not_prime : ¬(recordGapCenter - 175114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175114]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03057_not_prime : ¬(recordGapCenter - 175018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175018]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03058_not_prime : ¬(recordGapCenter - 175000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175000]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03059_not_prime : ¬(recordGapCenter - 174982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174982]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03060_not_prime : ¬(recordGapCenter - 174604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174604]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03061_not_prime : ¬(recordGapCenter - 174562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174562]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03062_not_prime : ¬(recordGapCenter - 174514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174514]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03063_not_prime : ¬(recordGapCenter - 174502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174502]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03064_not_prime : ¬(recordGapCenter - 174358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174358]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03065_not_prime : ¬(recordGapCenter - 174292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174292]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03066_not_prime : ¬(recordGapCenter - 173962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173962]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03067_not_prime : ¬(recordGapCenter - 173938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173938]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03068_not_prime : ¬(recordGapCenter - 173854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173854]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03069_not_prime : ¬(recordGapCenter - 173764).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173764]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03070_not_prime : ¬(recordGapCenter - 173722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173722]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03071_not_prime : ¬(recordGapCenter - 173674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173674]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

theorem fullRecordGapTerm03072_not_prime : ¬(recordGapCenter - 173284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173284]
  · apply fullRecordGapRow00048_fermat
    simp [fullRecordGapRow00048_values]

end PrimeFactorUnimodality
