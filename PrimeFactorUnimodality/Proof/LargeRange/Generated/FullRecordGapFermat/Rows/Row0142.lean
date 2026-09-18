import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00142_values : List Nat :=
  [fullRecordGapCenterValue + 539702,
    fullRecordGapCenterValue + 539796,
    fullRecordGapCenterValue + 539862,
    fullRecordGapCenterValue + 539870,
    fullRecordGapCenterValue + 539906,
    fullRecordGapCenterValue + 539996,
    fullRecordGapCenterValue + 540002,
    fullRecordGapCenterValue + 540006,
    fullRecordGapCenterValue + 540066,
    fullRecordGapCenterValue + 540110,
    fullRecordGapCenterValue + 540138,
    fullRecordGapCenterValue + 540156,
    fullRecordGapCenterValue + 540242,
    fullRecordGapCenterValue + 540296,
    fullRecordGapCenterValue + 540356,
    fullRecordGapCenterValue + 540402,
    fullRecordGapCenterValue + 540446,
    fullRecordGapCenterValue + 540482,
    fullRecordGapCenterValue + 540636,
    fullRecordGapCenterValue + 540692,
    fullRecordGapCenterValue + 540732,
    fullRecordGapCenterValue + 540830,
    fullRecordGapCenterValue + 540902,
    fullRecordGapCenterValue + 540978,
    fullRecordGapCenterValue + 541010,
    fullRecordGapCenterValue + 541182,
    fullRecordGapCenterValue + 541238,
    fullRecordGapCenterValue + 541418,
    fullRecordGapCenterValue + 541572,
    fullRecordGapCenterValue + 541598,
    fullRecordGapCenterValue + 541668,
    fullRecordGapCenterValue + 541670,
    fullRecordGapCenterValue + 541682,
    fullRecordGapCenterValue + 541796,
    fullRecordGapCenterValue + 541826,
    fullRecordGapCenterValue + 541916,
    fullRecordGapCenterValue + 541928,
    fullRecordGapCenterValue + 542042,
    fullRecordGapCenterValue + 542132,
    fullRecordGapCenterValue + 542258,
    fullRecordGapCenterValue + 542292,
    fullRecordGapCenterValue + 542312,
    fullRecordGapCenterValue + 542372,
    fullRecordGapCenterValue + 542418,
    fullRecordGapCenterValue + 542442,
    fullRecordGapCenterValue + 542456,
    fullRecordGapCenterValue + 542468,
    fullRecordGapCenterValue + 542510,
    fullRecordGapCenterValue + 542522,
    fullRecordGapCenterValue + 542546,
    fullRecordGapCenterValue + 542558,
    fullRecordGapCenterValue + 542876,
    fullRecordGapCenterValue + 542936,
    fullRecordGapCenterValue + 542942,
    fullRecordGapCenterValue + 543138,
    fullRecordGapCenterValue + 543156,
    fullRecordGapCenterValue + 543386,
    fullRecordGapCenterValue + 543468,
    fullRecordGapCenterValue + 543498,
    fullRecordGapCenterValue + 543596,
    fullRecordGapCenterValue + 543702,
    fullRecordGapCenterValue + 543758,
    fullRecordGapCenterValue + 543806,
    fullRecordGapCenterValue + 543828]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00142_fermat : ∀ n ∈ fullRecordGapRow00142_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09025_not_prime : ¬(recordGapCenter + 539702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539702]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09026_not_prime : ¬(recordGapCenter + 539796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539796]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09027_not_prime : ¬(recordGapCenter + 539862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539862]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09028_not_prime : ¬(recordGapCenter + 539870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539870]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09029_not_prime : ¬(recordGapCenter + 539906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539906]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09030_not_prime : ¬(recordGapCenter + 539996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539996]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09031_not_prime : ¬(recordGapCenter + 540002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540002]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09032_not_prime : ¬(recordGapCenter + 540006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540006]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09033_not_prime : ¬(recordGapCenter + 540066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540066]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09034_not_prime : ¬(recordGapCenter + 540110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540110]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09035_not_prime : ¬(recordGapCenter + 540138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540138]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09036_not_prime : ¬(recordGapCenter + 540156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540156]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09037_not_prime : ¬(recordGapCenter + 540242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540242]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09038_not_prime : ¬(recordGapCenter + 540296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540296]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09039_not_prime : ¬(recordGapCenter + 540356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540356]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09040_not_prime : ¬(recordGapCenter + 540402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540402]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09041_not_prime : ¬(recordGapCenter + 540446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540446]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09042_not_prime : ¬(recordGapCenter + 540482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540482]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09043_not_prime : ¬(recordGapCenter + 540636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540636]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09044_not_prime : ¬(recordGapCenter + 540692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540692]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09045_not_prime : ¬(recordGapCenter + 540732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540732]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09046_not_prime : ¬(recordGapCenter + 540830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540830]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09047_not_prime : ¬(recordGapCenter + 540902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540902]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09048_not_prime : ¬(recordGapCenter + 540978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 540978]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09049_not_prime : ¬(recordGapCenter + 541010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541010]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09050_not_prime : ¬(recordGapCenter + 541182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541182]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09051_not_prime : ¬(recordGapCenter + 541238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541238]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09052_not_prime : ¬(recordGapCenter + 541418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541418]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09053_not_prime : ¬(recordGapCenter + 541572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541572]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09054_not_prime : ¬(recordGapCenter + 541598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541598]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09055_not_prime : ¬(recordGapCenter + 541668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541668]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09056_not_prime : ¬(recordGapCenter + 541670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541670]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09057_not_prime : ¬(recordGapCenter + 541682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541682]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09058_not_prime : ¬(recordGapCenter + 541796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541796]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09059_not_prime : ¬(recordGapCenter + 541826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541826]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09060_not_prime : ¬(recordGapCenter + 541916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541916]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09061_not_prime : ¬(recordGapCenter + 541928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 541928]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09062_not_prime : ¬(recordGapCenter + 542042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542042]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09063_not_prime : ¬(recordGapCenter + 542132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542132]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09064_not_prime : ¬(recordGapCenter + 542258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542258]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09065_not_prime : ¬(recordGapCenter + 542292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542292]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09066_not_prime : ¬(recordGapCenter + 542312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542312]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09067_not_prime : ¬(recordGapCenter + 542372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542372]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09068_not_prime : ¬(recordGapCenter + 542418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542418]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09069_not_prime : ¬(recordGapCenter + 542442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542442]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09070_not_prime : ¬(recordGapCenter + 542456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542456]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09071_not_prime : ¬(recordGapCenter + 542468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542468]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09072_not_prime : ¬(recordGapCenter + 542510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542510]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09073_not_prime : ¬(recordGapCenter + 542522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542522]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09074_not_prime : ¬(recordGapCenter + 542546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542546]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09075_not_prime : ¬(recordGapCenter + 542558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542558]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09076_not_prime : ¬(recordGapCenter + 542876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542876]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09077_not_prime : ¬(recordGapCenter + 542936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542936]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09078_not_prime : ¬(recordGapCenter + 542942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 542942]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09079_not_prime : ¬(recordGapCenter + 543138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543138]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09080_not_prime : ¬(recordGapCenter + 543156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543156]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09081_not_prime : ¬(recordGapCenter + 543386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543386]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09082_not_prime : ¬(recordGapCenter + 543468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543468]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09083_not_prime : ¬(recordGapCenter + 543498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543498]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09084_not_prime : ¬(recordGapCenter + 543596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543596]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09085_not_prime : ¬(recordGapCenter + 543702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543702]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09086_not_prime : ¬(recordGapCenter + 543758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543758]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09087_not_prime : ¬(recordGapCenter + 543806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543806]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

theorem fullRecordGapTerm09088_not_prime : ¬(recordGapCenter + 543828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543828]
  · apply fullRecordGapRow00142_fermat
    simp [fullRecordGapRow00142_values]

end PrimeFactorUnimodality
