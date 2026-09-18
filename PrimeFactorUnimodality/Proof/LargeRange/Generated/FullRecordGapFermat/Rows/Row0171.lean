import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00171_values : List Nat :=
  [fullRecordGapCenterValue + 655436,
    fullRecordGapCenterValue + 655466,
    fullRecordGapCenterValue + 655476,
    fullRecordGapCenterValue + 655478,
    fullRecordGapCenterValue + 655496,
    fullRecordGapCenterValue + 655548,
    fullRecordGapCenterValue + 655572,
    fullRecordGapCenterValue + 655602,
    fullRecordGapCenterValue + 655736,
    fullRecordGapCenterValue + 655778,
    fullRecordGapCenterValue + 655782,
    fullRecordGapCenterValue + 655958,
    fullRecordGapCenterValue + 655986,
    fullRecordGapCenterValue + 655988,
    fullRecordGapCenterValue + 656072,
    fullRecordGapCenterValue + 656142,
    fullRecordGapCenterValue + 656148,
    fullRecordGapCenterValue + 656202,
    fullRecordGapCenterValue + 656342,
    fullRecordGapCenterValue + 656346,
    fullRecordGapCenterValue + 656372,
    fullRecordGapCenterValue + 656510,
    fullRecordGapCenterValue + 656556,
    fullRecordGapCenterValue + 656570,
    fullRecordGapCenterValue + 656598,
    fullRecordGapCenterValue + 656666,
    fullRecordGapCenterValue + 656706,
    fullRecordGapCenterValue + 656870,
    fullRecordGapCenterValue + 656990,
    fullRecordGapCenterValue + 657062,
    fullRecordGapCenterValue + 657086,
    fullRecordGapCenterValue + 657102,
    fullRecordGapCenterValue + 657116,
    fullRecordGapCenterValue + 657170,
    fullRecordGapCenterValue + 657242,
    fullRecordGapCenterValue + 657276,
    fullRecordGapCenterValue + 657282,
    fullRecordGapCenterValue + 657398]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00171_fermat : ∀ n ∈ fullRecordGapRow00171_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10881_not_prime : ¬(recordGapCenter + 655436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655436]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10882_not_prime : ¬(recordGapCenter + 655466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655466]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10883_not_prime : ¬(recordGapCenter + 655476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655476]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10884_not_prime : ¬(recordGapCenter + 655478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655478]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10885_not_prime : ¬(recordGapCenter + 655496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655496]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10886_not_prime : ¬(recordGapCenter + 655548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655548]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10887_not_prime : ¬(recordGapCenter + 655572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655572]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10888_not_prime : ¬(recordGapCenter + 655602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655602]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10889_not_prime : ¬(recordGapCenter + 655736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655736]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10890_not_prime : ¬(recordGapCenter + 655778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655778]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10891_not_prime : ¬(recordGapCenter + 655782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655782]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10892_not_prime : ¬(recordGapCenter + 655958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655958]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10893_not_prime : ¬(recordGapCenter + 655986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655986]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10894_not_prime : ¬(recordGapCenter + 655988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655988]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10895_not_prime : ¬(recordGapCenter + 656072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656072]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10896_not_prime : ¬(recordGapCenter + 656142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656142]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10897_not_prime : ¬(recordGapCenter + 656148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656148]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10898_not_prime : ¬(recordGapCenter + 656202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656202]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10899_not_prime : ¬(recordGapCenter + 656342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656342]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10900_not_prime : ¬(recordGapCenter + 656346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656346]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10901_not_prime : ¬(recordGapCenter + 656372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656372]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10902_not_prime : ¬(recordGapCenter + 656510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656510]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10903_not_prime : ¬(recordGapCenter + 656556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656556]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10904_not_prime : ¬(recordGapCenter + 656570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656570]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10905_not_prime : ¬(recordGapCenter + 656598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656598]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10906_not_prime : ¬(recordGapCenter + 656666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656666]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10907_not_prime : ¬(recordGapCenter + 656706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656706]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10908_not_prime : ¬(recordGapCenter + 656870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656870]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10909_not_prime : ¬(recordGapCenter + 656990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 656990]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10910_not_prime : ¬(recordGapCenter + 657062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657062]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10911_not_prime : ¬(recordGapCenter + 657086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657086]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10912_not_prime : ¬(recordGapCenter + 657102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657102]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10913_not_prime : ¬(recordGapCenter + 657116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657116]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10914_not_prime : ¬(recordGapCenter + 657170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657170]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10915_not_prime : ¬(recordGapCenter + 657242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657242]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10916_not_prime : ¬(recordGapCenter + 657276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657276]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10917_not_prime : ¬(recordGapCenter + 657282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657282]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

theorem fullRecordGapTerm10918_not_prime : ¬(recordGapCenter + 657398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 657398]
  · apply fullRecordGapRow00171_fermat
    simp [fullRecordGapRow00171_values]

end PrimeFactorUnimodality
