import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00161_values : List Nat :=
  [fullRecordGapCenterValue + 617172,
    fullRecordGapCenterValue + 617246,
    fullRecordGapCenterValue + 617400,
    fullRecordGapCenterValue + 617402,
    fullRecordGapCenterValue + 617510,
    fullRecordGapCenterValue + 617522,
    fullRecordGapCenterValue + 617570,
    fullRecordGapCenterValue + 617618,
    fullRecordGapCenterValue + 617636,
    fullRecordGapCenterValue + 617666,
    fullRecordGapCenterValue + 617676,
    fullRecordGapCenterValue + 617718,
    fullRecordGapCenterValue + 617772,
    fullRecordGapCenterValue + 617858,
    fullRecordGapCenterValue + 617898,
    fullRecordGapCenterValue + 617972,
    fullRecordGapCenterValue + 617978,
    fullRecordGapCenterValue + 618038,
    fullRecordGapCenterValue + 618158,
    fullRecordGapCenterValue + 618182,
    fullRecordGapCenterValue + 618258,
    fullRecordGapCenterValue + 618356,
    fullRecordGapCenterValue + 618468,
    fullRecordGapCenterValue + 618506,
    fullRecordGapCenterValue + 618558,
    fullRecordGapCenterValue + 618572,
    fullRecordGapCenterValue + 618626,
    fullRecordGapCenterValue + 618668,
    fullRecordGapCenterValue + 618738,
    fullRecordGapCenterValue + 618756,
    fullRecordGapCenterValue + 618776,
    fullRecordGapCenterValue + 618846,
    fullRecordGapCenterValue + 618866,
    fullRecordGapCenterValue + 618872,
    fullRecordGapCenterValue + 618938,
    fullRecordGapCenterValue + 619046,
    fullRecordGapCenterValue + 619116,
    fullRecordGapCenterValue + 619118,
    fullRecordGapCenterValue + 619148,
    fullRecordGapCenterValue + 619196,
    fullRecordGapCenterValue + 619356,
    fullRecordGapCenterValue + 619448,
    fullRecordGapCenterValue + 619490,
    fullRecordGapCenterValue + 619532,
    fullRecordGapCenterValue + 619598,
    fullRecordGapCenterValue + 619610,
    fullRecordGapCenterValue + 619790,
    fullRecordGapCenterValue + 619862,
    fullRecordGapCenterValue + 620012,
    fullRecordGapCenterValue + 620036,
    fullRecordGapCenterValue + 620102,
    fullRecordGapCenterValue + 620142,
    fullRecordGapCenterValue + 620148,
    fullRecordGapCenterValue + 620216,
    fullRecordGapCenterValue + 620322,
    fullRecordGapCenterValue + 620348,
    fullRecordGapCenterValue + 620390,
    fullRecordGapCenterValue + 620408,
    fullRecordGapCenterValue + 620456,
    fullRecordGapCenterValue + 620538,
    fullRecordGapCenterValue + 620628,
    fullRecordGapCenterValue + 620742,
    fullRecordGapCenterValue + 620810,
    fullRecordGapCenterValue + 620898]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00161_fermat : ∀ n ∈ fullRecordGapRow00161_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10241_not_prime : ¬(recordGapCenter + 617172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617172]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10242_not_prime : ¬(recordGapCenter + 617246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617246]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10243_not_prime : ¬(recordGapCenter + 617400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617400]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10244_not_prime : ¬(recordGapCenter + 617402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617402]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10245_not_prime : ¬(recordGapCenter + 617510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617510]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10246_not_prime : ¬(recordGapCenter + 617522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617522]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10247_not_prime : ¬(recordGapCenter + 617570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617570]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10248_not_prime : ¬(recordGapCenter + 617618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617618]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10249_not_prime : ¬(recordGapCenter + 617636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617636]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10250_not_prime : ¬(recordGapCenter + 617666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617666]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10251_not_prime : ¬(recordGapCenter + 617676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617676]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10252_not_prime : ¬(recordGapCenter + 617718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617718]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10253_not_prime : ¬(recordGapCenter + 617772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617772]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10254_not_prime : ¬(recordGapCenter + 617858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617858]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10255_not_prime : ¬(recordGapCenter + 617898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617898]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10256_not_prime : ¬(recordGapCenter + 617972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617972]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10257_not_prime : ¬(recordGapCenter + 617978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617978]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10258_not_prime : ¬(recordGapCenter + 618038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618038]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10259_not_prime : ¬(recordGapCenter + 618158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618158]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10260_not_prime : ¬(recordGapCenter + 618182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618182]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10261_not_prime : ¬(recordGapCenter + 618258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618258]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10262_not_prime : ¬(recordGapCenter + 618356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618356]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10263_not_prime : ¬(recordGapCenter + 618468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618468]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10264_not_prime : ¬(recordGapCenter + 618506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618506]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10265_not_prime : ¬(recordGapCenter + 618558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618558]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10266_not_prime : ¬(recordGapCenter + 618572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618572]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10267_not_prime : ¬(recordGapCenter + 618626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618626]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10268_not_prime : ¬(recordGapCenter + 618668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618668]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10269_not_prime : ¬(recordGapCenter + 618738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618738]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10270_not_prime : ¬(recordGapCenter + 618756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618756]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10271_not_prime : ¬(recordGapCenter + 618776).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618776]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10272_not_prime : ¬(recordGapCenter + 618846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618846]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10273_not_prime : ¬(recordGapCenter + 618866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618866]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10274_not_prime : ¬(recordGapCenter + 618872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618872]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10275_not_prime : ¬(recordGapCenter + 618938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 618938]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10276_not_prime : ¬(recordGapCenter + 619046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619046]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10277_not_prime : ¬(recordGapCenter + 619116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619116]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10278_not_prime : ¬(recordGapCenter + 619118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619118]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10279_not_prime : ¬(recordGapCenter + 619148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619148]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10280_not_prime : ¬(recordGapCenter + 619196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619196]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10281_not_prime : ¬(recordGapCenter + 619356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619356]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10282_not_prime : ¬(recordGapCenter + 619448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619448]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10283_not_prime : ¬(recordGapCenter + 619490).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619490]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10284_not_prime : ¬(recordGapCenter + 619532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619532]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10285_not_prime : ¬(recordGapCenter + 619598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619598]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10286_not_prime : ¬(recordGapCenter + 619610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619610]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10287_not_prime : ¬(recordGapCenter + 619790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619790]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10288_not_prime : ¬(recordGapCenter + 619862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 619862]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10289_not_prime : ¬(recordGapCenter + 620012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620012]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10290_not_prime : ¬(recordGapCenter + 620036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620036]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10291_not_prime : ¬(recordGapCenter + 620102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620102]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10292_not_prime : ¬(recordGapCenter + 620142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620142]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10293_not_prime : ¬(recordGapCenter + 620148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620148]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10294_not_prime : ¬(recordGapCenter + 620216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620216]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10295_not_prime : ¬(recordGapCenter + 620322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620322]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10296_not_prime : ¬(recordGapCenter + 620348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620348]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10297_not_prime : ¬(recordGapCenter + 620390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620390]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10298_not_prime : ¬(recordGapCenter + 620408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620408]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10299_not_prime : ¬(recordGapCenter + 620456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620456]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10300_not_prime : ¬(recordGapCenter + 620538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620538]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10301_not_prime : ¬(recordGapCenter + 620628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620628]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10302_not_prime : ¬(recordGapCenter + 620742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620742]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10303_not_prime : ¬(recordGapCenter + 620810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620810]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

theorem fullRecordGapTerm10304_not_prime : ¬(recordGapCenter + 620898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620898]
  · apply fullRecordGapRow00161_fermat
    simp [fullRecordGapRow00161_values]

end PrimeFactorUnimodality
