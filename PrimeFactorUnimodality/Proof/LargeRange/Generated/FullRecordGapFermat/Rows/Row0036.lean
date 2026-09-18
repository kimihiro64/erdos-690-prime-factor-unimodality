import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00036_values : List Nat :=
  [fullRecordGapCenterValue - 271438,
    fullRecordGapCenterValue - 271294,
    fullRecordGapCenterValue - 271204,
    fullRecordGapCenterValue - 271162,
    fullRecordGapCenterValue - 270958,
    fullRecordGapCenterValue - 270898,
    fullRecordGapCenterValue - 270862,
    fullRecordGapCenterValue - 270834,
    fullRecordGapCenterValue - 270822,
    fullRecordGapCenterValue - 270694,
    fullRecordGapCenterValue - 270562,
    fullRecordGapCenterValue - 270462,
    fullRecordGapCenterValue - 270268,
    fullRecordGapCenterValue - 270262,
    fullRecordGapCenterValue - 270238,
    fullRecordGapCenterValue - 270118,
    fullRecordGapCenterValue - 270078,
    fullRecordGapCenterValue - 269842,
    fullRecordGapCenterValue - 269734,
    fullRecordGapCenterValue - 269562,
    fullRecordGapCenterValue - 269554,
    fullRecordGapCenterValue - 269398,
    fullRecordGapCenterValue - 269362,
    fullRecordGapCenterValue - 269358,
    fullRecordGapCenterValue - 269322,
    fullRecordGapCenterValue - 269092,
    fullRecordGapCenterValue - 269058,
    fullRecordGapCenterValue - 269044,
    fullRecordGapCenterValue - 268678,
    fullRecordGapCenterValue - 268638,
    fullRecordGapCenterValue - 268564,
    fullRecordGapCenterValue - 268098,
    fullRecordGapCenterValue - 268084,
    fullRecordGapCenterValue - 268012,
    fullRecordGapCenterValue - 267958,
    fullRecordGapCenterValue - 267892,
    fullRecordGapCenterValue - 267538,
    fullRecordGapCenterValue - 267522,
    fullRecordGapCenterValue - 267474,
    fullRecordGapCenterValue - 267378,
    fullRecordGapCenterValue - 267118,
    fullRecordGapCenterValue - 266998,
    fullRecordGapCenterValue - 266902,
    fullRecordGapCenterValue - 266878,
    fullRecordGapCenterValue - 266782,
    fullRecordGapCenterValue - 266758,
    fullRecordGapCenterValue - 266698,
    fullRecordGapCenterValue - 266404,
    fullRecordGapCenterValue - 266338,
    fullRecordGapCenterValue - 266298,
    fullRecordGapCenterValue - 266242,
    fullRecordGapCenterValue - 266112,
    fullRecordGapCenterValue - 265942,
    fullRecordGapCenterValue - 265858,
    fullRecordGapCenterValue - 265828,
    fullRecordGapCenterValue - 265822,
    fullRecordGapCenterValue - 265758,
    fullRecordGapCenterValue - 265674,
    fullRecordGapCenterValue - 265614,
    fullRecordGapCenterValue - 265612,
    fullRecordGapCenterValue - 265578,
    fullRecordGapCenterValue - 265498,
    fullRecordGapCenterValue - 265372,
    fullRecordGapCenterValue - 265348]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00036_fermat : ∀ n ∈ fullRecordGapRow00036_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02241_not_prime : ¬(recordGapCenter - 271438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271438]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02242_not_prime : ¬(recordGapCenter - 271294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271294]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02243_not_prime : ¬(recordGapCenter - 271204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271204]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02244_not_prime : ¬(recordGapCenter - 271162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271162]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02245_not_prime : ¬(recordGapCenter - 270958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270958]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02246_not_prime : ¬(recordGapCenter - 270898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270898]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02247_not_prime : ¬(recordGapCenter - 270862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270862]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02248_not_prime : ¬(recordGapCenter - 270834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270834]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02249_not_prime : ¬(recordGapCenter - 270822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270822]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02250_not_prime : ¬(recordGapCenter - 270694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270694]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02251_not_prime : ¬(recordGapCenter - 270562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270562]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02252_not_prime : ¬(recordGapCenter - 270462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270462]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02253_not_prime : ¬(recordGapCenter - 270268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270268]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02254_not_prime : ¬(recordGapCenter - 270262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270262]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02255_not_prime : ¬(recordGapCenter - 270238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270238]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02256_not_prime : ¬(recordGapCenter - 270118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270118]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02257_not_prime : ¬(recordGapCenter - 270078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270078]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02258_not_prime : ¬(recordGapCenter - 269842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269842]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02259_not_prime : ¬(recordGapCenter - 269734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269734]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02260_not_prime : ¬(recordGapCenter - 269562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269562]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02261_not_prime : ¬(recordGapCenter - 269554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269554]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02262_not_prime : ¬(recordGapCenter - 269398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269398]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02263_not_prime : ¬(recordGapCenter - 269362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269362]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02264_not_prime : ¬(recordGapCenter - 269358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269358]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02265_not_prime : ¬(recordGapCenter - 269322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269322]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02266_not_prime : ¬(recordGapCenter - 269092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269092]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02267_not_prime : ¬(recordGapCenter - 269058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269058]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02268_not_prime : ¬(recordGapCenter - 269044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269044]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02269_not_prime : ¬(recordGapCenter - 268678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268678]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02270_not_prime : ¬(recordGapCenter - 268638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268638]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02271_not_prime : ¬(recordGapCenter - 268564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268564]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02272_not_prime : ¬(recordGapCenter - 268098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268098]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02273_not_prime : ¬(recordGapCenter - 268084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268084]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02274_not_prime : ¬(recordGapCenter - 268012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268012]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02275_not_prime : ¬(recordGapCenter - 267958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267958]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02276_not_prime : ¬(recordGapCenter - 267892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267892]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02277_not_prime : ¬(recordGapCenter - 267538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267538]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02278_not_prime : ¬(recordGapCenter - 267522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267522]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02279_not_prime : ¬(recordGapCenter - 267474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267474]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02280_not_prime : ¬(recordGapCenter - 267378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267378]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02281_not_prime : ¬(recordGapCenter - 267118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267118]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02282_not_prime : ¬(recordGapCenter - 266998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266998]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02283_not_prime : ¬(recordGapCenter - 266902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266902]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02284_not_prime : ¬(recordGapCenter - 266878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266878]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02285_not_prime : ¬(recordGapCenter - 266782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266782]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02286_not_prime : ¬(recordGapCenter - 266758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266758]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02287_not_prime : ¬(recordGapCenter - 266698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266698]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02288_not_prime : ¬(recordGapCenter - 266404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266404]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02289_not_prime : ¬(recordGapCenter - 266338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266338]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02290_not_prime : ¬(recordGapCenter - 266298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266298]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02291_not_prime : ¬(recordGapCenter - 266242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266242]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02292_not_prime : ¬(recordGapCenter - 266112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266112]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02293_not_prime : ¬(recordGapCenter - 265942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265942]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02294_not_prime : ¬(recordGapCenter - 265858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265858]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02295_not_prime : ¬(recordGapCenter - 265828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265828]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02296_not_prime : ¬(recordGapCenter - 265822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265822]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02297_not_prime : ¬(recordGapCenter - 265758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265758]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02298_not_prime : ¬(recordGapCenter - 265674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265674]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02299_not_prime : ¬(recordGapCenter - 265614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265614]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02300_not_prime : ¬(recordGapCenter - 265612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265612]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02301_not_prime : ¬(recordGapCenter - 265578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265578]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02302_not_prime : ¬(recordGapCenter - 265498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265498]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02303_not_prime : ¬(recordGapCenter - 265372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265372]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

theorem fullRecordGapTerm02304_not_prime : ¬(recordGapCenter - 265348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265348]
  · apply fullRecordGapRow00036_fermat
    simp [fullRecordGapRow00036_values]

end PrimeFactorUnimodality
