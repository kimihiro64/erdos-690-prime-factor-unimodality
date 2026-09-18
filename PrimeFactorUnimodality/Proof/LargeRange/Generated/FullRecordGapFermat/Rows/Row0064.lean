import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00064_values : List Nat :=
  [fullRecordGapCenterValue + 58320,
    fullRecordGapCenterValue + 60000,
    fullRecordGapCenterValue + 60750,
    fullRecordGapCenterValue + 61236,
    fullRecordGapCenterValue + 61250,
    fullRecordGapCenterValue + 61440,
    fullRecordGapCenterValue + 63000,
    fullRecordGapCenterValue + 64800,
    fullRecordGapCenterValue + 65856,
    fullRecordGapCenterValue + 67760,
    fullRecordGapCenterValue + 68600,
    fullRecordGapCenterValue + 69696,
    fullRecordGapCenterValue + 72000,
    fullRecordGapCenterValue + 72030,
    fullRecordGapCenterValue + 72600,
    fullRecordGapCenterValue + 73920,
    fullRecordGapCenterValue + 75000,
    fullRecordGapCenterValue + 76230,
    fullRecordGapCenterValue + 76800,
    fullRecordGapCenterValue + 76832,
    fullRecordGapCenterValue + 77000,
    fullRecordGapCenterValue + 77760,
    fullRecordGapCenterValue + 79200,
    fullRecordGapCenterValue + 80190,
    fullRecordGapCenterValue + 80850,
    fullRecordGapCenterValue + 83006,
    fullRecordGapCenterValue + 83160,
    fullRecordGapCenterValue + 84000,
    fullRecordGapCenterValue + 85536,
    fullRecordGapCenterValue + 86378,
    fullRecordGapCenterValue + 86402,
    fullRecordGapCenterValue + 86436,
    fullRecordGapCenterValue + 86822,
    fullRecordGapCenterValue + 87146,
    fullRecordGapCenterValue + 87318,
    fullRecordGapCenterValue + 87480,
    fullRecordGapCenterValue + 87500,
    fullRecordGapCenterValue + 87518,
    fullRecordGapCenterValue + 87566,
    fullRecordGapCenterValue + 87602,
    fullRecordGapCenterValue + 87782,
    fullRecordGapCenterValue + 87866,
    fullRecordGapCenterValue + 87938,
    fullRecordGapCenterValue + 88058,
    fullRecordGapCenterValue + 88082,
    fullRecordGapCenterValue + 88142,
    fullRecordGapCenterValue + 88200,
    fullRecordGapCenterValue + 88358,
    fullRecordGapCenterValue + 88406,
    fullRecordGapCenterValue + 88538,
    fullRecordGapCenterValue + 88742,
    fullRecordGapCenterValue + 89066,
    fullRecordGapCenterValue + 89282,
    fullRecordGapCenterValue + 89678,
    fullRecordGapCenterValue + 89918,
    fullRecordGapCenterValue + 89966,
    fullRecordGapCenterValue + 90638,
    fullRecordGapCenterValue + 90720,
    fullRecordGapCenterValue + 90722,
    fullRecordGapCenterValue + 91046,
    fullRecordGapCenterValue + 91082,
    fullRecordGapCenterValue + 91106,
    fullRecordGapCenterValue + 91476,
    fullRecordGapCenterValue + 91502]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00064_fermat : ∀ n ∈ fullRecordGapRow00064_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04033_not_prime : ¬(recordGapCenter + 58320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 58320]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04034_not_prime : ¬(recordGapCenter + 60000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 60000]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04035_not_prime : ¬(recordGapCenter + 60750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 60750]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04036_not_prime : ¬(recordGapCenter + 61236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 61236]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04037_not_prime : ¬(recordGapCenter + 61250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 61250]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04038_not_prime : ¬(recordGapCenter + 61440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 61440]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04039_not_prime : ¬(recordGapCenter + 63000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 63000]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04040_not_prime : ¬(recordGapCenter + 64800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 64800]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04041_not_prime : ¬(recordGapCenter + 65856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 65856]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04042_not_prime : ¬(recordGapCenter + 67760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 67760]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04043_not_prime : ¬(recordGapCenter + 68600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 68600]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04044_not_prime : ¬(recordGapCenter + 69696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 69696]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04045_not_prime : ¬(recordGapCenter + 72000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 72000]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04046_not_prime : ¬(recordGapCenter + 72030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 72030]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04047_not_prime : ¬(recordGapCenter + 72600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 72600]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04048_not_prime : ¬(recordGapCenter + 73920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 73920]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04049_not_prime : ¬(recordGapCenter + 75000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 75000]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04050_not_prime : ¬(recordGapCenter + 76230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 76230]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04051_not_prime : ¬(recordGapCenter + 76800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 76800]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04052_not_prime : ¬(recordGapCenter + 76832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 76832]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04053_not_prime : ¬(recordGapCenter + 77000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 77000]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04054_not_prime : ¬(recordGapCenter + 77760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 77760]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04055_not_prime : ¬(recordGapCenter + 79200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 79200]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04056_not_prime : ¬(recordGapCenter + 80190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 80190]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04057_not_prime : ¬(recordGapCenter + 80850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 80850]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04058_not_prime : ¬(recordGapCenter + 83006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 83006]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04059_not_prime : ¬(recordGapCenter + 83160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 83160]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04060_not_prime : ¬(recordGapCenter + 84000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 84000]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04061_not_prime : ¬(recordGapCenter + 85536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 85536]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04062_not_prime : ¬(recordGapCenter + 86378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 86378]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04063_not_prime : ¬(recordGapCenter + 86402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 86402]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04064_not_prime : ¬(recordGapCenter + 86436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 86436]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04065_not_prime : ¬(recordGapCenter + 86822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 86822]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04066_not_prime : ¬(recordGapCenter + 87146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87146]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04067_not_prime : ¬(recordGapCenter + 87318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87318]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04068_not_prime : ¬(recordGapCenter + 87480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87480]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04069_not_prime : ¬(recordGapCenter + 87500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87500]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04070_not_prime : ¬(recordGapCenter + 87518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87518]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04071_not_prime : ¬(recordGapCenter + 87566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87566]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04072_not_prime : ¬(recordGapCenter + 87602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87602]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04073_not_prime : ¬(recordGapCenter + 87782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87782]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04074_not_prime : ¬(recordGapCenter + 87866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87866]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04075_not_prime : ¬(recordGapCenter + 87938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87938]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04076_not_prime : ¬(recordGapCenter + 88058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88058]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04077_not_prime : ¬(recordGapCenter + 88082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88082]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04078_not_prime : ¬(recordGapCenter + 88142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88142]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04079_not_prime : ¬(recordGapCenter + 88200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88200]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04080_not_prime : ¬(recordGapCenter + 88358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88358]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04081_not_prime : ¬(recordGapCenter + 88406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88406]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04082_not_prime : ¬(recordGapCenter + 88538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88538]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04083_not_prime : ¬(recordGapCenter + 88742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88742]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04084_not_prime : ¬(recordGapCenter + 89066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89066]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04085_not_prime : ¬(recordGapCenter + 89282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89282]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04086_not_prime : ¬(recordGapCenter + 89678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89678]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04087_not_prime : ¬(recordGapCenter + 89918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89918]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04088_not_prime : ¬(recordGapCenter + 89966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89966]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04089_not_prime : ¬(recordGapCenter + 90638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 90638]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04090_not_prime : ¬(recordGapCenter + 90720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 90720]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04091_not_prime : ¬(recordGapCenter + 90722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 90722]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04092_not_prime : ¬(recordGapCenter + 91046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91046]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04093_not_prime : ¬(recordGapCenter + 91082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91082]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04094_not_prime : ¬(recordGapCenter + 91106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91106]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04095_not_prime : ¬(recordGapCenter + 91476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91476]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

theorem fullRecordGapTerm04096_not_prime : ¬(recordGapCenter + 91502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91502]
  · apply fullRecordGapRow00064_fermat
    simp [fullRecordGapRow00064_values]

end PrimeFactorUnimodality
