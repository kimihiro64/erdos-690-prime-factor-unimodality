import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00003_values : List Nat :=
  [fullRecordGapCenterValue - 444838,
    fullRecordGapCenterValue - 444658,
    fullRecordGapCenterValue - 444622,
    fullRecordGapCenterValue - 444594,
    fullRecordGapCenterValue - 444538,
    fullRecordGapCenterValue - 444484,
    fullRecordGapCenterValue - 444364,
    fullRecordGapCenterValue - 444322,
    fullRecordGapCenterValue - 444282,
    fullRecordGapCenterValue - 444232,
    fullRecordGapCenterValue - 444124,
    fullRecordGapCenterValue - 443974,
    fullRecordGapCenterValue - 443914,
    fullRecordGapCenterValue - 443838,
    fullRecordGapCenterValue - 443830,
    fullRecordGapCenterValue - 443782,
    fullRecordGapCenterValue - 443658,
    fullRecordGapCenterValue - 443614,
    fullRecordGapCenterValue - 443512,
    fullRecordGapCenterValue - 443494,
    fullRecordGapCenterValue - 443442,
    fullRecordGapCenterValue - 443298,
    fullRecordGapCenterValue - 443284,
    fullRecordGapCenterValue - 443202,
    fullRecordGapCenterValue - 443134,
    fullRecordGapCenterValue - 443098,
    fullRecordGapCenterValue - 442984,
    fullRecordGapCenterValue - 442978,
    fullRecordGapCenterValue - 442938,
    fullRecordGapCenterValue - 442924,
    fullRecordGapCenterValue - 442914,
    fullRecordGapCenterValue - 442588,
    fullRecordGapCenterValue - 442564,
    fullRecordGapCenterValue - 442542,
    fullRecordGapCenterValue - 442438,
    fullRecordGapCenterValue - 442368,
    fullRecordGapCenterValue - 442362,
    fullRecordGapCenterValue - 442210,
    fullRecordGapCenterValue - 442132,
    fullRecordGapCenterValue - 442074,
    fullRecordGapCenterValue - 442042,
    fullRecordGapCenterValue - 441814,
    fullRecordGapCenterValue - 441802,
    fullRecordGapCenterValue - 441682,
    fullRecordGapCenterValue - 441622,
    fullRecordGapCenterValue - 441318,
    fullRecordGapCenterValue - 441310,
    fullRecordGapCenterValue - 441304,
    fullRecordGapCenterValue - 441292,
    fullRecordGapCenterValue - 441178,
    fullRecordGapCenterValue - 441138,
    fullRecordGapCenterValue - 441010,
    fullRecordGapCenterValue - 440872,
    fullRecordGapCenterValue - 440824,
    fullRecordGapCenterValue - 440782,
    fullRecordGapCenterValue - 440718,
    fullRecordGapCenterValue - 440614,
    fullRecordGapCenterValue - 440584,
    fullRecordGapCenterValue - 440502,
    fullRecordGapCenterValue - 440338,
    fullRecordGapCenterValue - 440332,
    fullRecordGapCenterValue - 440178,
    fullRecordGapCenterValue - 440170,
    fullRecordGapCenterValue - 440038]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00003_fermat : ∀ n ∈ fullRecordGapRow00003_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00129_not_prime : ¬(recordGapCenter - 444838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444838]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00130_not_prime : ¬(recordGapCenter - 444658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444658]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00131_not_prime : ¬(recordGapCenter - 444622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444622]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00132_not_prime : ¬(recordGapCenter - 444594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444594]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00133_not_prime : ¬(recordGapCenter - 444538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444538]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00134_not_prime : ¬(recordGapCenter - 444484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444484]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00135_not_prime : ¬(recordGapCenter - 444364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444364]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00136_not_prime : ¬(recordGapCenter - 444322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444322]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00137_not_prime : ¬(recordGapCenter - 444282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444282]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00138_not_prime : ¬(recordGapCenter - 444232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444232]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00139_not_prime : ¬(recordGapCenter - 444124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444124]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00140_not_prime : ¬(recordGapCenter - 443974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443974]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00141_not_prime : ¬(recordGapCenter - 443914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443914]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00142_not_prime : ¬(recordGapCenter - 443838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443838]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00143_not_prime : ¬(recordGapCenter - 443830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443830]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00144_not_prime : ¬(recordGapCenter - 443782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443782]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00145_not_prime : ¬(recordGapCenter - 443658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443658]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00146_not_prime : ¬(recordGapCenter - 443614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443614]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00147_not_prime : ¬(recordGapCenter - 443512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443512]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00148_not_prime : ¬(recordGapCenter - 443494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443494]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00149_not_prime : ¬(recordGapCenter - 443442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443442]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00150_not_prime : ¬(recordGapCenter - 443298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443298]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00151_not_prime : ¬(recordGapCenter - 443284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443284]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00152_not_prime : ¬(recordGapCenter - 443202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443202]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00153_not_prime : ¬(recordGapCenter - 443134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443134]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00154_not_prime : ¬(recordGapCenter - 443098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 443098]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00155_not_prime : ¬(recordGapCenter - 442984).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442984]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00156_not_prime : ¬(recordGapCenter - 442978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442978]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00157_not_prime : ¬(recordGapCenter - 442938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442938]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00158_not_prime : ¬(recordGapCenter - 442924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442924]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00159_not_prime : ¬(recordGapCenter - 442914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442914]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00160_not_prime : ¬(recordGapCenter - 442588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442588]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00161_not_prime : ¬(recordGapCenter - 442564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442564]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00162_not_prime : ¬(recordGapCenter - 442542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442542]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00163_not_prime : ¬(recordGapCenter - 442438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442438]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00164_not_prime : ¬(recordGapCenter - 442368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442368]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00165_not_prime : ¬(recordGapCenter - 442362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442362]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00166_not_prime : ¬(recordGapCenter - 442210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442210]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00167_not_prime : ¬(recordGapCenter - 442132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442132]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00168_not_prime : ¬(recordGapCenter - 442074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442074]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00169_not_prime : ¬(recordGapCenter - 442042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 442042]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00170_not_prime : ¬(recordGapCenter - 441814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441814]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00171_not_prime : ¬(recordGapCenter - 441802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441802]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00172_not_prime : ¬(recordGapCenter - 441682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441682]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00173_not_prime : ¬(recordGapCenter - 441622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441622]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00174_not_prime : ¬(recordGapCenter - 441318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441318]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00175_not_prime : ¬(recordGapCenter - 441310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441310]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00176_not_prime : ¬(recordGapCenter - 441304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441304]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00177_not_prime : ¬(recordGapCenter - 441292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441292]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00178_not_prime : ¬(recordGapCenter - 441178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441178]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00179_not_prime : ¬(recordGapCenter - 441138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441138]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00180_not_prime : ¬(recordGapCenter - 441010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 441010]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00181_not_prime : ¬(recordGapCenter - 440872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440872]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00182_not_prime : ¬(recordGapCenter - 440824).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440824]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00183_not_prime : ¬(recordGapCenter - 440782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440782]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00184_not_prime : ¬(recordGapCenter - 440718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440718]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00185_not_prime : ¬(recordGapCenter - 440614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440614]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00186_not_prime : ¬(recordGapCenter - 440584).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440584]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00187_not_prime : ¬(recordGapCenter - 440502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440502]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00188_not_prime : ¬(recordGapCenter - 440338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440338]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00189_not_prime : ¬(recordGapCenter - 440332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440332]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00190_not_prime : ¬(recordGapCenter - 440178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440178]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00191_not_prime : ¬(recordGapCenter - 440170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440170]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00192_not_prime : ¬(recordGapCenter - 440038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 440038]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

end PrimeFactorUnimodality
