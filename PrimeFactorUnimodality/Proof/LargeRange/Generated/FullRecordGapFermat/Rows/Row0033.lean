import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00033_values : List Nat :=
  [fullRecordGapCenterValue - 288994,
    fullRecordGapCenterValue - 288892,
    fullRecordGapCenterValue - 288844,
    fullRecordGapCenterValue - 288682,
    fullRecordGapCenterValue - 288474,
    fullRecordGapCenterValue - 288322,
    fullRecordGapCenterValue - 288294,
    fullRecordGapCenterValue - 288174,
    fullRecordGapCenterValue - 288172,
    fullRecordGapCenterValue - 288124,
    fullRecordGapCenterValue - 288120,
    fullRecordGapCenterValue - 288000,
    fullRecordGapCenterValue - 287884,
    fullRecordGapCenterValue - 287662,
    fullRecordGapCenterValue - 287634,
    fullRecordGapCenterValue - 287548,
    fullRecordGapCenterValue - 287502,
    fullRecordGapCenterValue - 287458,
    fullRecordGapCenterValue - 287418,
    fullRecordGapCenterValue - 287284,
    fullRecordGapCenterValue - 286978,
    fullRecordGapCenterValue - 286954,
    fullRecordGapCenterValue - 286828,
    fullRecordGapCenterValue - 286720,
    fullRecordGapCenterValue - 286684,
    fullRecordGapCenterValue - 286674,
    fullRecordGapCenterValue - 286662,
    fullRecordGapCenterValue - 286372,
    fullRecordGapCenterValue - 286302,
    fullRecordGapCenterValue - 286282,
    fullRecordGapCenterValue - 286204,
    fullRecordGapCenterValue - 286108,
    fullRecordGapCenterValue - 285954,
    fullRecordGapCenterValue - 285942,
    fullRecordGapCenterValue - 285898,
    fullRecordGapCenterValue - 285742,
    fullRecordGapCenterValue - 285738,
    fullRecordGapCenterValue - 285598,
    fullRecordGapCenterValue - 285394,
    fullRecordGapCenterValue - 285378,
    fullRecordGapCenterValue - 285198,
    fullRecordGapCenterValue - 285148,
    fullRecordGapCenterValue - 285120,
    fullRecordGapCenterValue - 285042,
    fullRecordGapCenterValue - 284938,
    fullRecordGapCenterValue - 284932,
    fullRecordGapCenterValue - 284764,
    fullRecordGapCenterValue - 284644,
    fullRecordGapCenterValue - 284638,
    fullRecordGapCenterValue - 284592,
    fullRecordGapCenterValue - 284542,
    fullRecordGapCenterValue - 284422,
    fullRecordGapCenterValue - 284322,
    fullRecordGapCenterValue - 284302,
    fullRecordGapCenterValue - 284044,
    fullRecordGapCenterValue - 284038,
    fullRecordGapCenterValue - 283854,
    fullRecordGapCenterValue - 283828,
    fullRecordGapCenterValue - 283818,
    fullRecordGapCenterValue - 283702,
    fullRecordGapCenterValue - 283684,
    fullRecordGapCenterValue - 283614,
    fullRecordGapCenterValue - 283534,
    fullRecordGapCenterValue - 283500]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00033_fermat : ∀ n ∈ fullRecordGapRow00033_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02049_not_prime : ¬(recordGapCenter - 288994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288994]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02050_not_prime : ¬(recordGapCenter - 288892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288892]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02051_not_prime : ¬(recordGapCenter - 288844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288844]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02052_not_prime : ¬(recordGapCenter - 288682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288682]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02053_not_prime : ¬(recordGapCenter - 288474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288474]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02054_not_prime : ¬(recordGapCenter - 288322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288322]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02055_not_prime : ¬(recordGapCenter - 288294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288294]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02056_not_prime : ¬(recordGapCenter - 288174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288174]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02057_not_prime : ¬(recordGapCenter - 288172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288172]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02058_not_prime : ¬(recordGapCenter - 288124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288124]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02059_not_prime : ¬(recordGapCenter - 288120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288120]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02060_not_prime : ¬(recordGapCenter - 288000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288000]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02061_not_prime : ¬(recordGapCenter - 287884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287884]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02062_not_prime : ¬(recordGapCenter - 287662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287662]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02063_not_prime : ¬(recordGapCenter - 287634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287634]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02064_not_prime : ¬(recordGapCenter - 287548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287548]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02065_not_prime : ¬(recordGapCenter - 287502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287502]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02066_not_prime : ¬(recordGapCenter - 287458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287458]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02067_not_prime : ¬(recordGapCenter - 287418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287418]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02068_not_prime : ¬(recordGapCenter - 287284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287284]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02069_not_prime : ¬(recordGapCenter - 286978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286978]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02070_not_prime : ¬(recordGapCenter - 286954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286954]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02071_not_prime : ¬(recordGapCenter - 286828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286828]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02072_not_prime : ¬(recordGapCenter - 286720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286720]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02073_not_prime : ¬(recordGapCenter - 286684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286684]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02074_not_prime : ¬(recordGapCenter - 286674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286674]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02075_not_prime : ¬(recordGapCenter - 286662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286662]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02076_not_prime : ¬(recordGapCenter - 286372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286372]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02077_not_prime : ¬(recordGapCenter - 286302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286302]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02078_not_prime : ¬(recordGapCenter - 286282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286282]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02079_not_prime : ¬(recordGapCenter - 286204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286204]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02080_not_prime : ¬(recordGapCenter - 286108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286108]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02081_not_prime : ¬(recordGapCenter - 285954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285954]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02082_not_prime : ¬(recordGapCenter - 285942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285942]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02083_not_prime : ¬(recordGapCenter - 285898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285898]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02084_not_prime : ¬(recordGapCenter - 285742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285742]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02085_not_prime : ¬(recordGapCenter - 285738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285738]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02086_not_prime : ¬(recordGapCenter - 285598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285598]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02087_not_prime : ¬(recordGapCenter - 285394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285394]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02088_not_prime : ¬(recordGapCenter - 285378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285378]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02089_not_prime : ¬(recordGapCenter - 285198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285198]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02090_not_prime : ¬(recordGapCenter - 285148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285148]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02091_not_prime : ¬(recordGapCenter - 285120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285120]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02092_not_prime : ¬(recordGapCenter - 285042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285042]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02093_not_prime : ¬(recordGapCenter - 284938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284938]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02094_not_prime : ¬(recordGapCenter - 284932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284932]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02095_not_prime : ¬(recordGapCenter - 284764).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284764]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02096_not_prime : ¬(recordGapCenter - 284644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284644]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02097_not_prime : ¬(recordGapCenter - 284638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284638]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02098_not_prime : ¬(recordGapCenter - 284592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284592]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02099_not_prime : ¬(recordGapCenter - 284542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284542]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02100_not_prime : ¬(recordGapCenter - 284422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284422]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02101_not_prime : ¬(recordGapCenter - 284322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284322]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02102_not_prime : ¬(recordGapCenter - 284302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284302]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02103_not_prime : ¬(recordGapCenter - 284044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284044]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02104_not_prime : ¬(recordGapCenter - 284038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284038]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02105_not_prime : ¬(recordGapCenter - 283854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283854]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02106_not_prime : ¬(recordGapCenter - 283828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283828]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02107_not_prime : ¬(recordGapCenter - 283818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283818]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02108_not_prime : ¬(recordGapCenter - 283702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283702]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02109_not_prime : ¬(recordGapCenter - 283684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283684]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02110_not_prime : ¬(recordGapCenter - 283614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283614]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02111_not_prime : ¬(recordGapCenter - 283534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283534]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm02112_not_prime : ¬(recordGapCenter - 283500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283500]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

end PrimeFactorUnimodality
