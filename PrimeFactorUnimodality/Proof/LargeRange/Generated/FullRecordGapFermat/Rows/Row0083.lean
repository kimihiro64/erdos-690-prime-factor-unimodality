import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00083_values : List Nat :=
  [fullRecordGapCenterValue + 251102,
    fullRecordGapCenterValue + 251276,
    fullRecordGapCenterValue + 251318,
    fullRecordGapCenterValue + 251366,
    fullRecordGapCenterValue + 251462,
    fullRecordGapCenterValue + 251492,
    fullRecordGapCenterValue + 251606,
    fullRecordGapCenterValue + 251708,
    fullRecordGapCenterValue + 251798,
    fullRecordGapCenterValue + 251858,
    fullRecordGapCenterValue + 251876,
    fullRecordGapCenterValue + 252000,
    fullRecordGapCenterValue + 252158,
    fullRecordGapCenterValue + 252302,
    fullRecordGapCenterValue + 252542,
    fullRecordGapCenterValue + 252698,
    fullRecordGapCenterValue + 252716,
    fullRecordGapCenterValue + 252788,
    fullRecordGapCenterValue + 252962,
    fullRecordGapCenterValue + 253082,
    fullRecordGapCenterValue + 253262,
    fullRecordGapCenterValue + 253268,
    fullRecordGapCenterValue + 253382,
    fullRecordGapCenterValue + 253440,
    fullRecordGapCenterValue + 253466,
    fullRecordGapCenterValue + 253508,
    fullRecordGapCenterValue + 253646,
    fullRecordGapCenterValue + 253718,
    fullRecordGapCenterValue + 253772,
    fullRecordGapCenterValue + 254016,
    fullRecordGapCenterValue + 254100,
    fullRecordGapCenterValue + 254102,
    fullRecordGapCenterValue + 254132,
    fullRecordGapCenterValue + 254348,
    fullRecordGapCenterValue + 254396,
    fullRecordGapCenterValue + 254522,
    fullRecordGapCenterValue + 254588,
    fullRecordGapCenterValue + 254906,
    fullRecordGapCenterValue + 254948,
    fullRecordGapCenterValue + 254972,
    fullRecordGapCenterValue + 255092,
    fullRecordGapCenterValue + 255182,
    fullRecordGapCenterValue + 255428,
    fullRecordGapCenterValue + 255452,
    fullRecordGapCenterValue + 255686,
    fullRecordGapCenterValue + 255902,
    fullRecordGapCenterValue + 255908,
    fullRecordGapCenterValue + 256028,
    fullRecordGapCenterValue + 256148,
    fullRecordGapCenterValue + 256226,
    fullRecordGapCenterValue + 256268,
    fullRecordGapCenterValue + 256436,
    fullRecordGapCenterValue + 256478,
    fullRecordGapCenterValue + 256608,
    fullRecordGapCenterValue + 256628,
    fullRecordGapCenterValue + 256826,
    fullRecordGapCenterValue + 256862,
    fullRecordGapCenterValue + 256898,
    fullRecordGapCenterValue + 256922,
    fullRecordGapCenterValue + 256946,
    fullRecordGapCenterValue + 257126,
    fullRecordGapCenterValue + 257250,
    fullRecordGapCenterValue + 257366,
    fullRecordGapCenterValue + 257612]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00083_fermat : ∀ n ∈ fullRecordGapRow00083_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05249_not_prime : ¬(recordGapCenter + 251102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251102]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05250_not_prime : ¬(recordGapCenter + 251276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251276]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05251_not_prime : ¬(recordGapCenter + 251318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251318]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05252_not_prime : ¬(recordGapCenter + 251366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251366]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05253_not_prime : ¬(recordGapCenter + 251462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251462]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05254_not_prime : ¬(recordGapCenter + 251492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251492]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05255_not_prime : ¬(recordGapCenter + 251606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251606]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05256_not_prime : ¬(recordGapCenter + 251708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251708]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05257_not_prime : ¬(recordGapCenter + 251798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251798]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05258_not_prime : ¬(recordGapCenter + 251858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251858]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05259_not_prime : ¬(recordGapCenter + 251876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 251876]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05260_not_prime : ¬(recordGapCenter + 252000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252000]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05261_not_prime : ¬(recordGapCenter + 252158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252158]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05262_not_prime : ¬(recordGapCenter + 252302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252302]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05263_not_prime : ¬(recordGapCenter + 252542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252542]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05264_not_prime : ¬(recordGapCenter + 252698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252698]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05265_not_prime : ¬(recordGapCenter + 252716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252716]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05266_not_prime : ¬(recordGapCenter + 252788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252788]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05267_not_prime : ¬(recordGapCenter + 252962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252962]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05268_not_prime : ¬(recordGapCenter + 253082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253082]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05269_not_prime : ¬(recordGapCenter + 253262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253262]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05270_not_prime : ¬(recordGapCenter + 253268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253268]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05271_not_prime : ¬(recordGapCenter + 253382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253382]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05272_not_prime : ¬(recordGapCenter + 253440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253440]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05273_not_prime : ¬(recordGapCenter + 253466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253466]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05274_not_prime : ¬(recordGapCenter + 253508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253508]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05275_not_prime : ¬(recordGapCenter + 253646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253646]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05276_not_prime : ¬(recordGapCenter + 253718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253718]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05277_not_prime : ¬(recordGapCenter + 253772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 253772]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05278_not_prime : ¬(recordGapCenter + 254016).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254016]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05279_not_prime : ¬(recordGapCenter + 254100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254100]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05280_not_prime : ¬(recordGapCenter + 254102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254102]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05281_not_prime : ¬(recordGapCenter + 254132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254132]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05282_not_prime : ¬(recordGapCenter + 254348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254348]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05283_not_prime : ¬(recordGapCenter + 254396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254396]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05284_not_prime : ¬(recordGapCenter + 254522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254522]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05285_not_prime : ¬(recordGapCenter + 254588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254588]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05286_not_prime : ¬(recordGapCenter + 254906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254906]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05287_not_prime : ¬(recordGapCenter + 254948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254948]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05288_not_prime : ¬(recordGapCenter + 254972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 254972]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05289_not_prime : ¬(recordGapCenter + 255092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 255092]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05290_not_prime : ¬(recordGapCenter + 255182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 255182]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05291_not_prime : ¬(recordGapCenter + 255428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 255428]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05292_not_prime : ¬(recordGapCenter + 255452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 255452]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05293_not_prime : ¬(recordGapCenter + 255686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 255686]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05294_not_prime : ¬(recordGapCenter + 255902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 255902]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05295_not_prime : ¬(recordGapCenter + 255908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 255908]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05296_not_prime : ¬(recordGapCenter + 256028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256028]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05297_not_prime : ¬(recordGapCenter + 256148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256148]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05298_not_prime : ¬(recordGapCenter + 256226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256226]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05299_not_prime : ¬(recordGapCenter + 256268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256268]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05300_not_prime : ¬(recordGapCenter + 256436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256436]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05301_not_prime : ¬(recordGapCenter + 256478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256478]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05302_not_prime : ¬(recordGapCenter + 256608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256608]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05303_not_prime : ¬(recordGapCenter + 256628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256628]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05304_not_prime : ¬(recordGapCenter + 256826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256826]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05305_not_prime : ¬(recordGapCenter + 256862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256862]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05306_not_prime : ¬(recordGapCenter + 256898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256898]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05307_not_prime : ¬(recordGapCenter + 256922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256922]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05308_not_prime : ¬(recordGapCenter + 256946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 256946]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05309_not_prime : ¬(recordGapCenter + 257126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 257126]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05310_not_prime : ¬(recordGapCenter + 257250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 257250]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05311_not_prime : ¬(recordGapCenter + 257366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 257366]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

theorem fullRecordGapTerm05312_not_prime : ¬(recordGapCenter + 257612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 257612]
  · apply fullRecordGapRow00083_fermat
    simp [fullRecordGapRow00083_values]

end PrimeFactorUnimodality
