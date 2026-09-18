import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00065_values : List Nat :=
  [fullRecordGapCenterValue + 91682,
    fullRecordGapCenterValue + 92102,
    fullRecordGapCenterValue + 92160,
    fullRecordGapCenterValue + 92186,
    fullRecordGapCenterValue + 92282,
    fullRecordGapCenterValue + 92366,
    fullRecordGapCenterValue + 92400,
    fullRecordGapCenterValue + 92522,
    fullRecordGapCenterValue + 92610,
    fullRecordGapCenterValue + 92618,
    fullRecordGapCenterValue + 92762,
    fullRecordGapCenterValue + 92928,
    fullRecordGapCenterValue + 92942,
    fullRecordGapCenterValue + 92978,
    fullRecordGapCenterValue + 93170,
    fullRecordGapCenterValue + 93182,
    fullRecordGapCenterValue + 93278,
    fullRecordGapCenterValue + 93446,
    fullRecordGapCenterValue + 93542,
    fullRecordGapCenterValue + 93662,
    fullRecordGapCenterValue + 93866,
    fullRecordGapCenterValue + 94080,
    fullRecordGapCenterValue + 94286,
    fullRecordGapCenterValue + 94298,
    fullRecordGapCenterValue + 94538,
    fullRecordGapCenterValue + 94586,
    fullRecordGapCenterValue + 95040,
    fullRecordGapCenterValue + 95126,
    fullRecordGapCenterValue + 95138,
    fullRecordGapCenterValue + 95258,
    fullRecordGapCenterValue + 95558,
    fullRecordGapCenterValue + 95582,
    fullRecordGapCenterValue + 96098,
    fullRecordGapCenterValue + 96626,
    fullRecordGapCenterValue + 96800,
    fullRecordGapCenterValue + 96962,
    fullRecordGapCenterValue + 97046,
    fullRecordGapCenterValue + 97178,
    fullRecordGapCenterValue + 97200,
    fullRecordGapCenterValue + 97238,
    fullRecordGapCenterValue + 97322,
    fullRecordGapCenterValue + 97358,
    fullRecordGapCenterValue + 97466,
    fullRecordGapCenterValue + 97718,
    fullRecordGapCenterValue + 97766,
    fullRecordGapCenterValue + 97946,
    fullRecordGapCenterValue + 98066,
    fullRecordGapCenterValue + 98246,
    fullRecordGapCenterValue + 98522,
    fullRecordGapCenterValue + 98558,
    fullRecordGapCenterValue + 98786,
    fullRecordGapCenterValue + 98858,
    fullRecordGapCenterValue + 98918,
    fullRecordGapCenterValue + 99206,
    fullRecordGapCenterValue + 99278,
    fullRecordGapCenterValue + 99842,
    fullRecordGapCenterValue + 100046,
    fullRecordGapCenterValue + 100238,
    fullRecordGapCenterValue + 100352,
    fullRecordGapCenterValue + 100658,
    fullRecordGapCenterValue + 101162,
    fullRecordGapCenterValue + 101186,
    fullRecordGapCenterValue + 101342,
    fullRecordGapCenterValue + 101546]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00065_fermat : ∀ n ∈ fullRecordGapRow00065_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04097_not_prime : ¬(recordGapCenter + 91682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91682]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04098_not_prime : ¬(recordGapCenter + 92102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92102]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04099_not_prime : ¬(recordGapCenter + 92160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92160]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04100_not_prime : ¬(recordGapCenter + 92186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92186]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04101_not_prime : ¬(recordGapCenter + 92282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92282]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04102_not_prime : ¬(recordGapCenter + 92366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92366]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04103_not_prime : ¬(recordGapCenter + 92400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92400]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04104_not_prime : ¬(recordGapCenter + 92522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92522]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04105_not_prime : ¬(recordGapCenter + 92610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92610]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04106_not_prime : ¬(recordGapCenter + 92618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92618]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04107_not_prime : ¬(recordGapCenter + 92762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92762]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04108_not_prime : ¬(recordGapCenter + 92928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92928]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04109_not_prime : ¬(recordGapCenter + 92942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92942]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04110_not_prime : ¬(recordGapCenter + 92978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92978]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04111_not_prime : ¬(recordGapCenter + 93170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93170]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04112_not_prime : ¬(recordGapCenter + 93182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93182]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04113_not_prime : ¬(recordGapCenter + 93278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93278]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04114_not_prime : ¬(recordGapCenter + 93446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93446]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04115_not_prime : ¬(recordGapCenter + 93542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93542]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04116_not_prime : ¬(recordGapCenter + 93662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93662]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04117_not_prime : ¬(recordGapCenter + 93866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93866]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04118_not_prime : ¬(recordGapCenter + 94080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94080]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04119_not_prime : ¬(recordGapCenter + 94286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94286]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04120_not_prime : ¬(recordGapCenter + 94298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94298]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04121_not_prime : ¬(recordGapCenter + 94538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94538]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04122_not_prime : ¬(recordGapCenter + 94586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94586]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04123_not_prime : ¬(recordGapCenter + 95040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95040]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04124_not_prime : ¬(recordGapCenter + 95126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95126]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04125_not_prime : ¬(recordGapCenter + 95138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95138]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04126_not_prime : ¬(recordGapCenter + 95258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95258]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04127_not_prime : ¬(recordGapCenter + 95558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95558]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04128_not_prime : ¬(recordGapCenter + 95582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95582]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04129_not_prime : ¬(recordGapCenter + 96098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96098]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04130_not_prime : ¬(recordGapCenter + 96626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96626]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04131_not_prime : ¬(recordGapCenter + 96800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96800]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04132_not_prime : ¬(recordGapCenter + 96962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96962]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04133_not_prime : ¬(recordGapCenter + 97046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97046]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04134_not_prime : ¬(recordGapCenter + 97178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97178]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04135_not_prime : ¬(recordGapCenter + 97200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97200]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04136_not_prime : ¬(recordGapCenter + 97238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97238]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04137_not_prime : ¬(recordGapCenter + 97322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97322]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04138_not_prime : ¬(recordGapCenter + 97358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97358]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04139_not_prime : ¬(recordGapCenter + 97466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97466]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04140_not_prime : ¬(recordGapCenter + 97718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97718]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04141_not_prime : ¬(recordGapCenter + 97766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97766]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04142_not_prime : ¬(recordGapCenter + 97946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97946]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04143_not_prime : ¬(recordGapCenter + 98066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98066]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04144_not_prime : ¬(recordGapCenter + 98246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98246]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04145_not_prime : ¬(recordGapCenter + 98522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98522]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04146_not_prime : ¬(recordGapCenter + 98558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98558]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04147_not_prime : ¬(recordGapCenter + 98786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98786]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04148_not_prime : ¬(recordGapCenter + 98858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98858]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04149_not_prime : ¬(recordGapCenter + 98918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98918]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04150_not_prime : ¬(recordGapCenter + 99206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 99206]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04151_not_prime : ¬(recordGapCenter + 99278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 99278]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04152_not_prime : ¬(recordGapCenter + 99842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 99842]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04153_not_prime : ¬(recordGapCenter + 100046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 100046]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04154_not_prime : ¬(recordGapCenter + 100238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 100238]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04155_not_prime : ¬(recordGapCenter + 100352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 100352]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04156_not_prime : ¬(recordGapCenter + 100658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 100658]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04157_not_prime : ¬(recordGapCenter + 101162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101162]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04158_not_prime : ¬(recordGapCenter + 101186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101186]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04159_not_prime : ¬(recordGapCenter + 101342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101342]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

theorem fullRecordGapTerm04160_not_prime : ¬(recordGapCenter + 101546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101546]
  · apply fullRecordGapRow00065_fermat
    simp [fullRecordGapRow00065_values]

end PrimeFactorUnimodality
