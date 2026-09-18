import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00089_values : List Nat :=
  [fullRecordGapCenterValue + 286206,
    fullRecordGapCenterValue + 286226,
    fullRecordGapCenterValue + 286302,
    fullRecordGapCenterValue + 286422,
    fullRecordGapCenterValue + 286652,
    fullRecordGapCenterValue + 286658,
    fullRecordGapCenterValue + 286746,
    fullRecordGapCenterValue + 286802,
    fullRecordGapCenterValue + 286842,
    fullRecordGapCenterValue + 287018,
    fullRecordGapCenterValue + 287058,
    fullRecordGapCenterValue + 287108,
    fullRecordGapCenterValue + 287138,
    fullRecordGapCenterValue + 287142,
    fullRecordGapCenterValue + 287156,
    fullRecordGapCenterValue + 287348,
    fullRecordGapCenterValue + 287372,
    fullRecordGapCenterValue + 287418,
    fullRecordGapCenterValue + 287598,
    fullRecordGapCenterValue + 287642,
    fullRecordGapCenterValue + 287852,
    fullRecordGapCenterValue + 287942,
    fullRecordGapCenterValue + 287948,
    fullRecordGapCenterValue + 288026,
    fullRecordGapCenterValue + 288102,
    fullRecordGapCenterValue + 288138,
    fullRecordGapCenterValue + 288146,
    fullRecordGapCenterValue + 288188,
    fullRecordGapCenterValue + 288356,
    fullRecordGapCenterValue + 288446,
    fullRecordGapCenterValue + 288506,
    fullRecordGapCenterValue + 288542,
    fullRecordGapCenterValue + 288962,
    fullRecordGapCenterValue + 289082,
    fullRecordGapCenterValue + 289122,
    fullRecordGapCenterValue + 289166,
    fullRecordGapCenterValue + 289326,
    fullRecordGapCenterValue + 289412,
    fullRecordGapCenterValue + 289482,
    fullRecordGapCenterValue + 289532,
    fullRecordGapCenterValue + 289686,
    fullRecordGapCenterValue + 289866,
    fullRecordGapCenterValue + 289878,
    fullRecordGapCenterValue + 290018,
    fullRecordGapCenterValue + 290042,
    fullRecordGapCenterValue + 290118,
    fullRecordGapCenterValue + 290126,
    fullRecordGapCenterValue + 290400,
    fullRecordGapCenterValue + 290426,
    fullRecordGapCenterValue + 290438,
    fullRecordGapCenterValue + 290468,
    fullRecordGapCenterValue + 290588,
    fullRecordGapCenterValue + 290606,
    fullRecordGapCenterValue + 290622,
    fullRecordGapCenterValue + 290762,
    fullRecordGapCenterValue + 290846,
    fullRecordGapCenterValue + 290876,
    fullRecordGapCenterValue + 290922,
    fullRecordGapCenterValue + 290942,
    fullRecordGapCenterValue + 291026,
    fullRecordGapCenterValue + 291068,
    fullRecordGapCenterValue + 291086,
    fullRecordGapCenterValue + 291098,
    fullRecordGapCenterValue + 291162]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00089_fermat : ∀ n ∈ fullRecordGapRow00089_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05633_not_prime : ¬(recordGapCenter + 286206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286206]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05634_not_prime : ¬(recordGapCenter + 286226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286226]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05635_not_prime : ¬(recordGapCenter + 286302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286302]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05636_not_prime : ¬(recordGapCenter + 286422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286422]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05637_not_prime : ¬(recordGapCenter + 286652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286652]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05638_not_prime : ¬(recordGapCenter + 286658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286658]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05639_not_prime : ¬(recordGapCenter + 286746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286746]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05640_not_prime : ¬(recordGapCenter + 286802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286802]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05641_not_prime : ¬(recordGapCenter + 286842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286842]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05642_not_prime : ¬(recordGapCenter + 287018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287018]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05643_not_prime : ¬(recordGapCenter + 287058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287058]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05644_not_prime : ¬(recordGapCenter + 287108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287108]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05645_not_prime : ¬(recordGapCenter + 287138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287138]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05646_not_prime : ¬(recordGapCenter + 287142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287142]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05647_not_prime : ¬(recordGapCenter + 287156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287156]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05648_not_prime : ¬(recordGapCenter + 287348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287348]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05649_not_prime : ¬(recordGapCenter + 287372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287372]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05650_not_prime : ¬(recordGapCenter + 287418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287418]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05651_not_prime : ¬(recordGapCenter + 287598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287598]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05652_not_prime : ¬(recordGapCenter + 287642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287642]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05653_not_prime : ¬(recordGapCenter + 287852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287852]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05654_not_prime : ¬(recordGapCenter + 287942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287942]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05655_not_prime : ¬(recordGapCenter + 287948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 287948]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05656_not_prime : ¬(recordGapCenter + 288026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288026]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05657_not_prime : ¬(recordGapCenter + 288102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288102]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05658_not_prime : ¬(recordGapCenter + 288138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288138]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05659_not_prime : ¬(recordGapCenter + 288146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288146]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05660_not_prime : ¬(recordGapCenter + 288188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288188]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05661_not_prime : ¬(recordGapCenter + 288356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288356]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05662_not_prime : ¬(recordGapCenter + 288446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288446]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05663_not_prime : ¬(recordGapCenter + 288506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288506]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05664_not_prime : ¬(recordGapCenter + 288542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288542]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05665_not_prime : ¬(recordGapCenter + 288962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 288962]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05666_not_prime : ¬(recordGapCenter + 289082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289082]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05667_not_prime : ¬(recordGapCenter + 289122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289122]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05668_not_prime : ¬(recordGapCenter + 289166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289166]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05669_not_prime : ¬(recordGapCenter + 289326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289326]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05670_not_prime : ¬(recordGapCenter + 289412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289412]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05671_not_prime : ¬(recordGapCenter + 289482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289482]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05672_not_prime : ¬(recordGapCenter + 289532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289532]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05673_not_prime : ¬(recordGapCenter + 289686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289686]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05674_not_prime : ¬(recordGapCenter + 289866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289866]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05675_not_prime : ¬(recordGapCenter + 289878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 289878]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05676_not_prime : ¬(recordGapCenter + 290018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290018]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05677_not_prime : ¬(recordGapCenter + 290042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290042]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05678_not_prime : ¬(recordGapCenter + 290118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290118]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05679_not_prime : ¬(recordGapCenter + 290126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290126]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05680_not_prime : ¬(recordGapCenter + 290400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290400]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05681_not_prime : ¬(recordGapCenter + 290426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290426]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05682_not_prime : ¬(recordGapCenter + 290438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290438]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05683_not_prime : ¬(recordGapCenter + 290468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290468]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05684_not_prime : ¬(recordGapCenter + 290588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290588]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05685_not_prime : ¬(recordGapCenter + 290606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290606]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05686_not_prime : ¬(recordGapCenter + 290622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290622]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05687_not_prime : ¬(recordGapCenter + 290762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290762]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05688_not_prime : ¬(recordGapCenter + 290846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290846]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05689_not_prime : ¬(recordGapCenter + 290876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290876]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05690_not_prime : ¬(recordGapCenter + 290922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290922]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05691_not_prime : ¬(recordGapCenter + 290942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 290942]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05692_not_prime : ¬(recordGapCenter + 291026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291026]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05693_not_prime : ¬(recordGapCenter + 291068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291068]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05694_not_prime : ¬(recordGapCenter + 291086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291086]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05695_not_prime : ¬(recordGapCenter + 291098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291098]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

theorem fullRecordGapTerm05696_not_prime : ¬(recordGapCenter + 291162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291162]
  · apply fullRecordGapRow00089_fermat
    simp [fullRecordGapRow00089_values]

end PrimeFactorUnimodality
