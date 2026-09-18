import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00108_values : List Nat :=
  [fullRecordGapCenterValue + 382566,
    fullRecordGapCenterValue + 382638,
    fullRecordGapCenterValue + 382856,
    fullRecordGapCenterValue + 382868,
    fullRecordGapCenterValue + 382898,
    fullRecordGapCenterValue + 382946,
    fullRecordGapCenterValue + 383048,
    fullRecordGapCenterValue + 383066,
    fullRecordGapCenterValue + 383132,
    fullRecordGapCenterValue + 383178,
    fullRecordGapCenterValue + 383198,
    fullRecordGapCenterValue + 383252,
    fullRecordGapCenterValue + 383288,
    fullRecordGapCenterValue + 383328,
    fullRecordGapCenterValue + 383336,
    fullRecordGapCenterValue + 383406,
    fullRecordGapCenterValue + 383442,
    fullRecordGapCenterValue + 383498,
    fullRecordGapCenterValue + 383546,
    fullRecordGapCenterValue + 383828,
    fullRecordGapCenterValue + 383906,
    fullRecordGapCenterValue + 383982,
    fullRecordGapCenterValue + 384000,
    fullRecordGapCenterValue + 384086,
    fullRecordGapCenterValue + 384198,
    fullRecordGapCenterValue + 384242,
    fullRecordGapCenterValue + 384378,
    fullRecordGapCenterValue + 384458,
    fullRecordGapCenterValue + 384518,
    fullRecordGapCenterValue + 384542,
    fullRecordGapCenterValue + 384546,
    fullRecordGapCenterValue + 384548,
    fullRecordGapCenterValue + 384596,
    fullRecordGapCenterValue + 384632,
    fullRecordGapCenterValue + 384638,
    fullRecordGapCenterValue + 384912,
    fullRecordGapCenterValue + 384918,
    fullRecordGapCenterValue + 384968,
    fullRecordGapCenterValue + 385166,
    fullRecordGapCenterValue + 385302,
    fullRecordGapCenterValue + 385316,
    fullRecordGapCenterValue + 385386,
    fullRecordGapCenterValue + 385508,
    fullRecordGapCenterValue + 385676,
    fullRecordGapCenterValue + 385772,
    fullRecordGapCenterValue + 386018,
    fullRecordGapCenterValue + 386108,
    fullRecordGapCenterValue + 386186,
    fullRecordGapCenterValue + 386286,
    fullRecordGapCenterValue + 386306,
    fullRecordGapCenterValue + 386402,
    fullRecordGapCenterValue + 386418,
    fullRecordGapCenterValue + 386696,
    fullRecordGapCenterValue + 386706,
    fullRecordGapCenterValue + 386898,
    fullRecordGapCenterValue + 387026,
    fullRecordGapCenterValue + 387116,
    fullRecordGapCenterValue + 387188,
    fullRecordGapCenterValue + 387200,
    fullRecordGapCenterValue + 387272,
    fullRecordGapCenterValue + 387308,
    fullRecordGapCenterValue + 387318,
    fullRecordGapCenterValue + 387402,
    fullRecordGapCenterValue + 387446]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00108_fermat : ∀ n ∈ fullRecordGapRow00108_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06849_not_prime : ¬(recordGapCenter + 382566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382566]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06850_not_prime : ¬(recordGapCenter + 382638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382638]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06851_not_prime : ¬(recordGapCenter + 382856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382856]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06852_not_prime : ¬(recordGapCenter + 382868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382868]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06853_not_prime : ¬(recordGapCenter + 382898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382898]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06854_not_prime : ¬(recordGapCenter + 382946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382946]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06855_not_prime : ¬(recordGapCenter + 383048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383048]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06856_not_prime : ¬(recordGapCenter + 383066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383066]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06857_not_prime : ¬(recordGapCenter + 383132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383132]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06858_not_prime : ¬(recordGapCenter + 383178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383178]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06859_not_prime : ¬(recordGapCenter + 383198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383198]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06860_not_prime : ¬(recordGapCenter + 383252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383252]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06861_not_prime : ¬(recordGapCenter + 383288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383288]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06862_not_prime : ¬(recordGapCenter + 383328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383328]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06863_not_prime : ¬(recordGapCenter + 383336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383336]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06864_not_prime : ¬(recordGapCenter + 383406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383406]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06865_not_prime : ¬(recordGapCenter + 383442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383442]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06866_not_prime : ¬(recordGapCenter + 383498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383498]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06867_not_prime : ¬(recordGapCenter + 383546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383546]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06868_not_prime : ¬(recordGapCenter + 383828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383828]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06869_not_prime : ¬(recordGapCenter + 383906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383906]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06870_not_prime : ¬(recordGapCenter + 383982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383982]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06871_not_prime : ¬(recordGapCenter + 384000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384000]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06872_not_prime : ¬(recordGapCenter + 384086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384086]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06873_not_prime : ¬(recordGapCenter + 384198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384198]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06874_not_prime : ¬(recordGapCenter + 384242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384242]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06875_not_prime : ¬(recordGapCenter + 384378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384378]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06876_not_prime : ¬(recordGapCenter + 384458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384458]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06877_not_prime : ¬(recordGapCenter + 384518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384518]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06878_not_prime : ¬(recordGapCenter + 384542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384542]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06879_not_prime : ¬(recordGapCenter + 384546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384546]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06880_not_prime : ¬(recordGapCenter + 384548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384548]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06881_not_prime : ¬(recordGapCenter + 384596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384596]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06882_not_prime : ¬(recordGapCenter + 384632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384632]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06883_not_prime : ¬(recordGapCenter + 384638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384638]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06884_not_prime : ¬(recordGapCenter + 384912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384912]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06885_not_prime : ¬(recordGapCenter + 384918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384918]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06886_not_prime : ¬(recordGapCenter + 384968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384968]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06887_not_prime : ¬(recordGapCenter + 385166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385166]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06888_not_prime : ¬(recordGapCenter + 385302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385302]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06889_not_prime : ¬(recordGapCenter + 385316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385316]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06890_not_prime : ¬(recordGapCenter + 385386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385386]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06891_not_prime : ¬(recordGapCenter + 385508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385508]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06892_not_prime : ¬(recordGapCenter + 385676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385676]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06893_not_prime : ¬(recordGapCenter + 385772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385772]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06894_not_prime : ¬(recordGapCenter + 386018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386018]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06895_not_prime : ¬(recordGapCenter + 386108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386108]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06896_not_prime : ¬(recordGapCenter + 386186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386186]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06897_not_prime : ¬(recordGapCenter + 386286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386286]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06898_not_prime : ¬(recordGapCenter + 386306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386306]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06899_not_prime : ¬(recordGapCenter + 386402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386402]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06900_not_prime : ¬(recordGapCenter + 386418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386418]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06901_not_prime : ¬(recordGapCenter + 386696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386696]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06902_not_prime : ¬(recordGapCenter + 386706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386706]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06903_not_prime : ¬(recordGapCenter + 386898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386898]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06904_not_prime : ¬(recordGapCenter + 387026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387026]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06905_not_prime : ¬(recordGapCenter + 387116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387116]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06906_not_prime : ¬(recordGapCenter + 387188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387188]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06907_not_prime : ¬(recordGapCenter + 387200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387200]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06908_not_prime : ¬(recordGapCenter + 387272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387272]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06909_not_prime : ¬(recordGapCenter + 387308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387308]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06910_not_prime : ¬(recordGapCenter + 387318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387318]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06911_not_prime : ¬(recordGapCenter + 387402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387402]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

theorem fullRecordGapTerm06912_not_prime : ¬(recordGapCenter + 387446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387446]
  · apply fullRecordGapRow00108_fermat
    simp [fullRecordGapRow00108_values]

end PrimeFactorUnimodality
