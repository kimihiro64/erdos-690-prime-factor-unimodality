import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00080_values : List Nat :=
  [fullRecordGapCenterValue + 229286,
    fullRecordGapCenterValue + 229322,
    fullRecordGapCenterValue + 229358,
    fullRecordGapCenterValue + 229388,
    fullRecordGapCenterValue + 229652,
    fullRecordGapCenterValue + 229826,
    fullRecordGapCenterValue + 230042,
    fullRecordGapCenterValue + 230108,
    fullRecordGapCenterValue + 230366,
    fullRecordGapCenterValue + 230496,
    fullRecordGapCenterValue + 230606,
    fullRecordGapCenterValue + 230618,
    fullRecordGapCenterValue + 230942,
    fullRecordGapCenterValue + 231026,
    fullRecordGapCenterValue + 231092,
    fullRecordGapCenterValue + 231122,
    fullRecordGapCenterValue + 231596,
    fullRecordGapCenterValue + 231662,
    fullRecordGapCenterValue + 231698,
    fullRecordGapCenterValue + 231758,
    fullRecordGapCenterValue + 231866,
    fullRecordGapCenterValue + 231908,
    fullRecordGapCenterValue + 232178,
    fullRecordGapCenterValue + 232226,
    fullRecordGapCenterValue + 232262,
    fullRecordGapCenterValue + 232268,
    fullRecordGapCenterValue + 232292,
    fullRecordGapCenterValue + 232320,
    fullRecordGapCenterValue + 232682,
    fullRecordGapCenterValue + 232796,
    fullRecordGapCenterValue + 232916,
    fullRecordGapCenterValue + 233186,
    fullRecordGapCenterValue + 233348,
    fullRecordGapCenterValue + 233378,
    fullRecordGapCenterValue + 233462,
    fullRecordGapCenterValue + 233756,
    fullRecordGapCenterValue + 233822,
    fullRecordGapCenterValue + 233858,
    fullRecordGapCenterValue + 234326,
    fullRecordGapCenterValue + 234386,
    fullRecordGapCenterValue + 234518,
    fullRecordGapCenterValue + 234722,
    fullRecordGapCenterValue + 234932,
    fullRecordGapCenterValue + 234998,
    fullRecordGapCenterValue + 235028,
    fullRecordGapCenterValue + 235406,
    fullRecordGapCenterValue + 235442,
    fullRecordGapCenterValue + 235526,
    fullRecordGapCenterValue + 235652,
    fullRecordGapCenterValue + 235778,
    fullRecordGapCenterValue + 235982,
    fullRecordGapCenterValue + 235988,
    fullRecordGapCenterValue + 236066,
    fullRecordGapCenterValue + 236196,
    fullRecordGapCenterValue + 236250,
    fullRecordGapCenterValue + 236378,
    fullRecordGapCenterValue + 236426,
    fullRecordGapCenterValue + 236636,
    fullRecordGapCenterValue + 236798,
    fullRecordGapCenterValue + 236822,
    fullRecordGapCenterValue + 236828,
    fullRecordGapCenterValue + 236846,
    fullRecordGapCenterValue + 236906,
    fullRecordGapCenterValue + 236972]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00080_fermat : ∀ n ∈ fullRecordGapRow00080_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05057_not_prime : ¬(recordGapCenter + 229286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 229286]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05058_not_prime : ¬(recordGapCenter + 229322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 229322]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05059_not_prime : ¬(recordGapCenter + 229358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 229358]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05060_not_prime : ¬(recordGapCenter + 229388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 229388]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05061_not_prime : ¬(recordGapCenter + 229652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 229652]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05062_not_prime : ¬(recordGapCenter + 229826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 229826]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05063_not_prime : ¬(recordGapCenter + 230042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 230042]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05064_not_prime : ¬(recordGapCenter + 230108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 230108]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05065_not_prime : ¬(recordGapCenter + 230366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 230366]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05066_not_prime : ¬(recordGapCenter + 230496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 230496]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05067_not_prime : ¬(recordGapCenter + 230606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 230606]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05068_not_prime : ¬(recordGapCenter + 230618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 230618]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05069_not_prime : ¬(recordGapCenter + 230942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 230942]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05070_not_prime : ¬(recordGapCenter + 231026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231026]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05071_not_prime : ¬(recordGapCenter + 231092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231092]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05072_not_prime : ¬(recordGapCenter + 231122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231122]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05073_not_prime : ¬(recordGapCenter + 231596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231596]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05074_not_prime : ¬(recordGapCenter + 231662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231662]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05075_not_prime : ¬(recordGapCenter + 231698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231698]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05076_not_prime : ¬(recordGapCenter + 231758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231758]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05077_not_prime : ¬(recordGapCenter + 231866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231866]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05078_not_prime : ¬(recordGapCenter + 231908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 231908]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05079_not_prime : ¬(recordGapCenter + 232178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232178]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05080_not_prime : ¬(recordGapCenter + 232226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232226]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05081_not_prime : ¬(recordGapCenter + 232262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232262]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05082_not_prime : ¬(recordGapCenter + 232268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232268]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05083_not_prime : ¬(recordGapCenter + 232292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232292]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05084_not_prime : ¬(recordGapCenter + 232320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232320]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05085_not_prime : ¬(recordGapCenter + 232682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232682]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05086_not_prime : ¬(recordGapCenter + 232796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232796]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05087_not_prime : ¬(recordGapCenter + 232916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 232916]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05088_not_prime : ¬(recordGapCenter + 233186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 233186]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05089_not_prime : ¬(recordGapCenter + 233348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 233348]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05090_not_prime : ¬(recordGapCenter + 233378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 233378]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05091_not_prime : ¬(recordGapCenter + 233462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 233462]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05092_not_prime : ¬(recordGapCenter + 233756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 233756]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05093_not_prime : ¬(recordGapCenter + 233822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 233822]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05094_not_prime : ¬(recordGapCenter + 233858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 233858]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05095_not_prime : ¬(recordGapCenter + 234326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 234326]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05096_not_prime : ¬(recordGapCenter + 234386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 234386]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05097_not_prime : ¬(recordGapCenter + 234518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 234518]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05098_not_prime : ¬(recordGapCenter + 234722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 234722]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05099_not_prime : ¬(recordGapCenter + 234932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 234932]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05100_not_prime : ¬(recordGapCenter + 234998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 234998]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05101_not_prime : ¬(recordGapCenter + 235028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 235028]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05102_not_prime : ¬(recordGapCenter + 235406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 235406]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05103_not_prime : ¬(recordGapCenter + 235442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 235442]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05104_not_prime : ¬(recordGapCenter + 235526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 235526]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05105_not_prime : ¬(recordGapCenter + 235652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 235652]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05106_not_prime : ¬(recordGapCenter + 235778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 235778]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05107_not_prime : ¬(recordGapCenter + 235982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 235982]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05108_not_prime : ¬(recordGapCenter + 235988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 235988]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05109_not_prime : ¬(recordGapCenter + 236066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236066]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05110_not_prime : ¬(recordGapCenter + 236196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236196]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05111_not_prime : ¬(recordGapCenter + 236250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236250]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05112_not_prime : ¬(recordGapCenter + 236378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236378]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05113_not_prime : ¬(recordGapCenter + 236426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236426]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05114_not_prime : ¬(recordGapCenter + 236636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236636]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05115_not_prime : ¬(recordGapCenter + 236798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236798]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05116_not_prime : ¬(recordGapCenter + 236822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236822]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05117_not_prime : ¬(recordGapCenter + 236828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236828]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05118_not_prime : ¬(recordGapCenter + 236846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236846]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05119_not_prime : ¬(recordGapCenter + 236906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236906]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

theorem fullRecordGapTerm05120_not_prime : ¬(recordGapCenter + 236972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 236972]
  · apply fullRecordGapRow00080_fermat
    simp [fullRecordGapRow00080_values]

end PrimeFactorUnimodality
