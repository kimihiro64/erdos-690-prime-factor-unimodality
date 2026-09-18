import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00136_values : List Nat :=
  [fullRecordGapCenterValue + 516038,
    fullRecordGapCenterValue + 516092,
    fullRecordGapCenterValue + 516096,
    fullRecordGapCenterValue + 516332,
    fullRecordGapCenterValue + 516462,
    fullRecordGapCenterValue + 516938,
    fullRecordGapCenterValue + 516968,
    fullRecordGapCenterValue + 517052,
    fullRecordGapCenterValue + 517148,
    fullRecordGapCenterValue + 517206,
    fullRecordGapCenterValue + 517226,
    fullRecordGapCenterValue + 517346,
    fullRecordGapCenterValue + 517490,
    fullRecordGapCenterValue + 517596,
    fullRecordGapCenterValue + 517742,
    fullRecordGapCenterValue + 517746,
    fullRecordGapCenterValue + 517758,
    fullRecordGapCenterValue + 517812,
    fullRecordGapCenterValue + 517938,
    fullRecordGapCenterValue + 517970,
    fullRecordGapCenterValue + 517988,
    fullRecordGapCenterValue + 518018,
    fullRecordGapCenterValue + 518036,
    fullRecordGapCenterValue + 518106,
    fullRecordGapCenterValue + 518108,
    fullRecordGapCenterValue + 518142,
    fullRecordGapCenterValue + 518156,
    fullRecordGapCenterValue + 518226,
    fullRecordGapCenterValue + 518246,
    fullRecordGapCenterValue + 518268,
    fullRecordGapCenterValue + 518270,
    fullRecordGapCenterValue + 518318,
    fullRecordGapCenterValue + 518390,
    fullRecordGapCenterValue + 518400,
    fullRecordGapCenterValue + 518402,
    fullRecordGapCenterValue + 518438,
    fullRecordGapCenterValue + 518616,
    fullRecordGapCenterValue + 518676,
    fullRecordGapCenterValue + 518906,
    fullRecordGapCenterValue + 518918,
    fullRecordGapCenterValue + 518948,
    fullRecordGapCenterValue + 519006,
    fullRecordGapCenterValue + 519032,
    fullRecordGapCenterValue + 519062,
    fullRecordGapCenterValue + 519128,
    fullRecordGapCenterValue + 519206,
    fullRecordGapCenterValue + 519410,
    fullRecordGapCenterValue + 519446,
    fullRecordGapCenterValue + 519668,
    fullRecordGapCenterValue + 519710,
    fullRecordGapCenterValue + 519752,
    fullRecordGapCenterValue + 519852,
    fullRecordGapCenterValue + 520046,
    fullRecordGapCenterValue + 520062,
    fullRecordGapCenterValue + 520088,
    fullRecordGapCenterValue + 520158,
    fullRecordGapCenterValue + 520266,
    fullRecordGapCenterValue + 520292,
    fullRecordGapCenterValue + 520458,
    fullRecordGapCenterValue + 520508,
    fullRecordGapCenterValue + 520518,
    fullRecordGapCenterValue + 520602,
    fullRecordGapCenterValue + 520658,
    fullRecordGapCenterValue + 520808]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00136_fermat : ∀ n ∈ fullRecordGapRow00136_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08641_not_prime : ¬(recordGapCenter + 516038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 516038]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08642_not_prime : ¬(recordGapCenter + 516092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 516092]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08643_not_prime : ¬(recordGapCenter + 516096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 516096]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08644_not_prime : ¬(recordGapCenter + 516332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 516332]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08645_not_prime : ¬(recordGapCenter + 516462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 516462]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08646_not_prime : ¬(recordGapCenter + 516938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 516938]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08647_not_prime : ¬(recordGapCenter + 516968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 516968]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08648_not_prime : ¬(recordGapCenter + 517052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517052]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08649_not_prime : ¬(recordGapCenter + 517148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517148]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08650_not_prime : ¬(recordGapCenter + 517206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517206]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08651_not_prime : ¬(recordGapCenter + 517226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517226]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08652_not_prime : ¬(recordGapCenter + 517346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517346]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08653_not_prime : ¬(recordGapCenter + 517490).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517490]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08654_not_prime : ¬(recordGapCenter + 517596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517596]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08655_not_prime : ¬(recordGapCenter + 517742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517742]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08656_not_prime : ¬(recordGapCenter + 517746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517746]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08657_not_prime : ¬(recordGapCenter + 517758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517758]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08658_not_prime : ¬(recordGapCenter + 517812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517812]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08659_not_prime : ¬(recordGapCenter + 517938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517938]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08660_not_prime : ¬(recordGapCenter + 517970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517970]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08661_not_prime : ¬(recordGapCenter + 517988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 517988]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08662_not_prime : ¬(recordGapCenter + 518018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518018]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08663_not_prime : ¬(recordGapCenter + 518036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518036]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08664_not_prime : ¬(recordGapCenter + 518106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518106]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08665_not_prime : ¬(recordGapCenter + 518108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518108]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08666_not_prime : ¬(recordGapCenter + 518142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518142]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08667_not_prime : ¬(recordGapCenter + 518156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518156]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08668_not_prime : ¬(recordGapCenter + 518226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518226]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08669_not_prime : ¬(recordGapCenter + 518246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518246]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08670_not_prime : ¬(recordGapCenter + 518268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518268]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08671_not_prime : ¬(recordGapCenter + 518270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518270]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08672_not_prime : ¬(recordGapCenter + 518318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518318]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08673_not_prime : ¬(recordGapCenter + 518390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518390]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08674_not_prime : ¬(recordGapCenter + 518400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518400]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08675_not_prime : ¬(recordGapCenter + 518402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518402]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08676_not_prime : ¬(recordGapCenter + 518438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518438]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08677_not_prime : ¬(recordGapCenter + 518616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518616]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08678_not_prime : ¬(recordGapCenter + 518676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518676]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08679_not_prime : ¬(recordGapCenter + 518906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518906]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08680_not_prime : ¬(recordGapCenter + 518918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518918]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08681_not_prime : ¬(recordGapCenter + 518948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 518948]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08682_not_prime : ¬(recordGapCenter + 519006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519006]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08683_not_prime : ¬(recordGapCenter + 519032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519032]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08684_not_prime : ¬(recordGapCenter + 519062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519062]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08685_not_prime : ¬(recordGapCenter + 519128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519128]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08686_not_prime : ¬(recordGapCenter + 519206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519206]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08687_not_prime : ¬(recordGapCenter + 519410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519410]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08688_not_prime : ¬(recordGapCenter + 519446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519446]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08689_not_prime : ¬(recordGapCenter + 519668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519668]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08690_not_prime : ¬(recordGapCenter + 519710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519710]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08691_not_prime : ¬(recordGapCenter + 519752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519752]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08692_not_prime : ¬(recordGapCenter + 519852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 519852]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08693_not_prime : ¬(recordGapCenter + 520046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520046]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08694_not_prime : ¬(recordGapCenter + 520062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520062]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08695_not_prime : ¬(recordGapCenter + 520088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520088]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08696_not_prime : ¬(recordGapCenter + 520158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520158]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08697_not_prime : ¬(recordGapCenter + 520266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520266]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08698_not_prime : ¬(recordGapCenter + 520292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520292]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08699_not_prime : ¬(recordGapCenter + 520458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520458]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08700_not_prime : ¬(recordGapCenter + 520508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520508]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08701_not_prime : ¬(recordGapCenter + 520518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520518]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08702_not_prime : ¬(recordGapCenter + 520602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520602]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08703_not_prime : ¬(recordGapCenter + 520658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520658]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

theorem fullRecordGapTerm08704_not_prime : ¬(recordGapCenter + 520808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520808]
  · apply fullRecordGapRow00136_fermat
    simp [fullRecordGapRow00136_values]

end PrimeFactorUnimodality
