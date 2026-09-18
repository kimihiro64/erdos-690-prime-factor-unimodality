import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00127_values : List Nat :=
  [fullRecordGapCenterValue + 474146,
    fullRecordGapCenterValue + 474170,
    fullRecordGapCenterValue + 474182,
    fullRecordGapCenterValue + 474248,
    fullRecordGapCenterValue + 474258,
    fullRecordGapCenterValue + 474302,
    fullRecordGapCenterValue + 474332,
    fullRecordGapCenterValue + 474378,
    fullRecordGapCenterValue + 474542,
    fullRecordGapCenterValue + 474590,
    fullRecordGapCenterValue + 474626,
    fullRecordGapCenterValue + 474686,
    fullRecordGapCenterValue + 474722,
    fullRecordGapCenterValue + 474836,
    fullRecordGapCenterValue + 474882,
    fullRecordGapCenterValue + 475028,
    fullRecordGapCenterValue + 475070,
    fullRecordGapCenterValue + 475142,
    fullRecordGapCenterValue + 475346,
    fullRecordGapCenterValue + 475352,
    fullRecordGapCenterValue + 475382,
    fullRecordGapCenterValue + 475638,
    fullRecordGapCenterValue + 475736,
    fullRecordGapCenterValue + 475802,
    fullRecordGapCenterValue + 475806,
    fullRecordGapCenterValue + 475868,
    fullRecordGapCenterValue + 475892,
    fullRecordGapCenterValue + 475998,
    fullRecordGapCenterValue + 476018,
    fullRecordGapCenterValue + 476072,
    fullRecordGapCenterValue + 476156,
    fullRecordGapCenterValue + 476198,
    fullRecordGapCenterValue + 476312,
    fullRecordGapCenterValue + 476348,
    fullRecordGapCenterValue + 476358,
    fullRecordGapCenterValue + 476390,
    fullRecordGapCenterValue + 476402,
    fullRecordGapCenterValue + 476466,
    fullRecordGapCenterValue + 476642,
    fullRecordGapCenterValue + 476936,
    fullRecordGapCenterValue + 476948,
    fullRecordGapCenterValue + 477038,
    fullRecordGapCenterValue + 477146,
    fullRecordGapCenterValue + 477170,
    fullRecordGapCenterValue + 477186,
    fullRecordGapCenterValue + 477278,
    fullRecordGapCenterValue + 477368,
    fullRecordGapCenterValue + 477446,
    fullRecordGapCenterValue + 477458,
    fullRecordGapCenterValue + 477656,
    fullRecordGapCenterValue + 477678,
    fullRecordGapCenterValue + 477716,
    fullRecordGapCenterValue + 477758,
    fullRecordGapCenterValue + 477762,
    fullRecordGapCenterValue + 477842,
    fullRecordGapCenterValue + 477878,
    fullRecordGapCenterValue + 477956,
    fullRecordGapCenterValue + 478070,
    fullRecordGapCenterValue + 478146,
    fullRecordGapCenterValue + 478158,
    fullRecordGapCenterValue + 478238,
    fullRecordGapCenterValue + 478370,
    fullRecordGapCenterValue + 478472,
    fullRecordGapCenterValue + 478658]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00127_fermat : ∀ n ∈ fullRecordGapRow00127_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08065_not_prime : ¬(recordGapCenter + 474146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474146]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08066_not_prime : ¬(recordGapCenter + 474170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474170]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08067_not_prime : ¬(recordGapCenter + 474182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474182]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08068_not_prime : ¬(recordGapCenter + 474248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474248]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08069_not_prime : ¬(recordGapCenter + 474258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474258]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08070_not_prime : ¬(recordGapCenter + 474302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474302]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08071_not_prime : ¬(recordGapCenter + 474332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474332]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08072_not_prime : ¬(recordGapCenter + 474378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474378]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08073_not_prime : ¬(recordGapCenter + 474542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474542]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08074_not_prime : ¬(recordGapCenter + 474590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474590]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08075_not_prime : ¬(recordGapCenter + 474626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474626]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08076_not_prime : ¬(recordGapCenter + 474686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474686]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08077_not_prime : ¬(recordGapCenter + 474722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474722]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08078_not_prime : ¬(recordGapCenter + 474836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474836]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08079_not_prime : ¬(recordGapCenter + 474882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474882]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08080_not_prime : ¬(recordGapCenter + 475028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475028]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08081_not_prime : ¬(recordGapCenter + 475070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475070]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08082_not_prime : ¬(recordGapCenter + 475142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475142]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08083_not_prime : ¬(recordGapCenter + 475346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475346]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08084_not_prime : ¬(recordGapCenter + 475352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475352]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08085_not_prime : ¬(recordGapCenter + 475382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475382]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08086_not_prime : ¬(recordGapCenter + 475638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475638]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08087_not_prime : ¬(recordGapCenter + 475736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475736]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08088_not_prime : ¬(recordGapCenter + 475802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475802]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08089_not_prime : ¬(recordGapCenter + 475806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475806]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08090_not_prime : ¬(recordGapCenter + 475868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475868]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08091_not_prime : ¬(recordGapCenter + 475892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475892]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08092_not_prime : ¬(recordGapCenter + 475998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475998]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08093_not_prime : ¬(recordGapCenter + 476018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476018]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08094_not_prime : ¬(recordGapCenter + 476072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476072]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08095_not_prime : ¬(recordGapCenter + 476156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476156]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08096_not_prime : ¬(recordGapCenter + 476198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476198]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08097_not_prime : ¬(recordGapCenter + 476312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476312]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08098_not_prime : ¬(recordGapCenter + 476348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476348]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08099_not_prime : ¬(recordGapCenter + 476358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476358]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08100_not_prime : ¬(recordGapCenter + 476390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476390]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08101_not_prime : ¬(recordGapCenter + 476402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476402]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08102_not_prime : ¬(recordGapCenter + 476466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476466]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08103_not_prime : ¬(recordGapCenter + 476642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476642]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08104_not_prime : ¬(recordGapCenter + 476936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476936]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08105_not_prime : ¬(recordGapCenter + 476948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476948]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08106_not_prime : ¬(recordGapCenter + 477038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477038]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08107_not_prime : ¬(recordGapCenter + 477146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477146]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08108_not_prime : ¬(recordGapCenter + 477170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477170]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08109_not_prime : ¬(recordGapCenter + 477186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477186]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08110_not_prime : ¬(recordGapCenter + 477278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477278]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08111_not_prime : ¬(recordGapCenter + 477368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477368]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08112_not_prime : ¬(recordGapCenter + 477446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477446]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08113_not_prime : ¬(recordGapCenter + 477458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477458]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08114_not_prime : ¬(recordGapCenter + 477656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477656]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08115_not_prime : ¬(recordGapCenter + 477678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477678]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08116_not_prime : ¬(recordGapCenter + 477716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477716]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08117_not_prime : ¬(recordGapCenter + 477758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477758]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08118_not_prime : ¬(recordGapCenter + 477762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477762]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08119_not_prime : ¬(recordGapCenter + 477842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477842]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08120_not_prime : ¬(recordGapCenter + 477878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477878]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08121_not_prime : ¬(recordGapCenter + 477956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477956]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08122_not_prime : ¬(recordGapCenter + 478070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478070]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08123_not_prime : ¬(recordGapCenter + 478146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478146]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08124_not_prime : ¬(recordGapCenter + 478158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478158]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08125_not_prime : ¬(recordGapCenter + 478238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478238]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08126_not_prime : ¬(recordGapCenter + 478370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478370]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08127_not_prime : ¬(recordGapCenter + 478472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478472]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

theorem fullRecordGapTerm08128_not_prime : ¬(recordGapCenter + 478658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478658]
  · apply fullRecordGapRow00127_fermat
    simp [fullRecordGapRow00127_values]

end PrimeFactorUnimodality
