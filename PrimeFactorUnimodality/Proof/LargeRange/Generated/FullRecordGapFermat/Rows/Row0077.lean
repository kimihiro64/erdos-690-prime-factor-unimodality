import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00077_values : List Nat :=
  [fullRecordGapCenterValue + 207938,
    fullRecordGapCenterValue + 207986,
    fullRecordGapCenterValue + 208118,
    fullRecordGapCenterValue + 208268,
    fullRecordGapCenterValue + 208346,
    fullRecordGapCenterValue + 208412,
    fullRecordGapCenterValue + 208652,
    fullRecordGapCenterValue + 208892,
    fullRecordGapCenterValue + 209088,
    fullRecordGapCenterValue + 209102,
    fullRecordGapCenterValue + 209156,
    fullRecordGapCenterValue + 209252,
    fullRecordGapCenterValue + 209318,
    fullRecordGapCenterValue + 209366,
    fullRecordGapCenterValue + 209522,
    fullRecordGapCenterValue + 209732,
    fullRecordGapCenterValue + 209822,
    fullRecordGapCenterValue + 209906,
    fullRecordGapCenterValue + 209952,
    fullRecordGapCenterValue + 210038,
    fullRecordGapCenterValue + 210068,
    fullRecordGapCenterValue + 210212,
    fullRecordGapCenterValue + 210458,
    fullRecordGapCenterValue + 210506,
    fullRecordGapCenterValue + 210662,
    fullRecordGapCenterValue + 210746,
    fullRecordGapCenterValue + 210758,
    fullRecordGapCenterValue + 210788,
    fullRecordGapCenterValue + 211082,
    fullRecordGapCenterValue + 211226,
    fullRecordGapCenterValue + 211298,
    fullRecordGapCenterValue + 211382,
    fullRecordGapCenterValue + 211538,
    fullRecordGapCenterValue + 211748,
    fullRecordGapCenterValue + 211766,
    fullRecordGapCenterValue + 211886,
    fullRecordGapCenterValue + 212066,
    fullRecordGapCenterValue + 212276,
    fullRecordGapCenterValue + 212438,
    fullRecordGapCenterValue + 212486,
    fullRecordGapCenterValue + 212522,
    fullRecordGapCenterValue + 212546,
    fullRecordGapCenterValue + 212606,
    fullRecordGapCenterValue + 212642,
    fullRecordGapCenterValue + 213062,
    fullRecordGapCenterValue + 213068,
    fullRecordGapCenterValue + 213182,
    fullRecordGapCenterValue + 213326,
    fullRecordGapCenterValue + 213362,
    fullRecordGapCenterValue + 213518,
    fullRecordGapCenterValue + 213602,
    fullRecordGapCenterValue + 213722,
    fullRecordGapCenterValue + 213806,
    fullRecordGapCenterValue + 213812,
    fullRecordGapCenterValue + 214028,
    fullRecordGapCenterValue + 214142,
    fullRecordGapCenterValue + 214196,
    fullRecordGapCenterValue + 214202,
    fullRecordGapCenterValue + 214326,
    fullRecordGapCenterValue + 214532,
    fullRecordGapCenterValue + 214646,
    fullRecordGapCenterValue + 215132,
    fullRecordGapCenterValue + 215282,
    fullRecordGapCenterValue + 215342]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00077_fermat : ∀ n ∈ fullRecordGapRow00077_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04865_not_prime : ¬(recordGapCenter + 207938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207938]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04866_not_prime : ¬(recordGapCenter + 207986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 207986]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04867_not_prime : ¬(recordGapCenter + 208118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 208118]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04868_not_prime : ¬(recordGapCenter + 208268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 208268]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04869_not_prime : ¬(recordGapCenter + 208346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 208346]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04870_not_prime : ¬(recordGapCenter + 208412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 208412]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04871_not_prime : ¬(recordGapCenter + 208652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 208652]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04872_not_prime : ¬(recordGapCenter + 208892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 208892]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04873_not_prime : ¬(recordGapCenter + 209088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209088]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04874_not_prime : ¬(recordGapCenter + 209102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209102]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04875_not_prime : ¬(recordGapCenter + 209156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209156]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04876_not_prime : ¬(recordGapCenter + 209252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209252]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04877_not_prime : ¬(recordGapCenter + 209318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209318]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04878_not_prime : ¬(recordGapCenter + 209366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209366]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04879_not_prime : ¬(recordGapCenter + 209522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209522]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04880_not_prime : ¬(recordGapCenter + 209732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209732]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04881_not_prime : ¬(recordGapCenter + 209822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209822]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04882_not_prime : ¬(recordGapCenter + 209906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209906]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04883_not_prime : ¬(recordGapCenter + 209952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 209952]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04884_not_prime : ¬(recordGapCenter + 210038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210038]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04885_not_prime : ¬(recordGapCenter + 210068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210068]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04886_not_prime : ¬(recordGapCenter + 210212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210212]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04887_not_prime : ¬(recordGapCenter + 210458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210458]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04888_not_prime : ¬(recordGapCenter + 210506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210506]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04889_not_prime : ¬(recordGapCenter + 210662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210662]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04890_not_prime : ¬(recordGapCenter + 210746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210746]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04891_not_prime : ¬(recordGapCenter + 210758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210758]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04892_not_prime : ¬(recordGapCenter + 210788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 210788]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04893_not_prime : ¬(recordGapCenter + 211082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 211082]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04894_not_prime : ¬(recordGapCenter + 211226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 211226]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04895_not_prime : ¬(recordGapCenter + 211298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 211298]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04896_not_prime : ¬(recordGapCenter + 211382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 211382]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04897_not_prime : ¬(recordGapCenter + 211538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 211538]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04898_not_prime : ¬(recordGapCenter + 211748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 211748]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04899_not_prime : ¬(recordGapCenter + 211766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 211766]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04900_not_prime : ¬(recordGapCenter + 211886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 211886]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04901_not_prime : ¬(recordGapCenter + 212066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 212066]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04902_not_prime : ¬(recordGapCenter + 212276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 212276]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04903_not_prime : ¬(recordGapCenter + 212438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 212438]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04904_not_prime : ¬(recordGapCenter + 212486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 212486]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04905_not_prime : ¬(recordGapCenter + 212522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 212522]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04906_not_prime : ¬(recordGapCenter + 212546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 212546]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04907_not_prime : ¬(recordGapCenter + 212606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 212606]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04908_not_prime : ¬(recordGapCenter + 212642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 212642]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04909_not_prime : ¬(recordGapCenter + 213062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213062]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04910_not_prime : ¬(recordGapCenter + 213068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213068]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04911_not_prime : ¬(recordGapCenter + 213182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213182]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04912_not_prime : ¬(recordGapCenter + 213326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213326]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04913_not_prime : ¬(recordGapCenter + 213362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213362]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04914_not_prime : ¬(recordGapCenter + 213518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213518]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04915_not_prime : ¬(recordGapCenter + 213602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213602]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04916_not_prime : ¬(recordGapCenter + 213722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213722]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04917_not_prime : ¬(recordGapCenter + 213806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213806]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04918_not_prime : ¬(recordGapCenter + 213812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 213812]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04919_not_prime : ¬(recordGapCenter + 214028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 214028]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04920_not_prime : ¬(recordGapCenter + 214142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 214142]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04921_not_prime : ¬(recordGapCenter + 214196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 214196]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04922_not_prime : ¬(recordGapCenter + 214202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 214202]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04923_not_prime : ¬(recordGapCenter + 214326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 214326]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04924_not_prime : ¬(recordGapCenter + 214532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 214532]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04925_not_prime : ¬(recordGapCenter + 214646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 214646]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04926_not_prime : ¬(recordGapCenter + 215132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215132]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04927_not_prime : ¬(recordGapCenter + 215282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215282]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

theorem fullRecordGapTerm04928_not_prime : ¬(recordGapCenter + 215342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215342]
  · apply fullRecordGapRow00077_fermat
    simp [fullRecordGapRow00077_values]

end PrimeFactorUnimodality
