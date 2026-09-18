import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00168_values : List Nat :=
  [fullRecordGapCenterValue + 645002,
    fullRecordGapCenterValue + 645032,
    fullRecordGapCenterValue + 645038,
    fullRecordGapCenterValue + 645108,
    fullRecordGapCenterValue + 645120,
    fullRecordGapCenterValue + 645332,
    fullRecordGapCenterValue + 645338,
    fullRecordGapCenterValue + 645356,
    fullRecordGapCenterValue + 645368,
    fullRecordGapCenterValue + 645416,
    fullRecordGapCenterValue + 645486,
    fullRecordGapCenterValue + 645492,
    fullRecordGapCenterValue + 645530,
    fullRecordGapCenterValue + 645782,
    fullRecordGapCenterValue + 645846,
    fullRecordGapCenterValue + 645878,
    fullRecordGapCenterValue + 645972,
    fullRecordGapCenterValue + 646010,
    fullRecordGapCenterValue + 646088,
    fullRecordGapCenterValue + 646172,
    fullRecordGapCenterValue + 646188,
    fullRecordGapCenterValue + 646278,
    fullRecordGapCenterValue + 646292,
    fullRecordGapCenterValue + 646446,
    fullRecordGapCenterValue + 646482,
    fullRecordGapCenterValue + 646502,
    fullRecordGapCenterValue + 646508,
    fullRecordGapCenterValue + 646572,
    fullRecordGapCenterValue + 646662,
    fullRecordGapCenterValue + 646682,
    fullRecordGapCenterValue + 646692,
    fullRecordGapCenterValue + 646718,
    fullRecordGapCenterValue + 646788,
    fullRecordGapCenterValue + 646826,
    fullRecordGapCenterValue + 646838,
    fullRecordGapCenterValue + 646886,
    fullRecordGapCenterValue + 647066,
    fullRecordGapCenterValue + 647132,
    fullRecordGapCenterValue + 647238,
    fullRecordGapCenterValue + 647246,
    fullRecordGapCenterValue + 647286,
    fullRecordGapCenterValue + 647288,
    fullRecordGapCenterValue + 647318,
    fullRecordGapCenterValue + 647336,
    fullRecordGapCenterValue + 647382,
    fullRecordGapCenterValue + 647418,
    fullRecordGapCenterValue + 647432,
    fullRecordGapCenterValue + 647538,
    fullRecordGapCenterValue + 647606,
    fullRecordGapCenterValue + 647798,
    fullRecordGapCenterValue + 647826,
    fullRecordGapCenterValue + 647846,
    fullRecordGapCenterValue + 647916,
    fullRecordGapCenterValue + 647930,
    fullRecordGapCenterValue + 648000,
    fullRecordGapCenterValue + 648012,
    fullRecordGapCenterValue + 648152,
    fullRecordGapCenterValue + 648236,
    fullRecordGapCenterValue + 648302,
    fullRecordGapCenterValue + 648326,
    fullRecordGapCenterValue + 648422,
    fullRecordGapCenterValue + 648476,
    fullRecordGapCenterValue + 648530,
    fullRecordGapCenterValue + 648588]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00168_fermat : ∀ n ∈ fullRecordGapRow00168_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10689_not_prime : ¬(recordGapCenter + 645002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645002]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10690_not_prime : ¬(recordGapCenter + 645032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645032]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10691_not_prime : ¬(recordGapCenter + 645038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645038]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10692_not_prime : ¬(recordGapCenter + 645108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645108]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10693_not_prime : ¬(recordGapCenter + 645120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645120]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10694_not_prime : ¬(recordGapCenter + 645332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645332]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10695_not_prime : ¬(recordGapCenter + 645338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645338]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10696_not_prime : ¬(recordGapCenter + 645356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645356]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10697_not_prime : ¬(recordGapCenter + 645368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645368]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10698_not_prime : ¬(recordGapCenter + 645416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645416]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10699_not_prime : ¬(recordGapCenter + 645486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645486]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10700_not_prime : ¬(recordGapCenter + 645492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645492]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10701_not_prime : ¬(recordGapCenter + 645530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645530]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10702_not_prime : ¬(recordGapCenter + 645782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645782]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10703_not_prime : ¬(recordGapCenter + 645846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645846]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10704_not_prime : ¬(recordGapCenter + 645878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645878]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10705_not_prime : ¬(recordGapCenter + 645972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645972]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10706_not_prime : ¬(recordGapCenter + 646010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646010]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10707_not_prime : ¬(recordGapCenter + 646088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646088]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10708_not_prime : ¬(recordGapCenter + 646172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646172]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10709_not_prime : ¬(recordGapCenter + 646188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646188]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10710_not_prime : ¬(recordGapCenter + 646278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646278]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10711_not_prime : ¬(recordGapCenter + 646292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646292]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10712_not_prime : ¬(recordGapCenter + 646446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646446]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10713_not_prime : ¬(recordGapCenter + 646482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646482]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10714_not_prime : ¬(recordGapCenter + 646502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646502]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10715_not_prime : ¬(recordGapCenter + 646508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646508]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10716_not_prime : ¬(recordGapCenter + 646572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646572]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10717_not_prime : ¬(recordGapCenter + 646662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646662]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10718_not_prime : ¬(recordGapCenter + 646682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646682]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10719_not_prime : ¬(recordGapCenter + 646692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646692]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10720_not_prime : ¬(recordGapCenter + 646718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646718]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10721_not_prime : ¬(recordGapCenter + 646788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646788]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10722_not_prime : ¬(recordGapCenter + 646826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646826]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10723_not_prime : ¬(recordGapCenter + 646838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646838]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10724_not_prime : ¬(recordGapCenter + 646886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646886]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10725_not_prime : ¬(recordGapCenter + 647066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647066]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10726_not_prime : ¬(recordGapCenter + 647132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647132]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10727_not_prime : ¬(recordGapCenter + 647238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647238]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10728_not_prime : ¬(recordGapCenter + 647246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647246]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10729_not_prime : ¬(recordGapCenter + 647286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647286]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10730_not_prime : ¬(recordGapCenter + 647288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647288]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10731_not_prime : ¬(recordGapCenter + 647318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647318]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10732_not_prime : ¬(recordGapCenter + 647336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647336]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10733_not_prime : ¬(recordGapCenter + 647382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647382]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10734_not_prime : ¬(recordGapCenter + 647418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647418]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10735_not_prime : ¬(recordGapCenter + 647432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647432]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10736_not_prime : ¬(recordGapCenter + 647538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647538]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10737_not_prime : ¬(recordGapCenter + 647606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647606]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10738_not_prime : ¬(recordGapCenter + 647798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647798]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10739_not_prime : ¬(recordGapCenter + 647826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647826]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10740_not_prime : ¬(recordGapCenter + 647846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647846]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10741_not_prime : ¬(recordGapCenter + 647916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647916]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10742_not_prime : ¬(recordGapCenter + 647930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647930]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10743_not_prime : ¬(recordGapCenter + 648000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648000]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10744_not_prime : ¬(recordGapCenter + 648012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648012]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10745_not_prime : ¬(recordGapCenter + 648152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648152]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10746_not_prime : ¬(recordGapCenter + 648236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648236]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10747_not_prime : ¬(recordGapCenter + 648302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648302]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10748_not_prime : ¬(recordGapCenter + 648326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648326]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10749_not_prime : ¬(recordGapCenter + 648422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648422]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10750_not_prime : ¬(recordGapCenter + 648476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648476]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10751_not_prime : ¬(recordGapCenter + 648530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648530]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

theorem fullRecordGapTerm10752_not_prime : ¬(recordGapCenter + 648588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648588]
  · apply fullRecordGapRow00168_fermat
    simp [fullRecordGapRow00168_values]

end PrimeFactorUnimodality
