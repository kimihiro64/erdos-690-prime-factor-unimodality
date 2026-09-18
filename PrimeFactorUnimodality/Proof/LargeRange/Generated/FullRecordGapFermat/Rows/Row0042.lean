import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00042_values : List Nat :=
  [fullRecordGapCenterValue + 633638,
    fullRecordGapCenterValue + 633756,
    fullRecordGapCenterValue + 633848,
    fullRecordGapCenterValue + 634076,
    fullRecordGapCenterValue + 634232,
    fullRecordGapCenterValue + 634268,
    fullRecordGapCenterValue + 634298,
    fullRecordGapCenterValue + 634308,
    fullRecordGapCenterValue + 634398,
    fullRecordGapCenterValue + 634548,
    fullRecordGapCenterValue + 634596,
    fullRecordGapCenterValue + 634646,
    fullRecordGapCenterValue + 634706,
    fullRecordGapCenterValue + 634730,
    fullRecordGapCenterValue + 634742,
    fullRecordGapCenterValue + 634802,
    fullRecordGapCenterValue + 634812,
    fullRecordGapCenterValue + 634902,
    fullRecordGapCenterValue + 635040,
    fullRecordGapCenterValue + 635078,
    fullRecordGapCenterValue + 635108,
    fullRecordGapCenterValue + 635178,
    fullRecordGapCenterValue + 635192,
    fullRecordGapCenterValue + 635198,
    fullRecordGapCenterValue + 635372,
    fullRecordGapCenterValue + 635402,
    fullRecordGapCenterValue + 635468,
    fullRecordGapCenterValue + 635556,
    fullRecordGapCenterValue + 635636,
    fullRecordGapCenterValue + 635678,
    fullRecordGapCenterValue + 635772,
    fullRecordGapCenterValue + 635870,
    fullRecordGapCenterValue + 635898,
    fullRecordGapCenterValue + 635918,
    fullRecordGapCenterValue + 635978,
    fullRecordGapCenterValue + 635982,
    fullRecordGapCenterValue + 635988,
    fullRecordGapCenterValue + 636002,
    fullRecordGapCenterValue + 636062,
    fullRecordGapCenterValue + 636078,
    fullRecordGapCenterValue + 636146,
    fullRecordGapCenterValue + 636186,
    fullRecordGapCenterValue + 636248,
    fullRecordGapCenterValue + 636392,
    fullRecordGapCenterValue + 636422,
    fullRecordGapCenterValue + 636458,
    fullRecordGapCenterValue + 636476,
    fullRecordGapCenterValue + 636578,
    fullRecordGapCenterValue + 636612,
    fullRecordGapCenterValue + 636668,
    fullRecordGapCenterValue + 636710,
    fullRecordGapCenterValue + 636806,
    fullRecordGapCenterValue + 636836,
    fullRecordGapCenterValue + 636932,
    fullRecordGapCenterValue + 637016,
    fullRecordGapCenterValue + 637068,
    fullRecordGapCenterValue + 637122,
    fullRecordGapCenterValue + 637148,
    fullRecordGapCenterValue + 637172,
    fullRecordGapCenterValue + 637178,
    fullRecordGapCenterValue + 637256,
    fullRecordGapCenterValue + 637278,
    fullRecordGapCenterValue + 637302,
    fullRecordGapCenterValue + 637322,
    fullRecordGapCenterValue + 637382,
    fullRecordGapCenterValue + 637430,
    fullRecordGapCenterValue + 637458,
    fullRecordGapCenterValue + 637548,
    fullRecordGapCenterValue + 637610,
    fullRecordGapCenterValue + 637646,
    fullRecordGapCenterValue + 637682,
    fullRecordGapCenterValue + 637742,
    fullRecordGapCenterValue + 637766,
    fullRecordGapCenterValue + 637788,
    fullRecordGapCenterValue + 637926,
    fullRecordGapCenterValue + 638090,
    fullRecordGapCenterValue + 638178,
    fullRecordGapCenterValue + 638186,
    fullRecordGapCenterValue + 638246,
    fullRecordGapCenterValue + 638382,
    fullRecordGapCenterValue + 638412,
    fullRecordGapCenterValue + 638466,
    fullRecordGapCenterValue + 638468,
    fullRecordGapCenterValue + 638516,
    fullRecordGapCenterValue + 638562,
    fullRecordGapCenterValue + 638582,
    fullRecordGapCenterValue + 638598,
    fullRecordGapCenterValue + 638772,
    fullRecordGapCenterValue + 638880,
    fullRecordGapCenterValue + 638888,
    fullRecordGapCenterValue + 638906,
    fullRecordGapCenterValue + 638936,
    fullRecordGapCenterValue + 638948,
    fullRecordGapCenterValue + 639038,
    fullRecordGapCenterValue + 639278,
    fullRecordGapCenterValue + 639332,
    fullRecordGapCenterValue + 639348,
    fullRecordGapCenterValue + 639362,
    fullRecordGapCenterValue + 639458,
    fullRecordGapCenterValue + 639546,
    fullRecordGapCenterValue + 639588,
    fullRecordGapCenterValue + 639758,
    fullRecordGapCenterValue + 639942,
    fullRecordGapCenterValue + 639986,
    fullRecordGapCenterValue + 640070,
    fullRecordGapCenterValue + 640076,
    fullRecordGapCenterValue + 640106,
    fullRecordGapCenterValue + 640308,
    fullRecordGapCenterValue + 640316,
    fullRecordGapCenterValue + 640332,
    fullRecordGapCenterValue + 640362,
    fullRecordGapCenterValue + 640418,
    fullRecordGapCenterValue + 640572,
    fullRecordGapCenterValue + 640652,
    fullRecordGapCenterValue + 640682,
    fullRecordGapCenterValue + 640806,
    fullRecordGapCenterValue + 640862,
    fullRecordGapCenterValue + 640868,
    fullRecordGapCenterValue + 640938,
    fullRecordGapCenterValue + 641028,
    fullRecordGapCenterValue + 641042,
    fullRecordGapCenterValue + 641090,
    fullRecordGapCenterValue + 641126,
    fullRecordGapCenterValue + 641166,
    fullRecordGapCenterValue + 641202,
    fullRecordGapCenterValue + 641222,
    fullRecordGapCenterValue + 641226,
    fullRecordGapCenterValue + 641372,
    fullRecordGapCenterValue + 641442,
    fullRecordGapCenterValue + 641492,
    fullRecordGapCenterValue + 641522,
    fullRecordGapCenterValue + 641588,
    fullRecordGapCenterValue + 641636,
    fullRecordGapCenterValue + 641672,
    fullRecordGapCenterValue + 641678,
    fullRecordGapCenterValue + 642036,
    fullRecordGapCenterValue + 642126,
    fullRecordGapCenterValue + 642146,
    fullRecordGapCenterValue + 642338,
    fullRecordGapCenterValue + 642398,
    fullRecordGapCenterValue + 642548,
    fullRecordGapCenterValue + 642588,
    fullRecordGapCenterValue + 642596,
    fullRecordGapCenterValue + 642612,
    fullRecordGapCenterValue + 642626,
    fullRecordGapCenterValue + 642632,
    fullRecordGapCenterValue + 642710,
    fullRecordGapCenterValue + 642738,
    fullRecordGapCenterValue + 642806,
    fullRecordGapCenterValue + 642822,
    fullRecordGapCenterValue + 642938,
    fullRecordGapCenterValue + 642978,
    fullRecordGapCenterValue + 643028,
    fullRecordGapCenterValue + 643092,
    fullRecordGapCenterValue + 643098,
    fullRecordGapCenterValue + 643106,
    fullRecordGapCenterValue + 643116,
    fullRecordGapCenterValue + 643142,
    fullRecordGapCenterValue + 643182,
    fullRecordGapCenterValue + 643190,
    fullRecordGapCenterValue + 643202,
    fullRecordGapCenterValue + 643262,
    fullRecordGapCenterValue + 643268,
    fullRecordGapCenterValue + 643308,
    fullRecordGapCenterValue + 643316,
    fullRecordGapCenterValue + 643322,
    fullRecordGapCenterValue + 643332,
    fullRecordGapCenterValue + 643458,
    fullRecordGapCenterValue + 643508,
    fullRecordGapCenterValue + 643532,
    fullRecordGapCenterValue + 643592,
    fullRecordGapCenterValue + 643638,
    fullRecordGapCenterValue + 643668,
    fullRecordGapCenterValue + 643730,
    fullRecordGapCenterValue + 643778,
    fullRecordGapCenterValue + 643802,
    fullRecordGapCenterValue + 643868,
    fullRecordGapCenterValue + 643898,
    fullRecordGapCenterValue + 644018,
    fullRecordGapCenterValue + 644030,
    fullRecordGapCenterValue + 644036,
    fullRecordGapCenterValue + 644078,
    fullRecordGapCenterValue + 644186,
    fullRecordGapCenterValue + 644316,
    fullRecordGapCenterValue + 644348,
    fullRecordGapCenterValue + 644388,
    fullRecordGapCenterValue + 644390,
    fullRecordGapCenterValue + 644498,
    fullRecordGapCenterValue + 644702,
    fullRecordGapCenterValue + 644718,
    fullRecordGapCenterValue + 644792,
    fullRecordGapCenterValue + 644918,
    fullRecordGapCenterValue + 645002,
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
theorem fullRecordGapRow00042_fermat : ∀ n ∈ fullRecordGapRow00042_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10497_not_prime : ¬(recordGapCenter + 633638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633638]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10498_not_prime : ¬(recordGapCenter + 633756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633756]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10499_not_prime : ¬(recordGapCenter + 633848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633848]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10500_not_prime : ¬(recordGapCenter + 634076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634076]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10501_not_prime : ¬(recordGapCenter + 634232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634232]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10502_not_prime : ¬(recordGapCenter + 634268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634268]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10503_not_prime : ¬(recordGapCenter + 634298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634298]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10504_not_prime : ¬(recordGapCenter + 634308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634308]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10505_not_prime : ¬(recordGapCenter + 634398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634398]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10506_not_prime : ¬(recordGapCenter + 634548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634548]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10507_not_prime : ¬(recordGapCenter + 634596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634596]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10508_not_prime : ¬(recordGapCenter + 634646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634646]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10509_not_prime : ¬(recordGapCenter + 634706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634706]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10510_not_prime : ¬(recordGapCenter + 634730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634730]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10511_not_prime : ¬(recordGapCenter + 634742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634742]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10512_not_prime : ¬(recordGapCenter + 634802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634802]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10513_not_prime : ¬(recordGapCenter + 634812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634812]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10514_not_prime : ¬(recordGapCenter + 634902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634902]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10515_not_prime : ¬(recordGapCenter + 635040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635040]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10516_not_prime : ¬(recordGapCenter + 635078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635078]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10517_not_prime : ¬(recordGapCenter + 635108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635108]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10518_not_prime : ¬(recordGapCenter + 635178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635178]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10519_not_prime : ¬(recordGapCenter + 635192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635192]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10520_not_prime : ¬(recordGapCenter + 635198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635198]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10521_not_prime : ¬(recordGapCenter + 635372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635372]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10522_not_prime : ¬(recordGapCenter + 635402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635402]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10523_not_prime : ¬(recordGapCenter + 635468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635468]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10524_not_prime : ¬(recordGapCenter + 635556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635556]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10525_not_prime : ¬(recordGapCenter + 635636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635636]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10526_not_prime : ¬(recordGapCenter + 635678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635678]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10527_not_prime : ¬(recordGapCenter + 635772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635772]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10528_not_prime : ¬(recordGapCenter + 635870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635870]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10529_not_prime : ¬(recordGapCenter + 635898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635898]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10530_not_prime : ¬(recordGapCenter + 635918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635918]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10531_not_prime : ¬(recordGapCenter + 635978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635978]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10532_not_prime : ¬(recordGapCenter + 635982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635982]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10533_not_prime : ¬(recordGapCenter + 635988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635988]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10534_not_prime : ¬(recordGapCenter + 636002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636002]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10535_not_prime : ¬(recordGapCenter + 636062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636062]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10536_not_prime : ¬(recordGapCenter + 636078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636078]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10537_not_prime : ¬(recordGapCenter + 636146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636146]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10538_not_prime : ¬(recordGapCenter + 636186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636186]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10539_not_prime : ¬(recordGapCenter + 636248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636248]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10540_not_prime : ¬(recordGapCenter + 636392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636392]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10541_not_prime : ¬(recordGapCenter + 636422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636422]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10542_not_prime : ¬(recordGapCenter + 636458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636458]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10543_not_prime : ¬(recordGapCenter + 636476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636476]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10544_not_prime : ¬(recordGapCenter + 636578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636578]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10545_not_prime : ¬(recordGapCenter + 636612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636612]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10546_not_prime : ¬(recordGapCenter + 636668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636668]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10547_not_prime : ¬(recordGapCenter + 636710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636710]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10548_not_prime : ¬(recordGapCenter + 636806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636806]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10549_not_prime : ¬(recordGapCenter + 636836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636836]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10550_not_prime : ¬(recordGapCenter + 636932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636932]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10551_not_prime : ¬(recordGapCenter + 637016).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637016]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10552_not_prime : ¬(recordGapCenter + 637068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637068]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10553_not_prime : ¬(recordGapCenter + 637122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637122]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10554_not_prime : ¬(recordGapCenter + 637148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637148]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10555_not_prime : ¬(recordGapCenter + 637172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637172]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10556_not_prime : ¬(recordGapCenter + 637178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637178]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10557_not_prime : ¬(recordGapCenter + 637256).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637256]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10558_not_prime : ¬(recordGapCenter + 637278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637278]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10559_not_prime : ¬(recordGapCenter + 637302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637302]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10560_not_prime : ¬(recordGapCenter + 637322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637322]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10561_not_prime : ¬(recordGapCenter + 637382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637382]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10562_not_prime : ¬(recordGapCenter + 637430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637430]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10563_not_prime : ¬(recordGapCenter + 637458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637458]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10564_not_prime : ¬(recordGapCenter + 637548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637548]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10565_not_prime : ¬(recordGapCenter + 637610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637610]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10566_not_prime : ¬(recordGapCenter + 637646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637646]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10567_not_prime : ¬(recordGapCenter + 637682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637682]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10568_not_prime : ¬(recordGapCenter + 637742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637742]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10569_not_prime : ¬(recordGapCenter + 637766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637766]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10570_not_prime : ¬(recordGapCenter + 637788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637788]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10571_not_prime : ¬(recordGapCenter + 637926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637926]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10572_not_prime : ¬(recordGapCenter + 638090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638090]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10573_not_prime : ¬(recordGapCenter + 638178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638178]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10574_not_prime : ¬(recordGapCenter + 638186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638186]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10575_not_prime : ¬(recordGapCenter + 638246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638246]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10576_not_prime : ¬(recordGapCenter + 638382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638382]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10577_not_prime : ¬(recordGapCenter + 638412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638412]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10578_not_prime : ¬(recordGapCenter + 638466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638466]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10579_not_prime : ¬(recordGapCenter + 638468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638468]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10580_not_prime : ¬(recordGapCenter + 638516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638516]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10581_not_prime : ¬(recordGapCenter + 638562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638562]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10582_not_prime : ¬(recordGapCenter + 638582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638582]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10583_not_prime : ¬(recordGapCenter + 638598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638598]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10584_not_prime : ¬(recordGapCenter + 638772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638772]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10585_not_prime : ¬(recordGapCenter + 638880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638880]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10586_not_prime : ¬(recordGapCenter + 638888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638888]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10587_not_prime : ¬(recordGapCenter + 638906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638906]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10588_not_prime : ¬(recordGapCenter + 638936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638936]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10589_not_prime : ¬(recordGapCenter + 638948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638948]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10590_not_prime : ¬(recordGapCenter + 639038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639038]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10591_not_prime : ¬(recordGapCenter + 639278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639278]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10592_not_prime : ¬(recordGapCenter + 639332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639332]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10593_not_prime : ¬(recordGapCenter + 639348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639348]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10594_not_prime : ¬(recordGapCenter + 639362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639362]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10595_not_prime : ¬(recordGapCenter + 639458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639458]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10596_not_prime : ¬(recordGapCenter + 639546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639546]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10597_not_prime : ¬(recordGapCenter + 639588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639588]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10598_not_prime : ¬(recordGapCenter + 639758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639758]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10599_not_prime : ¬(recordGapCenter + 639942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639942]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10600_not_prime : ¬(recordGapCenter + 639986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639986]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10601_not_prime : ¬(recordGapCenter + 640070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640070]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10602_not_prime : ¬(recordGapCenter + 640076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640076]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10603_not_prime : ¬(recordGapCenter + 640106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640106]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10604_not_prime : ¬(recordGapCenter + 640308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640308]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10605_not_prime : ¬(recordGapCenter + 640316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640316]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10606_not_prime : ¬(recordGapCenter + 640332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640332]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10607_not_prime : ¬(recordGapCenter + 640362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640362]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10608_not_prime : ¬(recordGapCenter + 640418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640418]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10609_not_prime : ¬(recordGapCenter + 640572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640572]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10610_not_prime : ¬(recordGapCenter + 640652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640652]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10611_not_prime : ¬(recordGapCenter + 640682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640682]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10612_not_prime : ¬(recordGapCenter + 640806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640806]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10613_not_prime : ¬(recordGapCenter + 640862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640862]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10614_not_prime : ¬(recordGapCenter + 640868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640868]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10615_not_prime : ¬(recordGapCenter + 640938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640938]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10616_not_prime : ¬(recordGapCenter + 641028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641028]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10617_not_prime : ¬(recordGapCenter + 641042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641042]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10618_not_prime : ¬(recordGapCenter + 641090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641090]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10619_not_prime : ¬(recordGapCenter + 641126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641126]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10620_not_prime : ¬(recordGapCenter + 641166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641166]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10621_not_prime : ¬(recordGapCenter + 641202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641202]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10622_not_prime : ¬(recordGapCenter + 641222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641222]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10623_not_prime : ¬(recordGapCenter + 641226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641226]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10624_not_prime : ¬(recordGapCenter + 641372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641372]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10625_not_prime : ¬(recordGapCenter + 641442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641442]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10626_not_prime : ¬(recordGapCenter + 641492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641492]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10627_not_prime : ¬(recordGapCenter + 641522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641522]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10628_not_prime : ¬(recordGapCenter + 641588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641588]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10629_not_prime : ¬(recordGapCenter + 641636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641636]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10630_not_prime : ¬(recordGapCenter + 641672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641672]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10631_not_prime : ¬(recordGapCenter + 641678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641678]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10632_not_prime : ¬(recordGapCenter + 642036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642036]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10633_not_prime : ¬(recordGapCenter + 642126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642126]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10634_not_prime : ¬(recordGapCenter + 642146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642146]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10635_not_prime : ¬(recordGapCenter + 642338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642338]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10636_not_prime : ¬(recordGapCenter + 642398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642398]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10637_not_prime : ¬(recordGapCenter + 642548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642548]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10638_not_prime : ¬(recordGapCenter + 642588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642588]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10639_not_prime : ¬(recordGapCenter + 642596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642596]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10640_not_prime : ¬(recordGapCenter + 642612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642612]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10641_not_prime : ¬(recordGapCenter + 642626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642626]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10642_not_prime : ¬(recordGapCenter + 642632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642632]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10643_not_prime : ¬(recordGapCenter + 642710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642710]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10644_not_prime : ¬(recordGapCenter + 642738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642738]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10645_not_prime : ¬(recordGapCenter + 642806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642806]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10646_not_prime : ¬(recordGapCenter + 642822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642822]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10647_not_prime : ¬(recordGapCenter + 642938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642938]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10648_not_prime : ¬(recordGapCenter + 642978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642978]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10649_not_prime : ¬(recordGapCenter + 643028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643028]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10650_not_prime : ¬(recordGapCenter + 643092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643092]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10651_not_prime : ¬(recordGapCenter + 643098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643098]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10652_not_prime : ¬(recordGapCenter + 643106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643106]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10653_not_prime : ¬(recordGapCenter + 643116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643116]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10654_not_prime : ¬(recordGapCenter + 643142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643142]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10655_not_prime : ¬(recordGapCenter + 643182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643182]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10656_not_prime : ¬(recordGapCenter + 643190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643190]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10657_not_prime : ¬(recordGapCenter + 643202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643202]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10658_not_prime : ¬(recordGapCenter + 643262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643262]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10659_not_prime : ¬(recordGapCenter + 643268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643268]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10660_not_prime : ¬(recordGapCenter + 643308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643308]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10661_not_prime : ¬(recordGapCenter + 643316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643316]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10662_not_prime : ¬(recordGapCenter + 643322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643322]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10663_not_prime : ¬(recordGapCenter + 643332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643332]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10664_not_prime : ¬(recordGapCenter + 643458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643458]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10665_not_prime : ¬(recordGapCenter + 643508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643508]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10666_not_prime : ¬(recordGapCenter + 643532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643532]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10667_not_prime : ¬(recordGapCenter + 643592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643592]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10668_not_prime : ¬(recordGapCenter + 643638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643638]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10669_not_prime : ¬(recordGapCenter + 643668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643668]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10670_not_prime : ¬(recordGapCenter + 643730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643730]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10671_not_prime : ¬(recordGapCenter + 643778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643778]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10672_not_prime : ¬(recordGapCenter + 643802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643802]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10673_not_prime : ¬(recordGapCenter + 643868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643868]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10674_not_prime : ¬(recordGapCenter + 643898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643898]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10675_not_prime : ¬(recordGapCenter + 644018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644018]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10676_not_prime : ¬(recordGapCenter + 644030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644030]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10677_not_prime : ¬(recordGapCenter + 644036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644036]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10678_not_prime : ¬(recordGapCenter + 644078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644078]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10679_not_prime : ¬(recordGapCenter + 644186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644186]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10680_not_prime : ¬(recordGapCenter + 644316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644316]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10681_not_prime : ¬(recordGapCenter + 644348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644348]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10682_not_prime : ¬(recordGapCenter + 644388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644388]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10683_not_prime : ¬(recordGapCenter + 644390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644390]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10684_not_prime : ¬(recordGapCenter + 644498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644498]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10685_not_prime : ¬(recordGapCenter + 644702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644702]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10686_not_prime : ¬(recordGapCenter + 644718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644718]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10687_not_prime : ¬(recordGapCenter + 644792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644792]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10688_not_prime : ¬(recordGapCenter + 644918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644918]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10689_not_prime : ¬(recordGapCenter + 645002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645002]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10690_not_prime : ¬(recordGapCenter + 645032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645032]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10691_not_prime : ¬(recordGapCenter + 645038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645038]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10692_not_prime : ¬(recordGapCenter + 645108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645108]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10693_not_prime : ¬(recordGapCenter + 645120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645120]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10694_not_prime : ¬(recordGapCenter + 645332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645332]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10695_not_prime : ¬(recordGapCenter + 645338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645338]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10696_not_prime : ¬(recordGapCenter + 645356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645356]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10697_not_prime : ¬(recordGapCenter + 645368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645368]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10698_not_prime : ¬(recordGapCenter + 645416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645416]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10699_not_prime : ¬(recordGapCenter + 645486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645486]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10700_not_prime : ¬(recordGapCenter + 645492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645492]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10701_not_prime : ¬(recordGapCenter + 645530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645530]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10702_not_prime : ¬(recordGapCenter + 645782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645782]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10703_not_prime : ¬(recordGapCenter + 645846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645846]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10704_not_prime : ¬(recordGapCenter + 645878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645878]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10705_not_prime : ¬(recordGapCenter + 645972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 645972]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10706_not_prime : ¬(recordGapCenter + 646010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646010]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10707_not_prime : ¬(recordGapCenter + 646088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646088]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10708_not_prime : ¬(recordGapCenter + 646172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646172]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10709_not_prime : ¬(recordGapCenter + 646188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646188]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10710_not_prime : ¬(recordGapCenter + 646278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646278]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10711_not_prime : ¬(recordGapCenter + 646292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646292]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10712_not_prime : ¬(recordGapCenter + 646446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646446]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10713_not_prime : ¬(recordGapCenter + 646482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646482]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10714_not_prime : ¬(recordGapCenter + 646502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646502]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10715_not_prime : ¬(recordGapCenter + 646508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646508]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10716_not_prime : ¬(recordGapCenter + 646572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646572]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10717_not_prime : ¬(recordGapCenter + 646662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646662]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10718_not_prime : ¬(recordGapCenter + 646682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646682]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10719_not_prime : ¬(recordGapCenter + 646692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646692]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10720_not_prime : ¬(recordGapCenter + 646718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646718]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10721_not_prime : ¬(recordGapCenter + 646788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646788]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10722_not_prime : ¬(recordGapCenter + 646826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646826]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10723_not_prime : ¬(recordGapCenter + 646838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646838]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10724_not_prime : ¬(recordGapCenter + 646886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 646886]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10725_not_prime : ¬(recordGapCenter + 647066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647066]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10726_not_prime : ¬(recordGapCenter + 647132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647132]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10727_not_prime : ¬(recordGapCenter + 647238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647238]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10728_not_prime : ¬(recordGapCenter + 647246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647246]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10729_not_prime : ¬(recordGapCenter + 647286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647286]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10730_not_prime : ¬(recordGapCenter + 647288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647288]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10731_not_prime : ¬(recordGapCenter + 647318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647318]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10732_not_prime : ¬(recordGapCenter + 647336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647336]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10733_not_prime : ¬(recordGapCenter + 647382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647382]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10734_not_prime : ¬(recordGapCenter + 647418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647418]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10735_not_prime : ¬(recordGapCenter + 647432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647432]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10736_not_prime : ¬(recordGapCenter + 647538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647538]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10737_not_prime : ¬(recordGapCenter + 647606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647606]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10738_not_prime : ¬(recordGapCenter + 647798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647798]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10739_not_prime : ¬(recordGapCenter + 647826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647826]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10740_not_prime : ¬(recordGapCenter + 647846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647846]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10741_not_prime : ¬(recordGapCenter + 647916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647916]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10742_not_prime : ¬(recordGapCenter + 647930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 647930]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10743_not_prime : ¬(recordGapCenter + 648000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648000]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10744_not_prime : ¬(recordGapCenter + 648012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648012]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10745_not_prime : ¬(recordGapCenter + 648152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648152]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10746_not_prime : ¬(recordGapCenter + 648236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648236]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10747_not_prime : ¬(recordGapCenter + 648302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648302]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10748_not_prime : ¬(recordGapCenter + 648326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648326]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10749_not_prime : ¬(recordGapCenter + 648422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648422]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10750_not_prime : ¬(recordGapCenter + 648476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648476]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10751_not_prime : ¬(recordGapCenter + 648530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648530]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm10752_not_prime : ¬(recordGapCenter + 648588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648588]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

end PrimeFactorUnimodality
