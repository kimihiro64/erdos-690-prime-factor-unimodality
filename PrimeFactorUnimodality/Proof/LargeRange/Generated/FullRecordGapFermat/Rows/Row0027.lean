import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00027_values : List Nat :=
  [fullRecordGapCenterValue + 368582,
    fullRecordGapCenterValue + 368618,
    fullRecordGapCenterValue + 368642,
    fullRecordGapCenterValue + 368666,
    fullRecordGapCenterValue + 368898,
    fullRecordGapCenterValue + 368972,
    fullRecordGapCenterValue + 369128,
    fullRecordGapCenterValue + 369218,
    fullRecordGapCenterValue + 369302,
    fullRecordGapCenterValue + 369428,
    fullRecordGapCenterValue + 369476,
    fullRecordGapCenterValue + 369506,
    fullRecordGapCenterValue + 369752,
    fullRecordGapCenterValue + 369758,
    fullRecordGapCenterValue + 369906,
    fullRecordGapCenterValue + 369986,
    fullRecordGapCenterValue + 370002,
    fullRecordGapCenterValue + 370086,
    fullRecordGapCenterValue + 370088,
    fullRecordGapCenterValue + 370122,
    fullRecordGapCenterValue + 370232,
    fullRecordGapCenterValue + 370262,
    fullRecordGapCenterValue + 370338,
    fullRecordGapCenterValue + 370472,
    fullRecordGapCenterValue + 370506,
    fullRecordGapCenterValue + 370598,
    fullRecordGapCenterValue + 370646,
    fullRecordGapCenterValue + 370676,
    fullRecordGapCenterValue + 370686,
    fullRecordGapCenterValue + 370742,
    fullRecordGapCenterValue + 370802,
    fullRecordGapCenterValue + 370868,
    fullRecordGapCenterValue + 370892,
    fullRecordGapCenterValue + 371012,
    fullRecordGapCenterValue + 371058,
    fullRecordGapCenterValue + 371066,
    fullRecordGapCenterValue + 371250,
    fullRecordGapCenterValue + 371288,
    fullRecordGapCenterValue + 371366,
    fullRecordGapCenterValue + 371498,
    fullRecordGapCenterValue + 371528,
    fullRecordGapCenterValue + 371666,
    fullRecordGapCenterValue + 371738,
    fullRecordGapCenterValue + 371886,
    fullRecordGapCenterValue + 371946,
    fullRecordGapCenterValue + 372282,
    fullRecordGapCenterValue + 372332,
    fullRecordGapCenterValue + 372342,
    fullRecordGapCenterValue + 372426,
    fullRecordGapCenterValue + 372486,
    fullRecordGapCenterValue + 372536,
    fullRecordGapCenterValue + 372542,
    fullRecordGapCenterValue + 372680,
    fullRecordGapCenterValue + 372782,
    fullRecordGapCenterValue + 372822,
    fullRecordGapCenterValue + 372858,
    fullRecordGapCenterValue + 372902,
    fullRecordGapCenterValue + 372956,
    fullRecordGapCenterValue + 373026,
    fullRecordGapCenterValue + 373052,
    fullRecordGapCenterValue + 373112,
    fullRecordGapCenterValue + 373146,
    fullRecordGapCenterValue + 373206,
    fullRecordGapCenterValue + 373238,
    fullRecordGapCenterValue + 373242,
    fullRecordGapCenterValue + 373278,
    fullRecordGapCenterValue + 373448,
    fullRecordGapCenterValue + 373508,
    fullRecordGapCenterValue + 373532,
    fullRecordGapCenterValue + 373586,
    fullRecordGapCenterValue + 373628,
    fullRecordGapCenterValue + 373676,
    fullRecordGapCenterValue + 373718,
    fullRecordGapCenterValue + 373766,
    fullRecordGapCenterValue + 373866,
    fullRecordGapCenterValue + 373938,
    fullRecordGapCenterValue + 373962,
    fullRecordGapCenterValue + 374082,
    fullRecordGapCenterValue + 374138,
    fullRecordGapCenterValue + 374162,
    fullRecordGapCenterValue + 374222,
    fullRecordGapCenterValue + 374228,
    fullRecordGapCenterValue + 374246,
    fullRecordGapCenterValue + 374298,
    fullRecordGapCenterValue + 374406,
    fullRecordGapCenterValue + 374456,
    fullRecordGapCenterValue + 374732,
    fullRecordGapCenterValue + 374862,
    fullRecordGapCenterValue + 374936,
    fullRecordGapCenterValue + 375006,
    fullRecordGapCenterValue + 375026,
    fullRecordGapCenterValue + 375236,
    fullRecordGapCenterValue + 375302,
    fullRecordGapCenterValue + 375546,
    fullRecordGapCenterValue + 375548,
    fullRecordGapCenterValue + 375656,
    fullRecordGapCenterValue + 375722,
    fullRecordGapCenterValue + 375798,
    fullRecordGapCenterValue + 375842,
    fullRecordGapCenterValue + 375902,
    fullRecordGapCenterValue + 376098,
    fullRecordGapCenterValue + 376122,
    fullRecordGapCenterValue + 376136,
    fullRecordGapCenterValue + 376338,
    fullRecordGapCenterValue + 376358,
    fullRecordGapCenterValue + 376386,
    fullRecordGapCenterValue + 376458,
    fullRecordGapCenterValue + 376472,
    fullRecordGapCenterValue + 376518,
    fullRecordGapCenterValue + 376622,
    fullRecordGapCenterValue + 376638,
    fullRecordGapCenterValue + 376646,
    fullRecordGapCenterValue + 376806,
    fullRecordGapCenterValue + 376862,
    fullRecordGapCenterValue + 377066,
    fullRecordGapCenterValue + 377106,
    fullRecordGapCenterValue + 377300,
    fullRecordGapCenterValue + 377372,
    fullRecordGapCenterValue + 377382,
    fullRecordGapCenterValue + 377402,
    fullRecordGapCenterValue + 377438,
    fullRecordGapCenterValue + 377588,
    fullRecordGapCenterValue + 377708,
    fullRecordGapCenterValue + 377738,
    fullRecordGapCenterValue + 377756,
    fullRecordGapCenterValue + 377822,
    fullRecordGapCenterValue + 377826,
    fullRecordGapCenterValue + 377898,
    fullRecordGapCenterValue + 377906,
    fullRecordGapCenterValue + 377966,
    fullRecordGapCenterValue + 378008,
    fullRecordGapCenterValue + 378038,
    fullRecordGapCenterValue + 378086,
    fullRecordGapCenterValue + 378278,
    fullRecordGapCenterValue + 378296,
    fullRecordGapCenterValue + 378402,
    fullRecordGapCenterValue + 378438,
    fullRecordGapCenterValue + 378458,
    fullRecordGapCenterValue + 378536,
    fullRecordGapCenterValue + 378542,
    fullRecordGapCenterValue + 378582,
    fullRecordGapCenterValue + 378722,
    fullRecordGapCenterValue + 378786,
    fullRecordGapCenterValue + 378866,
    fullRecordGapCenterValue + 378878,
    fullRecordGapCenterValue + 378908,
    fullRecordGapCenterValue + 378926,
    fullRecordGapCenterValue + 379058,
    fullRecordGapCenterValue + 379172,
    fullRecordGapCenterValue + 379292,
    fullRecordGapCenterValue + 379352,
    fullRecordGapCenterValue + 379388,
    fullRecordGapCenterValue + 379446,
    fullRecordGapCenterValue + 379466,
    fullRecordGapCenterValue + 379598,
    fullRecordGapCenterValue + 379646,
    fullRecordGapCenterValue + 379718,
    fullRecordGapCenterValue + 379878,
    fullRecordGapCenterValue + 379902,
    fullRecordGapCenterValue + 379928,
    fullRecordGapCenterValue + 380012,
    fullRecordGapCenterValue + 380126,
    fullRecordGapCenterValue + 380168,
    fullRecordGapCenterValue + 380186,
    fullRecordGapCenterValue + 380252,
    fullRecordGapCenterValue + 380258,
    fullRecordGapCenterValue + 380348,
    fullRecordGapCenterValue + 380642,
    fullRecordGapCenterValue + 380648,
    fullRecordGapCenterValue + 380852,
    fullRecordGapCenterValue + 380958,
    fullRecordGapCenterValue + 381032,
    fullRecordGapCenterValue + 381068,
    fullRecordGapCenterValue + 381126,
    fullRecordGapCenterValue + 381246,
    fullRecordGapCenterValue + 381272,
    fullRecordGapCenterValue + 381308,
    fullRecordGapCenterValue + 381356,
    fullRecordGapCenterValue + 381522,
    fullRecordGapCenterValue + 381566,
    fullRecordGapCenterValue + 381572,
    fullRecordGapCenterValue + 381606,
    fullRecordGapCenterValue + 381782,
    fullRecordGapCenterValue + 381882,
    fullRecordGapCenterValue + 381896,
    fullRecordGapCenterValue + 382002,
    fullRecordGapCenterValue + 382142,
    fullRecordGapCenterValue + 382218,
    fullRecordGapCenterValue + 382232,
    fullRecordGapCenterValue + 382238,
    fullRecordGapCenterValue + 382286,
    fullRecordGapCenterValue + 382362,
    fullRecordGapCenterValue + 382566,
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
theorem fullRecordGapRow00027_fermat : ∀ n ∈ fullRecordGapRow00027_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06657_not_prime : ¬(recordGapCenter + 368582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368582]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06658_not_prime : ¬(recordGapCenter + 368618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368618]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06659_not_prime : ¬(recordGapCenter + 368642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368642]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06660_not_prime : ¬(recordGapCenter + 368666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368666]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06661_not_prime : ¬(recordGapCenter + 368898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368898]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06662_not_prime : ¬(recordGapCenter + 368972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368972]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06663_not_prime : ¬(recordGapCenter + 369128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369128]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06664_not_prime : ¬(recordGapCenter + 369218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369218]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06665_not_prime : ¬(recordGapCenter + 369302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369302]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06666_not_prime : ¬(recordGapCenter + 369428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369428]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06667_not_prime : ¬(recordGapCenter + 369476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369476]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06668_not_prime : ¬(recordGapCenter + 369506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369506]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06669_not_prime : ¬(recordGapCenter + 369752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369752]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06670_not_prime : ¬(recordGapCenter + 369758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369758]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06671_not_prime : ¬(recordGapCenter + 369906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369906]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06672_not_prime : ¬(recordGapCenter + 369986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369986]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06673_not_prime : ¬(recordGapCenter + 370002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370002]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06674_not_prime : ¬(recordGapCenter + 370086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370086]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06675_not_prime : ¬(recordGapCenter + 370088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370088]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06676_not_prime : ¬(recordGapCenter + 370122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370122]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06677_not_prime : ¬(recordGapCenter + 370232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370232]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06678_not_prime : ¬(recordGapCenter + 370262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370262]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06679_not_prime : ¬(recordGapCenter + 370338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370338]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06680_not_prime : ¬(recordGapCenter + 370472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370472]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06681_not_prime : ¬(recordGapCenter + 370506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370506]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06682_not_prime : ¬(recordGapCenter + 370598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370598]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06683_not_prime : ¬(recordGapCenter + 370646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370646]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06684_not_prime : ¬(recordGapCenter + 370676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370676]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06685_not_prime : ¬(recordGapCenter + 370686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370686]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06686_not_prime : ¬(recordGapCenter + 370742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370742]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06687_not_prime : ¬(recordGapCenter + 370802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370802]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06688_not_prime : ¬(recordGapCenter + 370868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370868]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06689_not_prime : ¬(recordGapCenter + 370892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370892]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06690_not_prime : ¬(recordGapCenter + 371012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371012]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06691_not_prime : ¬(recordGapCenter + 371058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371058]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06692_not_prime : ¬(recordGapCenter + 371066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371066]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06693_not_prime : ¬(recordGapCenter + 371250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371250]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06694_not_prime : ¬(recordGapCenter + 371288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371288]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06695_not_prime : ¬(recordGapCenter + 371366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371366]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06696_not_prime : ¬(recordGapCenter + 371498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371498]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06697_not_prime : ¬(recordGapCenter + 371528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371528]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06698_not_prime : ¬(recordGapCenter + 371666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371666]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06699_not_prime : ¬(recordGapCenter + 371738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371738]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06700_not_prime : ¬(recordGapCenter + 371886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371886]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06701_not_prime : ¬(recordGapCenter + 371946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371946]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06702_not_prime : ¬(recordGapCenter + 372282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372282]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06703_not_prime : ¬(recordGapCenter + 372332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372332]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06704_not_prime : ¬(recordGapCenter + 372342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372342]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06705_not_prime : ¬(recordGapCenter + 372426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372426]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06706_not_prime : ¬(recordGapCenter + 372486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372486]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06707_not_prime : ¬(recordGapCenter + 372536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372536]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06708_not_prime : ¬(recordGapCenter + 372542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372542]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06709_not_prime : ¬(recordGapCenter + 372680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372680]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06710_not_prime : ¬(recordGapCenter + 372782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372782]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06711_not_prime : ¬(recordGapCenter + 372822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372822]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06712_not_prime : ¬(recordGapCenter + 372858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372858]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06713_not_prime : ¬(recordGapCenter + 372902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372902]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06714_not_prime : ¬(recordGapCenter + 372956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372956]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06715_not_prime : ¬(recordGapCenter + 373026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373026]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06716_not_prime : ¬(recordGapCenter + 373052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373052]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06717_not_prime : ¬(recordGapCenter + 373112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373112]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06718_not_prime : ¬(recordGapCenter + 373146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373146]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06719_not_prime : ¬(recordGapCenter + 373206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373206]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06720_not_prime : ¬(recordGapCenter + 373238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373238]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06721_not_prime : ¬(recordGapCenter + 373242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373242]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06722_not_prime : ¬(recordGapCenter + 373278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373278]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06723_not_prime : ¬(recordGapCenter + 373448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373448]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06724_not_prime : ¬(recordGapCenter + 373508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373508]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06725_not_prime : ¬(recordGapCenter + 373532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373532]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06726_not_prime : ¬(recordGapCenter + 373586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373586]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06727_not_prime : ¬(recordGapCenter + 373628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373628]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06728_not_prime : ¬(recordGapCenter + 373676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373676]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06729_not_prime : ¬(recordGapCenter + 373718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373718]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06730_not_prime : ¬(recordGapCenter + 373766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373766]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06731_not_prime : ¬(recordGapCenter + 373866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373866]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06732_not_prime : ¬(recordGapCenter + 373938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373938]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06733_not_prime : ¬(recordGapCenter + 373962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373962]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06734_not_prime : ¬(recordGapCenter + 374082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374082]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06735_not_prime : ¬(recordGapCenter + 374138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374138]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06736_not_prime : ¬(recordGapCenter + 374162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374162]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06737_not_prime : ¬(recordGapCenter + 374222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374222]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06738_not_prime : ¬(recordGapCenter + 374228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374228]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06739_not_prime : ¬(recordGapCenter + 374246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374246]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06740_not_prime : ¬(recordGapCenter + 374298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374298]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06741_not_prime : ¬(recordGapCenter + 374406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374406]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06742_not_prime : ¬(recordGapCenter + 374456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374456]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06743_not_prime : ¬(recordGapCenter + 374732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374732]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06744_not_prime : ¬(recordGapCenter + 374862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374862]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06745_not_prime : ¬(recordGapCenter + 374936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 374936]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06746_not_prime : ¬(recordGapCenter + 375006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375006]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06747_not_prime : ¬(recordGapCenter + 375026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375026]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06748_not_prime : ¬(recordGapCenter + 375236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375236]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06749_not_prime : ¬(recordGapCenter + 375302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375302]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06750_not_prime : ¬(recordGapCenter + 375546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375546]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06751_not_prime : ¬(recordGapCenter + 375548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375548]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06752_not_prime : ¬(recordGapCenter + 375656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375656]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06753_not_prime : ¬(recordGapCenter + 375722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375722]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06754_not_prime : ¬(recordGapCenter + 375798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375798]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06755_not_prime : ¬(recordGapCenter + 375842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375842]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06756_not_prime : ¬(recordGapCenter + 375902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 375902]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06757_not_prime : ¬(recordGapCenter + 376098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376098]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06758_not_prime : ¬(recordGapCenter + 376122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376122]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06759_not_prime : ¬(recordGapCenter + 376136).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376136]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06760_not_prime : ¬(recordGapCenter + 376338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376338]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06761_not_prime : ¬(recordGapCenter + 376358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376358]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06762_not_prime : ¬(recordGapCenter + 376386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376386]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06763_not_prime : ¬(recordGapCenter + 376458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376458]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06764_not_prime : ¬(recordGapCenter + 376472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376472]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06765_not_prime : ¬(recordGapCenter + 376518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376518]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06766_not_prime : ¬(recordGapCenter + 376622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376622]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06767_not_prime : ¬(recordGapCenter + 376638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376638]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06768_not_prime : ¬(recordGapCenter + 376646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376646]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06769_not_prime : ¬(recordGapCenter + 376806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376806]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06770_not_prime : ¬(recordGapCenter + 376862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 376862]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06771_not_prime : ¬(recordGapCenter + 377066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377066]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06772_not_prime : ¬(recordGapCenter + 377106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377106]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06773_not_prime : ¬(recordGapCenter + 377300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377300]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06774_not_prime : ¬(recordGapCenter + 377372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377372]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06775_not_prime : ¬(recordGapCenter + 377382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377382]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06776_not_prime : ¬(recordGapCenter + 377402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377402]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06777_not_prime : ¬(recordGapCenter + 377438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377438]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06778_not_prime : ¬(recordGapCenter + 377588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377588]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06779_not_prime : ¬(recordGapCenter + 377708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377708]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06780_not_prime : ¬(recordGapCenter + 377738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377738]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06781_not_prime : ¬(recordGapCenter + 377756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377756]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06782_not_prime : ¬(recordGapCenter + 377822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377822]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06783_not_prime : ¬(recordGapCenter + 377826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377826]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06784_not_prime : ¬(recordGapCenter + 377898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377898]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06785_not_prime : ¬(recordGapCenter + 377906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377906]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06786_not_prime : ¬(recordGapCenter + 377966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 377966]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06787_not_prime : ¬(recordGapCenter + 378008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378008]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06788_not_prime : ¬(recordGapCenter + 378038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378038]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06789_not_prime : ¬(recordGapCenter + 378086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378086]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06790_not_prime : ¬(recordGapCenter + 378278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378278]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06791_not_prime : ¬(recordGapCenter + 378296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378296]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06792_not_prime : ¬(recordGapCenter + 378402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378402]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06793_not_prime : ¬(recordGapCenter + 378438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378438]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06794_not_prime : ¬(recordGapCenter + 378458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378458]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06795_not_prime : ¬(recordGapCenter + 378536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378536]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06796_not_prime : ¬(recordGapCenter + 378542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378542]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06797_not_prime : ¬(recordGapCenter + 378582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378582]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06798_not_prime : ¬(recordGapCenter + 378722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378722]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06799_not_prime : ¬(recordGapCenter + 378786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378786]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06800_not_prime : ¬(recordGapCenter + 378866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378866]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06801_not_prime : ¬(recordGapCenter + 378878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378878]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06802_not_prime : ¬(recordGapCenter + 378908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378908]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06803_not_prime : ¬(recordGapCenter + 378926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 378926]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06804_not_prime : ¬(recordGapCenter + 379058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379058]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06805_not_prime : ¬(recordGapCenter + 379172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379172]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06806_not_prime : ¬(recordGapCenter + 379292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379292]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06807_not_prime : ¬(recordGapCenter + 379352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379352]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06808_not_prime : ¬(recordGapCenter + 379388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379388]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06809_not_prime : ¬(recordGapCenter + 379446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379446]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06810_not_prime : ¬(recordGapCenter + 379466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379466]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06811_not_prime : ¬(recordGapCenter + 379598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379598]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06812_not_prime : ¬(recordGapCenter + 379646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379646]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06813_not_prime : ¬(recordGapCenter + 379718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379718]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06814_not_prime : ¬(recordGapCenter + 379878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379878]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06815_not_prime : ¬(recordGapCenter + 379902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379902]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06816_not_prime : ¬(recordGapCenter + 379928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 379928]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06817_not_prime : ¬(recordGapCenter + 380012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380012]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06818_not_prime : ¬(recordGapCenter + 380126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380126]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06819_not_prime : ¬(recordGapCenter + 380168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380168]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06820_not_prime : ¬(recordGapCenter + 380186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380186]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06821_not_prime : ¬(recordGapCenter + 380252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380252]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06822_not_prime : ¬(recordGapCenter + 380258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380258]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06823_not_prime : ¬(recordGapCenter + 380348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380348]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06824_not_prime : ¬(recordGapCenter + 380642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380642]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06825_not_prime : ¬(recordGapCenter + 380648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380648]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06826_not_prime : ¬(recordGapCenter + 380852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380852]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06827_not_prime : ¬(recordGapCenter + 380958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 380958]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06828_not_prime : ¬(recordGapCenter + 381032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381032]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06829_not_prime : ¬(recordGapCenter + 381068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381068]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06830_not_prime : ¬(recordGapCenter + 381126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381126]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06831_not_prime : ¬(recordGapCenter + 381246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381246]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06832_not_prime : ¬(recordGapCenter + 381272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381272]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06833_not_prime : ¬(recordGapCenter + 381308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381308]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06834_not_prime : ¬(recordGapCenter + 381356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381356]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06835_not_prime : ¬(recordGapCenter + 381522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381522]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06836_not_prime : ¬(recordGapCenter + 381566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381566]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06837_not_prime : ¬(recordGapCenter + 381572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381572]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06838_not_prime : ¬(recordGapCenter + 381606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381606]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06839_not_prime : ¬(recordGapCenter + 381782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381782]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06840_not_prime : ¬(recordGapCenter + 381882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381882]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06841_not_prime : ¬(recordGapCenter + 381896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 381896]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06842_not_prime : ¬(recordGapCenter + 382002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382002]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06843_not_prime : ¬(recordGapCenter + 382142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382142]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06844_not_prime : ¬(recordGapCenter + 382218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382218]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06845_not_prime : ¬(recordGapCenter + 382232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382232]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06846_not_prime : ¬(recordGapCenter + 382238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382238]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06847_not_prime : ¬(recordGapCenter + 382286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382286]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06848_not_prime : ¬(recordGapCenter + 382362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382362]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06849_not_prime : ¬(recordGapCenter + 382566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382566]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06850_not_prime : ¬(recordGapCenter + 382638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382638]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06851_not_prime : ¬(recordGapCenter + 382856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382856]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06852_not_prime : ¬(recordGapCenter + 382868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382868]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06853_not_prime : ¬(recordGapCenter + 382898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382898]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06854_not_prime : ¬(recordGapCenter + 382946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 382946]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06855_not_prime : ¬(recordGapCenter + 383048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383048]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06856_not_prime : ¬(recordGapCenter + 383066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383066]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06857_not_prime : ¬(recordGapCenter + 383132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383132]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06858_not_prime : ¬(recordGapCenter + 383178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383178]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06859_not_prime : ¬(recordGapCenter + 383198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383198]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06860_not_prime : ¬(recordGapCenter + 383252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383252]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06861_not_prime : ¬(recordGapCenter + 383288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383288]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06862_not_prime : ¬(recordGapCenter + 383328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383328]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06863_not_prime : ¬(recordGapCenter + 383336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383336]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06864_not_prime : ¬(recordGapCenter + 383406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383406]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06865_not_prime : ¬(recordGapCenter + 383442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383442]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06866_not_prime : ¬(recordGapCenter + 383498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383498]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06867_not_prime : ¬(recordGapCenter + 383546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383546]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06868_not_prime : ¬(recordGapCenter + 383828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383828]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06869_not_prime : ¬(recordGapCenter + 383906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383906]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06870_not_prime : ¬(recordGapCenter + 383982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 383982]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06871_not_prime : ¬(recordGapCenter + 384000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384000]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06872_not_prime : ¬(recordGapCenter + 384086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384086]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06873_not_prime : ¬(recordGapCenter + 384198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384198]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06874_not_prime : ¬(recordGapCenter + 384242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384242]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06875_not_prime : ¬(recordGapCenter + 384378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384378]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06876_not_prime : ¬(recordGapCenter + 384458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384458]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06877_not_prime : ¬(recordGapCenter + 384518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384518]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06878_not_prime : ¬(recordGapCenter + 384542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384542]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06879_not_prime : ¬(recordGapCenter + 384546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384546]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06880_not_prime : ¬(recordGapCenter + 384548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384548]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06881_not_prime : ¬(recordGapCenter + 384596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384596]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06882_not_prime : ¬(recordGapCenter + 384632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384632]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06883_not_prime : ¬(recordGapCenter + 384638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384638]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06884_not_prime : ¬(recordGapCenter + 384912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384912]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06885_not_prime : ¬(recordGapCenter + 384918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384918]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06886_not_prime : ¬(recordGapCenter + 384968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 384968]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06887_not_prime : ¬(recordGapCenter + 385166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385166]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06888_not_prime : ¬(recordGapCenter + 385302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385302]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06889_not_prime : ¬(recordGapCenter + 385316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385316]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06890_not_prime : ¬(recordGapCenter + 385386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385386]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06891_not_prime : ¬(recordGapCenter + 385508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385508]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06892_not_prime : ¬(recordGapCenter + 385676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385676]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06893_not_prime : ¬(recordGapCenter + 385772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 385772]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06894_not_prime : ¬(recordGapCenter + 386018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386018]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06895_not_prime : ¬(recordGapCenter + 386108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386108]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06896_not_prime : ¬(recordGapCenter + 386186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386186]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06897_not_prime : ¬(recordGapCenter + 386286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386286]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06898_not_prime : ¬(recordGapCenter + 386306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386306]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06899_not_prime : ¬(recordGapCenter + 386402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386402]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06900_not_prime : ¬(recordGapCenter + 386418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386418]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06901_not_prime : ¬(recordGapCenter + 386696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386696]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06902_not_prime : ¬(recordGapCenter + 386706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386706]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06903_not_prime : ¬(recordGapCenter + 386898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 386898]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06904_not_prime : ¬(recordGapCenter + 387026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387026]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06905_not_prime : ¬(recordGapCenter + 387116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387116]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06906_not_prime : ¬(recordGapCenter + 387188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387188]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06907_not_prime : ¬(recordGapCenter + 387200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387200]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06908_not_prime : ¬(recordGapCenter + 387272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387272]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06909_not_prime : ¬(recordGapCenter + 387308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387308]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06910_not_prime : ¬(recordGapCenter + 387318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387318]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06911_not_prime : ¬(recordGapCenter + 387402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387402]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm06912_not_prime : ¬(recordGapCenter + 387446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387446]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

end PrimeFactorUnimodality
