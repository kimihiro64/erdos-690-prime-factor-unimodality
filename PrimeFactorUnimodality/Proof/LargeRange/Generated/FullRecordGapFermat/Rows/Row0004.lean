import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00004_values : List Nat :=
  [fullRecordGapCenterValue - 393868,
    fullRecordGapCenterValue - 393774,
    fullRecordGapCenterValue - 393634,
    fullRecordGapCenterValue - 393594,
    fullRecordGapCenterValue - 393592,
    fullRecordGapCenterValue - 393544,
    fullRecordGapCenterValue - 393508,
    fullRecordGapCenterValue - 393454,
    fullRecordGapCenterValue - 393378,
    fullRecordGapCenterValue - 393322,
    fullRecordGapCenterValue - 393292,
    fullRecordGapCenterValue - 393258,
    fullRecordGapCenterValue - 393222,
    fullRecordGapCenterValue - 393004,
    fullRecordGapCenterValue - 392998,
    fullRecordGapCenterValue - 392908,
    fullRecordGapCenterValue - 392878,
    fullRecordGapCenterValue - 392872,
    fullRecordGapCenterValue - 392662,
    fullRecordGapCenterValue - 392622,
    fullRecordGapCenterValue - 392542,
    fullRecordGapCenterValue - 392362,
    fullRecordGapCenterValue - 392278,
    fullRecordGapCenterValue - 392188,
    fullRecordGapCenterValue - 392164,
    fullRecordGapCenterValue - 392068,
    fullRecordGapCenterValue - 391962,
    fullRecordGapCenterValue - 391954,
    fullRecordGapCenterValue - 391858,
    fullRecordGapCenterValue - 391738,
    fullRecordGapCenterValue - 391542,
    fullRecordGapCenterValue - 391444,
    fullRecordGapCenterValue - 391314,
    fullRecordGapCenterValue - 391278,
    fullRecordGapCenterValue - 391218,
    fullRecordGapCenterValue - 391198,
    fullRecordGapCenterValue - 391078,
    fullRecordGapCenterValue - 391038,
    fullRecordGapCenterValue - 391002,
    fullRecordGapCenterValue - 390882,
    fullRecordGapCenterValue - 390844,
    fullRecordGapCenterValue - 390802,
    fullRecordGapCenterValue - 390778,
    fullRecordGapCenterValue - 390774,
    fullRecordGapCenterValue - 390738,
    fullRecordGapCenterValue - 390682,
    fullRecordGapCenterValue - 390568,
    fullRecordGapCenterValue - 390378,
    fullRecordGapCenterValue - 390322,
    fullRecordGapCenterValue - 390154,
    fullRecordGapCenterValue - 390094,
    fullRecordGapCenterValue - 390088,
    fullRecordGapCenterValue - 389982,
    fullRecordGapCenterValue - 389814,
    fullRecordGapCenterValue - 389812,
    fullRecordGapCenterValue - 389622,
    fullRecordGapCenterValue - 389542,
    fullRecordGapCenterValue - 389434,
    fullRecordGapCenterValue - 389308,
    fullRecordGapCenterValue - 389274,
    fullRecordGapCenterValue - 389262,
    fullRecordGapCenterValue - 389218,
    fullRecordGapCenterValue - 389212,
    fullRecordGapCenterValue - 389182,
    fullRecordGapCenterValue - 389014,
    fullRecordGapCenterValue - 388924,
    fullRecordGapCenterValue - 388902,
    fullRecordGapCenterValue - 388758,
    fullRecordGapCenterValue - 388684,
    fullRecordGapCenterValue - 388618,
    fullRecordGapCenterValue - 388468,
    fullRecordGapCenterValue - 388302,
    fullRecordGapCenterValue - 388080,
    fullRecordGapCenterValue - 388012,
    fullRecordGapCenterValue - 388002,
    fullRecordGapCenterValue - 387988,
    fullRecordGapCenterValue - 387978,
    fullRecordGapCenterValue - 387874,
    fullRecordGapCenterValue - 387832,
    fullRecordGapCenterValue - 387784,
    fullRecordGapCenterValue - 387762,
    fullRecordGapCenterValue - 387742,
    fullRecordGapCenterValue - 387694,
    fullRecordGapCenterValue - 387592,
    fullRecordGapCenterValue - 387298,
    fullRecordGapCenterValue - 387238,
    fullRecordGapCenterValue - 387154,
    fullRecordGapCenterValue - 387118,
    fullRecordGapCenterValue - 387082,
    fullRecordGapCenterValue - 386994,
    fullRecordGapCenterValue - 386938,
    fullRecordGapCenterValue - 386934,
    fullRecordGapCenterValue - 386788,
    fullRecordGapCenterValue - 386734,
    fullRecordGapCenterValue - 386728,
    fullRecordGapCenterValue - 386668,
    fullRecordGapCenterValue - 386572,
    fullRecordGapCenterValue - 386494,
    fullRecordGapCenterValue - 386488,
    fullRecordGapCenterValue - 386418,
    fullRecordGapCenterValue - 386392,
    fullRecordGapCenterValue - 386362,
    fullRecordGapCenterValue - 386278,
    fullRecordGapCenterValue - 386248,
    fullRecordGapCenterValue - 386238,
    fullRecordGapCenterValue - 386068,
    fullRecordGapCenterValue - 385998,
    fullRecordGapCenterValue - 385948,
    fullRecordGapCenterValue - 385942,
    fullRecordGapCenterValue - 385912,
    fullRecordGapCenterValue - 385698,
    fullRecordGapCenterValue - 385674,
    fullRecordGapCenterValue - 385432,
    fullRecordGapCenterValue - 385348,
    fullRecordGapCenterValue - 385338,
    fullRecordGapCenterValue - 385324,
    fullRecordGapCenterValue - 385222,
    fullRecordGapCenterValue - 384918,
    fullRecordGapCenterValue - 384912,
    fullRecordGapCenterValue - 384862,
    fullRecordGapCenterValue - 384814,
    fullRecordGapCenterValue - 384694,
    fullRecordGapCenterValue - 384634,
    fullRecordGapCenterValue - 384628,
    fullRecordGapCenterValue - 384502,
    fullRecordGapCenterValue - 384478,
    fullRecordGapCenterValue - 384382,
    fullRecordGapCenterValue - 384232,
    fullRecordGapCenterValue - 384160,
    fullRecordGapCenterValue - 384094,
    fullRecordGapCenterValue - 384004,
    fullRecordGapCenterValue - 383998,
    fullRecordGapCenterValue - 383938,
    fullRecordGapCenterValue - 383862,
    fullRecordGapCenterValue - 383788,
    fullRecordGapCenterValue - 383752,
    fullRecordGapCenterValue - 383722,
    fullRecordGapCenterValue - 383694,
    fullRecordGapCenterValue - 383668,
    fullRecordGapCenterValue - 383512,
    fullRecordGapCenterValue - 383494,
    fullRecordGapCenterValue - 383434,
    fullRecordGapCenterValue - 383242,
    fullRecordGapCenterValue - 383224,
    fullRecordGapCenterValue - 383164,
    fullRecordGapCenterValue - 383158,
    fullRecordGapCenterValue - 383122,
    fullRecordGapCenterValue - 383074,
    fullRecordGapCenterValue - 383038,
    fullRecordGapCenterValue - 383014,
    fullRecordGapCenterValue - 382938,
    fullRecordGapCenterValue - 382918,
    fullRecordGapCenterValue - 382882,
    fullRecordGapCenterValue - 382854,
    fullRecordGapCenterValue - 382828,
    fullRecordGapCenterValue - 382818,
    fullRecordGapCenterValue - 382758,
    fullRecordGapCenterValue - 382638,
    fullRecordGapCenterValue - 382498,
    fullRecordGapCenterValue - 382314,
    fullRecordGapCenterValue - 382218,
    fullRecordGapCenterValue - 382198,
    fullRecordGapCenterValue - 382042,
    fullRecordGapCenterValue - 381958,
    fullRecordGapCenterValue - 381954,
    fullRecordGapCenterValue - 381882,
    fullRecordGapCenterValue - 381778,
    fullRecordGapCenterValue - 381772,
    fullRecordGapCenterValue - 381742,
    fullRecordGapCenterValue - 381688,
    fullRecordGapCenterValue - 381642,
    fullRecordGapCenterValue - 381622,
    fullRecordGapCenterValue - 381574,
    fullRecordGapCenterValue - 381538,
    fullRecordGapCenterValue - 381534,
    fullRecordGapCenterValue - 381268,
    fullRecordGapCenterValue - 381162,
    fullRecordGapCenterValue - 381112,
    fullRecordGapCenterValue - 381024,
    fullRecordGapCenterValue - 380838,
    fullRecordGapCenterValue - 380818,
    fullRecordGapCenterValue - 380572,
    fullRecordGapCenterValue - 380524,
    fullRecordGapCenterValue - 380454,
    fullRecordGapCenterValue - 380382,
    fullRecordGapCenterValue - 380344,
    fullRecordGapCenterValue - 380334,
    fullRecordGapCenterValue - 380284,
    fullRecordGapCenterValue - 380242,
    fullRecordGapCenterValue - 380118,
    fullRecordGapCenterValue - 380022,
    fullRecordGapCenterValue - 379978,
    fullRecordGapCenterValue - 379972,
    fullRecordGapCenterValue - 379902,
    fullRecordGapCenterValue - 379804,
    fullRecordGapCenterValue - 379774,
    fullRecordGapCenterValue - 379672,
    fullRecordGapCenterValue - 379594,
    fullRecordGapCenterValue - 379528,
    fullRecordGapCenterValue - 379402,
    fullRecordGapCenterValue - 379348,
    fullRecordGapCenterValue - 379342,
    fullRecordGapCenterValue - 379234,
    fullRecordGapCenterValue - 379194,
    fullRecordGapCenterValue - 379074,
    fullRecordGapCenterValue - 379048,
    fullRecordGapCenterValue - 378958,
    fullRecordGapCenterValue - 378894,
    fullRecordGapCenterValue - 378892,
    fullRecordGapCenterValue - 378874,
    fullRecordGapCenterValue - 378748,
    fullRecordGapCenterValue - 378622,
    fullRecordGapCenterValue - 378618,
    fullRecordGapCenterValue - 378604,
    fullRecordGapCenterValue - 378412,
    fullRecordGapCenterValue - 378172,
    fullRecordGapCenterValue - 378124,
    fullRecordGapCenterValue - 378034,
    fullRecordGapCenterValue - 377998,
    fullRecordGapCenterValue - 377934,
    fullRecordGapCenterValue - 377932,
    fullRecordGapCenterValue - 377908,
    fullRecordGapCenterValue - 377878,
    fullRecordGapCenterValue - 377512,
    fullRecordGapCenterValue - 377382,
    fullRecordGapCenterValue - 377362,
    fullRecordGapCenterValue - 377218,
    fullRecordGapCenterValue - 377032,
    fullRecordGapCenterValue - 376962,
    fullRecordGapCenterValue - 376834,
    fullRecordGapCenterValue - 376738,
    fullRecordGapCenterValue - 376702,
    fullRecordGapCenterValue - 376638,
    fullRecordGapCenterValue - 376582,
    fullRecordGapCenterValue - 376518,
    fullRecordGapCenterValue - 376294,
    fullRecordGapCenterValue - 376122,
    fullRecordGapCenterValue - 375868,
    fullRecordGapCenterValue - 375798,
    fullRecordGapCenterValue - 375748,
    fullRecordGapCenterValue - 375652,
    fullRecordGapCenterValue - 375618,
    fullRecordGapCenterValue - 375604,
    fullRecordGapCenterValue - 375442,
    fullRecordGapCenterValue - 375378,
    fullRecordGapCenterValue - 375294,
    fullRecordGapCenterValue - 375262,
    fullRecordGapCenterValue - 375244,
    fullRecordGapCenterValue - 375118,
    fullRecordGapCenterValue - 375094,
    fullRecordGapCenterValue - 375000,
    fullRecordGapCenterValue - 374982,
    fullRecordGapCenterValue - 374898,
    fullRecordGapCenterValue - 374674,
    fullRecordGapCenterValue - 374548,
    fullRecordGapCenterValue - 374502]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00004_fermat : ∀ n ∈ fullRecordGapRow00004_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00769_not_prime : ¬(recordGapCenter - 393868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393868]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00770_not_prime : ¬(recordGapCenter - 393774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393774]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00771_not_prime : ¬(recordGapCenter - 393634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393634]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00772_not_prime : ¬(recordGapCenter - 393594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393594]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00773_not_prime : ¬(recordGapCenter - 393592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393592]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00774_not_prime : ¬(recordGapCenter - 393544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393544]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00775_not_prime : ¬(recordGapCenter - 393508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393508]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00776_not_prime : ¬(recordGapCenter - 393454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393454]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00777_not_prime : ¬(recordGapCenter - 393378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393378]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00778_not_prime : ¬(recordGapCenter - 393322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393322]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00779_not_prime : ¬(recordGapCenter - 393292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393292]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00780_not_prime : ¬(recordGapCenter - 393258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393258]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00781_not_prime : ¬(recordGapCenter - 393222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393222]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00782_not_prime : ¬(recordGapCenter - 393004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393004]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00783_not_prime : ¬(recordGapCenter - 392998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392998]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00784_not_prime : ¬(recordGapCenter - 392908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392908]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00785_not_prime : ¬(recordGapCenter - 392878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392878]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00786_not_prime : ¬(recordGapCenter - 392872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392872]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00787_not_prime : ¬(recordGapCenter - 392662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392662]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00788_not_prime : ¬(recordGapCenter - 392622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392622]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00789_not_prime : ¬(recordGapCenter - 392542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392542]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00790_not_prime : ¬(recordGapCenter - 392362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392362]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00791_not_prime : ¬(recordGapCenter - 392278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392278]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00792_not_prime : ¬(recordGapCenter - 392188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392188]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00793_not_prime : ¬(recordGapCenter - 392164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392164]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00794_not_prime : ¬(recordGapCenter - 392068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392068]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00795_not_prime : ¬(recordGapCenter - 391962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391962]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00796_not_prime : ¬(recordGapCenter - 391954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391954]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00797_not_prime : ¬(recordGapCenter - 391858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391858]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00798_not_prime : ¬(recordGapCenter - 391738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391738]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00799_not_prime : ¬(recordGapCenter - 391542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391542]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00800_not_prime : ¬(recordGapCenter - 391444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391444]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00801_not_prime : ¬(recordGapCenter - 391314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391314]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00802_not_prime : ¬(recordGapCenter - 391278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391278]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00803_not_prime : ¬(recordGapCenter - 391218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391218]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00804_not_prime : ¬(recordGapCenter - 391198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391198]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00805_not_prime : ¬(recordGapCenter - 391078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391078]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00806_not_prime : ¬(recordGapCenter - 391038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391038]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00807_not_prime : ¬(recordGapCenter - 391002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391002]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00808_not_prime : ¬(recordGapCenter - 390882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390882]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00809_not_prime : ¬(recordGapCenter - 390844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390844]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00810_not_prime : ¬(recordGapCenter - 390802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390802]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00811_not_prime : ¬(recordGapCenter - 390778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390778]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00812_not_prime : ¬(recordGapCenter - 390774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390774]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00813_not_prime : ¬(recordGapCenter - 390738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390738]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00814_not_prime : ¬(recordGapCenter - 390682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390682]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00815_not_prime : ¬(recordGapCenter - 390568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390568]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00816_not_prime : ¬(recordGapCenter - 390378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390378]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00817_not_prime : ¬(recordGapCenter - 390322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390322]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00818_not_prime : ¬(recordGapCenter - 390154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390154]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00819_not_prime : ¬(recordGapCenter - 390094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390094]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00820_not_prime : ¬(recordGapCenter - 390088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390088]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00821_not_prime : ¬(recordGapCenter - 389982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389982]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00822_not_prime : ¬(recordGapCenter - 389814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389814]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00823_not_prime : ¬(recordGapCenter - 389812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389812]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00824_not_prime : ¬(recordGapCenter - 389622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389622]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00825_not_prime : ¬(recordGapCenter - 389542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389542]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00826_not_prime : ¬(recordGapCenter - 389434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389434]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00827_not_prime : ¬(recordGapCenter - 389308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389308]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00828_not_prime : ¬(recordGapCenter - 389274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389274]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00829_not_prime : ¬(recordGapCenter - 389262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389262]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00830_not_prime : ¬(recordGapCenter - 389218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389218]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00831_not_prime : ¬(recordGapCenter - 389212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389212]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00832_not_prime : ¬(recordGapCenter - 389182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389182]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00833_not_prime : ¬(recordGapCenter - 389014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389014]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00834_not_prime : ¬(recordGapCenter - 388924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388924]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00835_not_prime : ¬(recordGapCenter - 388902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388902]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00836_not_prime : ¬(recordGapCenter - 388758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388758]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00837_not_prime : ¬(recordGapCenter - 388684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388684]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00838_not_prime : ¬(recordGapCenter - 388618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388618]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00839_not_prime : ¬(recordGapCenter - 388468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388468]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00840_not_prime : ¬(recordGapCenter - 388302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388302]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00841_not_prime : ¬(recordGapCenter - 388080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388080]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00842_not_prime : ¬(recordGapCenter - 388012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388012]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00843_not_prime : ¬(recordGapCenter - 388002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 388002]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00844_not_prime : ¬(recordGapCenter - 387988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387988]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00845_not_prime : ¬(recordGapCenter - 387978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387978]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00846_not_prime : ¬(recordGapCenter - 387874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387874]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00847_not_prime : ¬(recordGapCenter - 387832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387832]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00848_not_prime : ¬(recordGapCenter - 387784).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387784]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00849_not_prime : ¬(recordGapCenter - 387762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387762]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00850_not_prime : ¬(recordGapCenter - 387742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387742]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00851_not_prime : ¬(recordGapCenter - 387694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387694]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00852_not_prime : ¬(recordGapCenter - 387592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387592]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00853_not_prime : ¬(recordGapCenter - 387298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387298]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00854_not_prime : ¬(recordGapCenter - 387238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387238]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00855_not_prime : ¬(recordGapCenter - 387154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387154]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00856_not_prime : ¬(recordGapCenter - 387118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387118]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00857_not_prime : ¬(recordGapCenter - 387082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 387082]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00858_not_prime : ¬(recordGapCenter - 386994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386994]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00859_not_prime : ¬(recordGapCenter - 386938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386938]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00860_not_prime : ¬(recordGapCenter - 386934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386934]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00861_not_prime : ¬(recordGapCenter - 386788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386788]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00862_not_prime : ¬(recordGapCenter - 386734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386734]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00863_not_prime : ¬(recordGapCenter - 386728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386728]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00864_not_prime : ¬(recordGapCenter - 386668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386668]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00865_not_prime : ¬(recordGapCenter - 386572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386572]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00866_not_prime : ¬(recordGapCenter - 386494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386494]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00867_not_prime : ¬(recordGapCenter - 386488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386488]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00868_not_prime : ¬(recordGapCenter - 386418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386418]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00869_not_prime : ¬(recordGapCenter - 386392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386392]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00870_not_prime : ¬(recordGapCenter - 386362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386362]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00871_not_prime : ¬(recordGapCenter - 386278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386278]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00872_not_prime : ¬(recordGapCenter - 386248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386248]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00873_not_prime : ¬(recordGapCenter - 386238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386238]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00874_not_prime : ¬(recordGapCenter - 386068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 386068]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00875_not_prime : ¬(recordGapCenter - 385998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385998]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00876_not_prime : ¬(recordGapCenter - 385948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385948]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00877_not_prime : ¬(recordGapCenter - 385942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385942]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00878_not_prime : ¬(recordGapCenter - 385912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385912]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00879_not_prime : ¬(recordGapCenter - 385698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385698]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00880_not_prime : ¬(recordGapCenter - 385674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385674]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00881_not_prime : ¬(recordGapCenter - 385432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385432]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00882_not_prime : ¬(recordGapCenter - 385348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385348]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00883_not_prime : ¬(recordGapCenter - 385338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385338]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00884_not_prime : ¬(recordGapCenter - 385324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385324]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00885_not_prime : ¬(recordGapCenter - 385222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 385222]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00886_not_prime : ¬(recordGapCenter - 384918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384918]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00887_not_prime : ¬(recordGapCenter - 384912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384912]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00888_not_prime : ¬(recordGapCenter - 384862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384862]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00889_not_prime : ¬(recordGapCenter - 384814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384814]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00890_not_prime : ¬(recordGapCenter - 384694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384694]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00891_not_prime : ¬(recordGapCenter - 384634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384634]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00892_not_prime : ¬(recordGapCenter - 384628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384628]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00893_not_prime : ¬(recordGapCenter - 384502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384502]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00894_not_prime : ¬(recordGapCenter - 384478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384478]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00895_not_prime : ¬(recordGapCenter - 384382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384382]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00896_not_prime : ¬(recordGapCenter - 384232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384232]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00897_not_prime : ¬(recordGapCenter - 384160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384160]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00898_not_prime : ¬(recordGapCenter - 384094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384094]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00899_not_prime : ¬(recordGapCenter - 384004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384004]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00900_not_prime : ¬(recordGapCenter - 383998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383998]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00901_not_prime : ¬(recordGapCenter - 383938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383938]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00902_not_prime : ¬(recordGapCenter - 383862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383862]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00903_not_prime : ¬(recordGapCenter - 383788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383788]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00904_not_prime : ¬(recordGapCenter - 383752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383752]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00905_not_prime : ¬(recordGapCenter - 383722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383722]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00906_not_prime : ¬(recordGapCenter - 383694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383694]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00907_not_prime : ¬(recordGapCenter - 383668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383668]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00908_not_prime : ¬(recordGapCenter - 383512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383512]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00909_not_prime : ¬(recordGapCenter - 383494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383494]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00910_not_prime : ¬(recordGapCenter - 383434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383434]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00911_not_prime : ¬(recordGapCenter - 383242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383242]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00912_not_prime : ¬(recordGapCenter - 383224).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383224]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00913_not_prime : ¬(recordGapCenter - 383164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383164]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00914_not_prime : ¬(recordGapCenter - 383158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383158]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00915_not_prime : ¬(recordGapCenter - 383122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383122]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00916_not_prime : ¬(recordGapCenter - 383074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383074]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00917_not_prime : ¬(recordGapCenter - 383038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383038]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00918_not_prime : ¬(recordGapCenter - 383014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383014]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00919_not_prime : ¬(recordGapCenter - 382938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382938]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00920_not_prime : ¬(recordGapCenter - 382918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382918]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00921_not_prime : ¬(recordGapCenter - 382882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382882]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00922_not_prime : ¬(recordGapCenter - 382854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382854]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00923_not_prime : ¬(recordGapCenter - 382828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382828]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00924_not_prime : ¬(recordGapCenter - 382818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382818]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00925_not_prime : ¬(recordGapCenter - 382758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382758]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00926_not_prime : ¬(recordGapCenter - 382638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382638]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00927_not_prime : ¬(recordGapCenter - 382498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382498]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00928_not_prime : ¬(recordGapCenter - 382314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382314]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00929_not_prime : ¬(recordGapCenter - 382218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382218]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00930_not_prime : ¬(recordGapCenter - 382198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382198]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00931_not_prime : ¬(recordGapCenter - 382042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382042]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00932_not_prime : ¬(recordGapCenter - 381958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381958]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00933_not_prime : ¬(recordGapCenter - 381954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381954]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00934_not_prime : ¬(recordGapCenter - 381882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381882]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00935_not_prime : ¬(recordGapCenter - 381778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381778]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00936_not_prime : ¬(recordGapCenter - 381772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381772]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00937_not_prime : ¬(recordGapCenter - 381742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381742]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00938_not_prime : ¬(recordGapCenter - 381688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381688]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00939_not_prime : ¬(recordGapCenter - 381642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381642]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00940_not_prime : ¬(recordGapCenter - 381622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381622]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00941_not_prime : ¬(recordGapCenter - 381574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381574]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00942_not_prime : ¬(recordGapCenter - 381538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381538]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00943_not_prime : ¬(recordGapCenter - 381534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381534]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00944_not_prime : ¬(recordGapCenter - 381268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381268]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00945_not_prime : ¬(recordGapCenter - 381162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381162]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00946_not_prime : ¬(recordGapCenter - 381112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381112]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00947_not_prime : ¬(recordGapCenter - 381024).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381024]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00948_not_prime : ¬(recordGapCenter - 380838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380838]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00949_not_prime : ¬(recordGapCenter - 380818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380818]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00950_not_prime : ¬(recordGapCenter - 380572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380572]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00951_not_prime : ¬(recordGapCenter - 380524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380524]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00952_not_prime : ¬(recordGapCenter - 380454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380454]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00953_not_prime : ¬(recordGapCenter - 380382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380382]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00954_not_prime : ¬(recordGapCenter - 380344).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380344]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00955_not_prime : ¬(recordGapCenter - 380334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380334]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00956_not_prime : ¬(recordGapCenter - 380284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380284]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00957_not_prime : ¬(recordGapCenter - 380242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380242]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00958_not_prime : ¬(recordGapCenter - 380118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380118]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00959_not_prime : ¬(recordGapCenter - 380022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380022]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00960_not_prime : ¬(recordGapCenter - 379978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379978]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00961_not_prime : ¬(recordGapCenter - 379972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379972]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00962_not_prime : ¬(recordGapCenter - 379902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379902]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00963_not_prime : ¬(recordGapCenter - 379804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379804]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00964_not_prime : ¬(recordGapCenter - 379774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379774]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00965_not_prime : ¬(recordGapCenter - 379672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379672]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00966_not_prime : ¬(recordGapCenter - 379594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379594]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00967_not_prime : ¬(recordGapCenter - 379528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379528]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00968_not_prime : ¬(recordGapCenter - 379402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379402]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00969_not_prime : ¬(recordGapCenter - 379348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379348]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00970_not_prime : ¬(recordGapCenter - 379342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379342]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00971_not_prime : ¬(recordGapCenter - 379234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379234]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00972_not_prime : ¬(recordGapCenter - 379194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379194]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00973_not_prime : ¬(recordGapCenter - 379074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379074]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00974_not_prime : ¬(recordGapCenter - 379048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379048]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00975_not_prime : ¬(recordGapCenter - 378958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378958]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00976_not_prime : ¬(recordGapCenter - 378894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378894]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00977_not_prime : ¬(recordGapCenter - 378892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378892]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00978_not_prime : ¬(recordGapCenter - 378874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378874]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00979_not_prime : ¬(recordGapCenter - 378748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378748]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00980_not_prime : ¬(recordGapCenter - 378622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378622]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00981_not_prime : ¬(recordGapCenter - 378618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378618]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00982_not_prime : ¬(recordGapCenter - 378604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378604]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00983_not_prime : ¬(recordGapCenter - 378412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378412]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00984_not_prime : ¬(recordGapCenter - 378172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378172]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00985_not_prime : ¬(recordGapCenter - 378124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378124]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00986_not_prime : ¬(recordGapCenter - 378034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378034]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00987_not_prime : ¬(recordGapCenter - 377998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377998]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00988_not_prime : ¬(recordGapCenter - 377934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377934]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00989_not_prime : ¬(recordGapCenter - 377932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377932]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00990_not_prime : ¬(recordGapCenter - 377908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377908]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00991_not_prime : ¬(recordGapCenter - 377878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377878]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00992_not_prime : ¬(recordGapCenter - 377512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377512]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00993_not_prime : ¬(recordGapCenter - 377382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377382]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00994_not_prime : ¬(recordGapCenter - 377362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377362]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00995_not_prime : ¬(recordGapCenter - 377218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377218]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00996_not_prime : ¬(recordGapCenter - 377032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377032]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00997_not_prime : ¬(recordGapCenter - 376962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376962]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00998_not_prime : ¬(recordGapCenter - 376834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376834]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00999_not_prime : ¬(recordGapCenter - 376738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376738]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01000_not_prime : ¬(recordGapCenter - 376702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376702]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01001_not_prime : ¬(recordGapCenter - 376638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376638]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01002_not_prime : ¬(recordGapCenter - 376582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376582]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01003_not_prime : ¬(recordGapCenter - 376518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376518]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01004_not_prime : ¬(recordGapCenter - 376294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376294]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01005_not_prime : ¬(recordGapCenter - 376122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376122]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01006_not_prime : ¬(recordGapCenter - 375868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375868]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01007_not_prime : ¬(recordGapCenter - 375798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375798]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01008_not_prime : ¬(recordGapCenter - 375748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375748]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01009_not_prime : ¬(recordGapCenter - 375652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375652]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01010_not_prime : ¬(recordGapCenter - 375618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375618]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01011_not_prime : ¬(recordGapCenter - 375604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375604]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01012_not_prime : ¬(recordGapCenter - 375442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375442]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01013_not_prime : ¬(recordGapCenter - 375378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375378]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01014_not_prime : ¬(recordGapCenter - 375294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375294]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01015_not_prime : ¬(recordGapCenter - 375262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375262]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01016_not_prime : ¬(recordGapCenter - 375244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375244]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01017_not_prime : ¬(recordGapCenter - 375118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375118]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01018_not_prime : ¬(recordGapCenter - 375094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375094]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01019_not_prime : ¬(recordGapCenter - 375000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375000]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01020_not_prime : ¬(recordGapCenter - 374982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374982]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01021_not_prime : ¬(recordGapCenter - 374898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374898]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01022_not_prime : ¬(recordGapCenter - 374674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374674]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01023_not_prime : ¬(recordGapCenter - 374548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374548]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm01024_not_prime : ¬(recordGapCenter - 374502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374502]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

end PrimeFactorUnimodality
