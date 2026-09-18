import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00026_values : List Nat :=
  [fullRecordGapCenterValue + 348482,
    fullRecordGapCenterValue + 348632,
    fullRecordGapCenterValue + 348666,
    fullRecordGapCenterValue + 348716,
    fullRecordGapCenterValue + 348882,
    fullRecordGapCenterValue + 349142,
    fullRecordGapCenterValue + 349196,
    fullRecordGapCenterValue + 349242,
    fullRecordGapCenterValue + 349266,
    fullRecordGapCenterValue + 349298,
    fullRecordGapCenterValue + 349352,
    fullRecordGapCenterValue + 349358,
    fullRecordGapCenterValue + 349386,
    fullRecordGapCenterValue + 349458,
    fullRecordGapCenterValue + 349626,
    fullRecordGapCenterValue + 349658,
    fullRecordGapCenterValue + 349718,
    fullRecordGapCenterValue + 349736,
    fullRecordGapCenterValue + 349886,
    fullRecordGapCenterValue + 349920,
    fullRecordGapCenterValue + 349926,
    fullRecordGapCenterValue + 350000,
    fullRecordGapCenterValue + 350072,
    fullRecordGapCenterValue + 350156,
    fullRecordGapCenterValue + 350282,
    fullRecordGapCenterValue + 350312,
    fullRecordGapCenterValue + 350408,
    fullRecordGapCenterValue + 350418,
    fullRecordGapCenterValue + 350466,
    fullRecordGapCenterValue + 350502,
    fullRecordGapCenterValue + 350562,
    fullRecordGapCenterValue + 350582,
    fullRecordGapCenterValue + 350666,
    fullRecordGapCenterValue + 350862,
    fullRecordGapCenterValue + 350876,
    fullRecordGapCenterValue + 350936,
    fullRecordGapCenterValue + 351066,
    fullRecordGapCenterValue + 351146,
    fullRecordGapCenterValue + 351188,
    fullRecordGapCenterValue + 351222,
    fullRecordGapCenterValue + 351326,
    fullRecordGapCenterValue + 351332,
    fullRecordGapCenterValue + 351398,
    fullRecordGapCenterValue + 351506,
    fullRecordGapCenterValue + 351782,
    fullRecordGapCenterValue + 351836,
    fullRecordGapCenterValue + 351942,
    fullRecordGapCenterValue + 352046,
    fullRecordGapCenterValue + 352076,
    fullRecordGapCenterValue + 352082,
    fullRecordGapCenterValue + 352122,
    fullRecordGapCenterValue + 352158,
    fullRecordGapCenterValue + 352266,
    fullRecordGapCenterValue + 352322,
    fullRecordGapCenterValue + 352382,
    fullRecordGapCenterValue + 352398,
    fullRecordGapCenterValue + 352472,
    fullRecordGapCenterValue + 352542,
    fullRecordGapCenterValue + 352626,
    fullRecordGapCenterValue + 352800,
    fullRecordGapCenterValue + 352808,
    fullRecordGapCenterValue + 352892,
    fullRecordGapCenterValue + 352952,
    fullRecordGapCenterValue + 353018,
    fullRecordGapCenterValue + 353042,
    fullRecordGapCenterValue + 353048,
    fullRecordGapCenterValue + 353222,
    fullRecordGapCenterValue + 353348,
    fullRecordGapCenterValue + 353406,
    fullRecordGapCenterValue + 353442,
    fullRecordGapCenterValue + 353516,
    fullRecordGapCenterValue + 353658,
    fullRecordGapCenterValue + 353768,
    fullRecordGapCenterValue + 353876,
    fullRecordGapCenterValue + 353946,
    fullRecordGapCenterValue + 353966,
    fullRecordGapCenterValue + 353972,
    fullRecordGapCenterValue + 354092,
    fullRecordGapCenterValue + 354126,
    fullRecordGapCenterValue + 354182,
    fullRecordGapCenterValue + 354422,
    fullRecordGapCenterValue + 354446,
    fullRecordGapCenterValue + 354572,
    fullRecordGapCenterValue + 354758,
    fullRecordGapCenterValue + 354816,
    fullRecordGapCenterValue + 354842,
    fullRecordGapCenterValue + 354846,
    fullRecordGapCenterValue + 355002,
    fullRecordGapCenterValue + 355022,
    fullRecordGapCenterValue + 355182,
    fullRecordGapCenterValue + 355478,
    fullRecordGapCenterValue + 355526,
    fullRecordGapCenterValue + 355622,
    fullRecordGapCenterValue + 355638,
    fullRecordGapCenterValue + 355686,
    fullRecordGapCenterValue + 355766,
    fullRecordGapCenterValue + 355826,
    fullRecordGapCenterValue + 355988,
    fullRecordGapCenterValue + 356036,
    fullRecordGapCenterValue + 356042,
    fullRecordGapCenterValue + 356186,
    fullRecordGapCenterValue + 356228,
    fullRecordGapCenterValue + 356276,
    fullRecordGapCenterValue + 356322,
    fullRecordGapCenterValue + 356358,
    fullRecordGapCenterValue + 356492,
    fullRecordGapCenterValue + 356498,
    fullRecordGapCenterValue + 356666,
    fullRecordGapCenterValue + 356786,
    fullRecordGapCenterValue + 356802,
    fullRecordGapCenterValue + 356882,
    fullRecordGapCenterValue + 356948,
    fullRecordGapCenterValue + 356982,
    fullRecordGapCenterValue + 357002,
    fullRecordGapCenterValue + 357026,
    fullRecordGapCenterValue + 357092,
    fullRecordGapCenterValue + 357218,
    fullRecordGapCenterValue + 357242,
    fullRecordGapCenterValue + 357402,
    fullRecordGapCenterValue + 357548,
    fullRecordGapCenterValue + 357596,
    fullRecordGapCenterValue + 357662,
    fullRecordGapCenterValue + 357668,
    fullRecordGapCenterValue + 357726,
    fullRecordGapCenterValue + 357746,
    fullRecordGapCenterValue + 357806,
    fullRecordGapCenterValue + 357908,
    fullRecordGapCenterValue + 357978,
    fullRecordGapCenterValue + 358076,
    fullRecordGapCenterValue + 358082,
    fullRecordGapCenterValue + 358158,
    fullRecordGapCenterValue + 358166,
    fullRecordGapCenterValue + 358286,
    fullRecordGapCenterValue + 358338,
    fullRecordGapCenterValue + 358400,
    fullRecordGapCenterValue + 358412,
    fullRecordGapCenterValue + 358458,
    fullRecordGapCenterValue + 358538,
    fullRecordGapCenterValue + 358562,
    fullRecordGapCenterValue + 358676,
    fullRecordGapCenterValue + 358782,
    fullRecordGapCenterValue + 358922,
    fullRecordGapCenterValue + 359066,
    fullRecordGapCenterValue + 359096,
    fullRecordGapCenterValue + 359186,
    fullRecordGapCenterValue + 359276,
    fullRecordGapCenterValue + 359318,
    fullRecordGapCenterValue + 359342,
    fullRecordGapCenterValue + 359588,
    fullRecordGapCenterValue + 359672,
    fullRecordGapCenterValue + 359846,
    fullRecordGapCenterValue + 359886,
    fullRecordGapCenterValue + 359978,
    fullRecordGapCenterValue + 360056,
    fullRecordGapCenterValue + 360078,
    fullRecordGapCenterValue + 360236,
    fullRecordGapCenterValue + 360362,
    fullRecordGapCenterValue + 360428,
    fullRecordGapCenterValue + 360546,
    fullRecordGapCenterValue + 360596,
    fullRecordGapCenterValue + 360722,
    fullRecordGapCenterValue + 360762,
    fullRecordGapCenterValue + 360782,
    fullRecordGapCenterValue + 360788,
    fullRecordGapCenterValue + 360812,
    fullRecordGapCenterValue + 360908,
    fullRecordGapCenterValue + 361002,
    fullRecordGapCenterValue + 361502,
    fullRecordGapCenterValue + 361506,
    fullRecordGapCenterValue + 361586,
    fullRecordGapCenterValue + 361628,
    fullRecordGapCenterValue + 361898,
    fullRecordGapCenterValue + 361902,
    fullRecordGapCenterValue + 361986,
    fullRecordGapCenterValue + 362078,
    fullRecordGapCenterValue + 362238,
    fullRecordGapCenterValue + 362282,
    fullRecordGapCenterValue + 362486,
    fullRecordGapCenterValue + 362546,
    fullRecordGapCenterValue + 362552,
    fullRecordGapCenterValue + 362588,
    fullRecordGapCenterValue + 362636,
    fullRecordGapCenterValue + 362658,
    fullRecordGapCenterValue + 362708,
    fullRecordGapCenterValue + 362958,
    fullRecordGapCenterValue + 363000,
    fullRecordGapCenterValue + 363002,
    fullRecordGapCenterValue + 363098,
    fullRecordGapCenterValue + 363126,
    fullRecordGapCenterValue + 363338,
    fullRecordGapCenterValue + 363452,
    fullRecordGapCenterValue + 363512,
    fullRecordGapCenterValue + 363578,
    fullRecordGapCenterValue + 363606,
    fullRecordGapCenterValue + 363702,
    fullRecordGapCenterValue + 363738,
    fullRecordGapCenterValue + 363746,
    fullRecordGapCenterValue + 363806,
    fullRecordGapCenterValue + 363882,
    fullRecordGapCenterValue + 363956,
    fullRecordGapCenterValue + 364022,
    fullRecordGapCenterValue + 364082,
    fullRecordGapCenterValue + 364218,
    fullRecordGapCenterValue + 364262,
    fullRecordGapCenterValue + 364358,
    fullRecordGapCenterValue + 364478,
    fullRecordGapCenterValue + 364500,
    fullRecordGapCenterValue + 364556,
    fullRecordGapCenterValue + 364578,
    fullRecordGapCenterValue + 364652,
    fullRecordGapCenterValue + 364758,
    fullRecordGapCenterValue + 364772,
    fullRecordGapCenterValue + 364946,
    fullRecordGapCenterValue + 365018,
    fullRecordGapCenterValue + 365198,
    fullRecordGapCenterValue + 365282,
    fullRecordGapCenterValue + 365426,
    fullRecordGapCenterValue + 365478,
    fullRecordGapCenterValue + 365492,
    fullRecordGapCenterValue + 365558,
    fullRecordGapCenterValue + 365576,
    fullRecordGapCenterValue + 365622,
    fullRecordGapCenterValue + 365642,
    fullRecordGapCenterValue + 365678,
    fullRecordGapCenterValue + 365828,
    fullRecordGapCenterValue + 365858,
    fullRecordGapCenterValue + 365996,
    fullRecordGapCenterValue + 366006,
    fullRecordGapCenterValue + 366182,
    fullRecordGapCenterValue + 366258,
    fullRecordGapCenterValue + 366332,
    fullRecordGapCenterValue + 366342,
    fullRecordGapCenterValue + 366518,
    fullRecordGapCenterValue + 366566,
    fullRecordGapCenterValue + 366578,
    fullRecordGapCenterValue + 366602,
    fullRecordGapCenterValue + 366686,
    fullRecordGapCenterValue + 366746,
    fullRecordGapCenterValue + 366812,
    fullRecordGapCenterValue + 366902,
    fullRecordGapCenterValue + 366998,
    fullRecordGapCenterValue + 367266,
    fullRecordGapCenterValue + 367322,
    fullRecordGapCenterValue + 367416,
    fullRecordGapCenterValue + 367518,
    fullRecordGapCenterValue + 367782,
    fullRecordGapCenterValue + 367838,
    fullRecordGapCenterValue + 367986,
    fullRecordGapCenterValue + 368006,
    fullRecordGapCenterValue + 368036,
    fullRecordGapCenterValue + 368162,
    fullRecordGapCenterValue + 368168,
    fullRecordGapCenterValue + 368216,
    fullRecordGapCenterValue + 368418,
    fullRecordGapCenterValue + 368546,
    fullRecordGapCenterValue + 368558]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00026_fermat : ∀ n ∈ fullRecordGapRow00026_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06401_not_prime : ¬(recordGapCenter + 348482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348482]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06402_not_prime : ¬(recordGapCenter + 348632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348632]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06403_not_prime : ¬(recordGapCenter + 348666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348666]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06404_not_prime : ¬(recordGapCenter + 348716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348716]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06405_not_prime : ¬(recordGapCenter + 348882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348882]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06406_not_prime : ¬(recordGapCenter + 349142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349142]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06407_not_prime : ¬(recordGapCenter + 349196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349196]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06408_not_prime : ¬(recordGapCenter + 349242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349242]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06409_not_prime : ¬(recordGapCenter + 349266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349266]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06410_not_prime : ¬(recordGapCenter + 349298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349298]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06411_not_prime : ¬(recordGapCenter + 349352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349352]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06412_not_prime : ¬(recordGapCenter + 349358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349358]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06413_not_prime : ¬(recordGapCenter + 349386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349386]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06414_not_prime : ¬(recordGapCenter + 349458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349458]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06415_not_prime : ¬(recordGapCenter + 349626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349626]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06416_not_prime : ¬(recordGapCenter + 349658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349658]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06417_not_prime : ¬(recordGapCenter + 349718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349718]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06418_not_prime : ¬(recordGapCenter + 349736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349736]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06419_not_prime : ¬(recordGapCenter + 349886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349886]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06420_not_prime : ¬(recordGapCenter + 349920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349920]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06421_not_prime : ¬(recordGapCenter + 349926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349926]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06422_not_prime : ¬(recordGapCenter + 350000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350000]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06423_not_prime : ¬(recordGapCenter + 350072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350072]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06424_not_prime : ¬(recordGapCenter + 350156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350156]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06425_not_prime : ¬(recordGapCenter + 350282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350282]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06426_not_prime : ¬(recordGapCenter + 350312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350312]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06427_not_prime : ¬(recordGapCenter + 350408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350408]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06428_not_prime : ¬(recordGapCenter + 350418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350418]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06429_not_prime : ¬(recordGapCenter + 350466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350466]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06430_not_prime : ¬(recordGapCenter + 350502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350502]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06431_not_prime : ¬(recordGapCenter + 350562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350562]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06432_not_prime : ¬(recordGapCenter + 350582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350582]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06433_not_prime : ¬(recordGapCenter + 350666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350666]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06434_not_prime : ¬(recordGapCenter + 350862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350862]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06435_not_prime : ¬(recordGapCenter + 350876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350876]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06436_not_prime : ¬(recordGapCenter + 350936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350936]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06437_not_prime : ¬(recordGapCenter + 351066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351066]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06438_not_prime : ¬(recordGapCenter + 351146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351146]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06439_not_prime : ¬(recordGapCenter + 351188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351188]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06440_not_prime : ¬(recordGapCenter + 351222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351222]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06441_not_prime : ¬(recordGapCenter + 351326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351326]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06442_not_prime : ¬(recordGapCenter + 351332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351332]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06443_not_prime : ¬(recordGapCenter + 351398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351398]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06444_not_prime : ¬(recordGapCenter + 351506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351506]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06445_not_prime : ¬(recordGapCenter + 351782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351782]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06446_not_prime : ¬(recordGapCenter + 351836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351836]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06447_not_prime : ¬(recordGapCenter + 351942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351942]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06448_not_prime : ¬(recordGapCenter + 352046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352046]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06449_not_prime : ¬(recordGapCenter + 352076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352076]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06450_not_prime : ¬(recordGapCenter + 352082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352082]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06451_not_prime : ¬(recordGapCenter + 352122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352122]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06452_not_prime : ¬(recordGapCenter + 352158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352158]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06453_not_prime : ¬(recordGapCenter + 352266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352266]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06454_not_prime : ¬(recordGapCenter + 352322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352322]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06455_not_prime : ¬(recordGapCenter + 352382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352382]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06456_not_prime : ¬(recordGapCenter + 352398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352398]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06457_not_prime : ¬(recordGapCenter + 352472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352472]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06458_not_prime : ¬(recordGapCenter + 352542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352542]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06459_not_prime : ¬(recordGapCenter + 352626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352626]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06460_not_prime : ¬(recordGapCenter + 352800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352800]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06461_not_prime : ¬(recordGapCenter + 352808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352808]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06462_not_prime : ¬(recordGapCenter + 352892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352892]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06463_not_prime : ¬(recordGapCenter + 352952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352952]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06464_not_prime : ¬(recordGapCenter + 353018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353018]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06465_not_prime : ¬(recordGapCenter + 353042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353042]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06466_not_prime : ¬(recordGapCenter + 353048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353048]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06467_not_prime : ¬(recordGapCenter + 353222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353222]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06468_not_prime : ¬(recordGapCenter + 353348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353348]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06469_not_prime : ¬(recordGapCenter + 353406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353406]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06470_not_prime : ¬(recordGapCenter + 353442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353442]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06471_not_prime : ¬(recordGapCenter + 353516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353516]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06472_not_prime : ¬(recordGapCenter + 353658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353658]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06473_not_prime : ¬(recordGapCenter + 353768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353768]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06474_not_prime : ¬(recordGapCenter + 353876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353876]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06475_not_prime : ¬(recordGapCenter + 353946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353946]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06476_not_prime : ¬(recordGapCenter + 353966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353966]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06477_not_prime : ¬(recordGapCenter + 353972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353972]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06478_not_prime : ¬(recordGapCenter + 354092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354092]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06479_not_prime : ¬(recordGapCenter + 354126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354126]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06480_not_prime : ¬(recordGapCenter + 354182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354182]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06481_not_prime : ¬(recordGapCenter + 354422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354422]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06482_not_prime : ¬(recordGapCenter + 354446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354446]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06483_not_prime : ¬(recordGapCenter + 354572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354572]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06484_not_prime : ¬(recordGapCenter + 354758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354758]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06485_not_prime : ¬(recordGapCenter + 354816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354816]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06486_not_prime : ¬(recordGapCenter + 354842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354842]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06487_not_prime : ¬(recordGapCenter + 354846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354846]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06488_not_prime : ¬(recordGapCenter + 355002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355002]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06489_not_prime : ¬(recordGapCenter + 355022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355022]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06490_not_prime : ¬(recordGapCenter + 355182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355182]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06491_not_prime : ¬(recordGapCenter + 355478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355478]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06492_not_prime : ¬(recordGapCenter + 355526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355526]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06493_not_prime : ¬(recordGapCenter + 355622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355622]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06494_not_prime : ¬(recordGapCenter + 355638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355638]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06495_not_prime : ¬(recordGapCenter + 355686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355686]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06496_not_prime : ¬(recordGapCenter + 355766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355766]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06497_not_prime : ¬(recordGapCenter + 355826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355826]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06498_not_prime : ¬(recordGapCenter + 355988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355988]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06499_not_prime : ¬(recordGapCenter + 356036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356036]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06500_not_prime : ¬(recordGapCenter + 356042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356042]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06501_not_prime : ¬(recordGapCenter + 356186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356186]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06502_not_prime : ¬(recordGapCenter + 356228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356228]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06503_not_prime : ¬(recordGapCenter + 356276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356276]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06504_not_prime : ¬(recordGapCenter + 356322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356322]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06505_not_prime : ¬(recordGapCenter + 356358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356358]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06506_not_prime : ¬(recordGapCenter + 356492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356492]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06507_not_prime : ¬(recordGapCenter + 356498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356498]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06508_not_prime : ¬(recordGapCenter + 356666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356666]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06509_not_prime : ¬(recordGapCenter + 356786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356786]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06510_not_prime : ¬(recordGapCenter + 356802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356802]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06511_not_prime : ¬(recordGapCenter + 356882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356882]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06512_not_prime : ¬(recordGapCenter + 356948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356948]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06513_not_prime : ¬(recordGapCenter + 356982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356982]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06514_not_prime : ¬(recordGapCenter + 357002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357002]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06515_not_prime : ¬(recordGapCenter + 357026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357026]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06516_not_prime : ¬(recordGapCenter + 357092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357092]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06517_not_prime : ¬(recordGapCenter + 357218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357218]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06518_not_prime : ¬(recordGapCenter + 357242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357242]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06519_not_prime : ¬(recordGapCenter + 357402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357402]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06520_not_prime : ¬(recordGapCenter + 357548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357548]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06521_not_prime : ¬(recordGapCenter + 357596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357596]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06522_not_prime : ¬(recordGapCenter + 357662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357662]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06523_not_prime : ¬(recordGapCenter + 357668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357668]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06524_not_prime : ¬(recordGapCenter + 357726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357726]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06525_not_prime : ¬(recordGapCenter + 357746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357746]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06526_not_prime : ¬(recordGapCenter + 357806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357806]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06527_not_prime : ¬(recordGapCenter + 357908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357908]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06528_not_prime : ¬(recordGapCenter + 357978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357978]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06529_not_prime : ¬(recordGapCenter + 358076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358076]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06530_not_prime : ¬(recordGapCenter + 358082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358082]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06531_not_prime : ¬(recordGapCenter + 358158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358158]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06532_not_prime : ¬(recordGapCenter + 358166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358166]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06533_not_prime : ¬(recordGapCenter + 358286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358286]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06534_not_prime : ¬(recordGapCenter + 358338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358338]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06535_not_prime : ¬(recordGapCenter + 358400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358400]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06536_not_prime : ¬(recordGapCenter + 358412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358412]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06537_not_prime : ¬(recordGapCenter + 358458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358458]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06538_not_prime : ¬(recordGapCenter + 358538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358538]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06539_not_prime : ¬(recordGapCenter + 358562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358562]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06540_not_prime : ¬(recordGapCenter + 358676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358676]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06541_not_prime : ¬(recordGapCenter + 358782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358782]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06542_not_prime : ¬(recordGapCenter + 358922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358922]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06543_not_prime : ¬(recordGapCenter + 359066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359066]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06544_not_prime : ¬(recordGapCenter + 359096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359096]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06545_not_prime : ¬(recordGapCenter + 359186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359186]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06546_not_prime : ¬(recordGapCenter + 359276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359276]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06547_not_prime : ¬(recordGapCenter + 359318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359318]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06548_not_prime : ¬(recordGapCenter + 359342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359342]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06549_not_prime : ¬(recordGapCenter + 359588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359588]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06550_not_prime : ¬(recordGapCenter + 359672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359672]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06551_not_prime : ¬(recordGapCenter + 359846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359846]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06552_not_prime : ¬(recordGapCenter + 359886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359886]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06553_not_prime : ¬(recordGapCenter + 359978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359978]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06554_not_prime : ¬(recordGapCenter + 360056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360056]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06555_not_prime : ¬(recordGapCenter + 360078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360078]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06556_not_prime : ¬(recordGapCenter + 360236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360236]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06557_not_prime : ¬(recordGapCenter + 360362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360362]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06558_not_prime : ¬(recordGapCenter + 360428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360428]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06559_not_prime : ¬(recordGapCenter + 360546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360546]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06560_not_prime : ¬(recordGapCenter + 360596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360596]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06561_not_prime : ¬(recordGapCenter + 360722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360722]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06562_not_prime : ¬(recordGapCenter + 360762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360762]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06563_not_prime : ¬(recordGapCenter + 360782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360782]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06564_not_prime : ¬(recordGapCenter + 360788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360788]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06565_not_prime : ¬(recordGapCenter + 360812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360812]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06566_not_prime : ¬(recordGapCenter + 360908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360908]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06567_not_prime : ¬(recordGapCenter + 361002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361002]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06568_not_prime : ¬(recordGapCenter + 361502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361502]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06569_not_prime : ¬(recordGapCenter + 361506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361506]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06570_not_prime : ¬(recordGapCenter + 361586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361586]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06571_not_prime : ¬(recordGapCenter + 361628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361628]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06572_not_prime : ¬(recordGapCenter + 361898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361898]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06573_not_prime : ¬(recordGapCenter + 361902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361902]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06574_not_prime : ¬(recordGapCenter + 361986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361986]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06575_not_prime : ¬(recordGapCenter + 362078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362078]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06576_not_prime : ¬(recordGapCenter + 362238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362238]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06577_not_prime : ¬(recordGapCenter + 362282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362282]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06578_not_prime : ¬(recordGapCenter + 362486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362486]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06579_not_prime : ¬(recordGapCenter + 362546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362546]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06580_not_prime : ¬(recordGapCenter + 362552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362552]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06581_not_prime : ¬(recordGapCenter + 362588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362588]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06582_not_prime : ¬(recordGapCenter + 362636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362636]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06583_not_prime : ¬(recordGapCenter + 362658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362658]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06584_not_prime : ¬(recordGapCenter + 362708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362708]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06585_not_prime : ¬(recordGapCenter + 362958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362958]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06586_not_prime : ¬(recordGapCenter + 363000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363000]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06587_not_prime : ¬(recordGapCenter + 363002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363002]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06588_not_prime : ¬(recordGapCenter + 363098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363098]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06589_not_prime : ¬(recordGapCenter + 363126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363126]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06590_not_prime : ¬(recordGapCenter + 363338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363338]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06591_not_prime : ¬(recordGapCenter + 363452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363452]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06592_not_prime : ¬(recordGapCenter + 363512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363512]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06593_not_prime : ¬(recordGapCenter + 363578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363578]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06594_not_prime : ¬(recordGapCenter + 363606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363606]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06595_not_prime : ¬(recordGapCenter + 363702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363702]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06596_not_prime : ¬(recordGapCenter + 363738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363738]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06597_not_prime : ¬(recordGapCenter + 363746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363746]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06598_not_prime : ¬(recordGapCenter + 363806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363806]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06599_not_prime : ¬(recordGapCenter + 363882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363882]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06600_not_prime : ¬(recordGapCenter + 363956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363956]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06601_not_prime : ¬(recordGapCenter + 364022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364022]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06602_not_prime : ¬(recordGapCenter + 364082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364082]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06603_not_prime : ¬(recordGapCenter + 364218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364218]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06604_not_prime : ¬(recordGapCenter + 364262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364262]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06605_not_prime : ¬(recordGapCenter + 364358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364358]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06606_not_prime : ¬(recordGapCenter + 364478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364478]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06607_not_prime : ¬(recordGapCenter + 364500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364500]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06608_not_prime : ¬(recordGapCenter + 364556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364556]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06609_not_prime : ¬(recordGapCenter + 364578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364578]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06610_not_prime : ¬(recordGapCenter + 364652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364652]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06611_not_prime : ¬(recordGapCenter + 364758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364758]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06612_not_prime : ¬(recordGapCenter + 364772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364772]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06613_not_prime : ¬(recordGapCenter + 364946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364946]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06614_not_prime : ¬(recordGapCenter + 365018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365018]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06615_not_prime : ¬(recordGapCenter + 365198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365198]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06616_not_prime : ¬(recordGapCenter + 365282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365282]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06617_not_prime : ¬(recordGapCenter + 365426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365426]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06618_not_prime : ¬(recordGapCenter + 365478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365478]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06619_not_prime : ¬(recordGapCenter + 365492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365492]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06620_not_prime : ¬(recordGapCenter + 365558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365558]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06621_not_prime : ¬(recordGapCenter + 365576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365576]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06622_not_prime : ¬(recordGapCenter + 365622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365622]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06623_not_prime : ¬(recordGapCenter + 365642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365642]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06624_not_prime : ¬(recordGapCenter + 365678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365678]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06625_not_prime : ¬(recordGapCenter + 365828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365828]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06626_not_prime : ¬(recordGapCenter + 365858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365858]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06627_not_prime : ¬(recordGapCenter + 365996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365996]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06628_not_prime : ¬(recordGapCenter + 366006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366006]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06629_not_prime : ¬(recordGapCenter + 366182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366182]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06630_not_prime : ¬(recordGapCenter + 366258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366258]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06631_not_prime : ¬(recordGapCenter + 366332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366332]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06632_not_prime : ¬(recordGapCenter + 366342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366342]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06633_not_prime : ¬(recordGapCenter + 366518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366518]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06634_not_prime : ¬(recordGapCenter + 366566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366566]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06635_not_prime : ¬(recordGapCenter + 366578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366578]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06636_not_prime : ¬(recordGapCenter + 366602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366602]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06637_not_prime : ¬(recordGapCenter + 366686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366686]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06638_not_prime : ¬(recordGapCenter + 366746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366746]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06639_not_prime : ¬(recordGapCenter + 366812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366812]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06640_not_prime : ¬(recordGapCenter + 366902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366902]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06641_not_prime : ¬(recordGapCenter + 366998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366998]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06642_not_prime : ¬(recordGapCenter + 367266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367266]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06643_not_prime : ¬(recordGapCenter + 367322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367322]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06644_not_prime : ¬(recordGapCenter + 367416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367416]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06645_not_prime : ¬(recordGapCenter + 367518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367518]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06646_not_prime : ¬(recordGapCenter + 367782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367782]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06647_not_prime : ¬(recordGapCenter + 367838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367838]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06648_not_prime : ¬(recordGapCenter + 367986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367986]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06649_not_prime : ¬(recordGapCenter + 368006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368006]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06650_not_prime : ¬(recordGapCenter + 368036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368036]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06651_not_prime : ¬(recordGapCenter + 368162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368162]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06652_not_prime : ¬(recordGapCenter + 368168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368168]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06653_not_prime : ¬(recordGapCenter + 368216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368216]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06654_not_prime : ¬(recordGapCenter + 368418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368418]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06655_not_prime : ¬(recordGapCenter + 368546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368546]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm06656_not_prime : ¬(recordGapCenter + 368558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368558]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

end PrimeFactorUnimodality
