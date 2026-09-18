import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00006_values : List Nat :=
  [fullRecordGapCenterValue - 353482,
    fullRecordGapCenterValue - 353454,
    fullRecordGapCenterValue - 353422,
    fullRecordGapCenterValue - 353308,
    fullRecordGapCenterValue - 353194,
    fullRecordGapCenterValue - 353062,
    fullRecordGapCenterValue - 352984,
    fullRecordGapCenterValue - 352722,
    fullRecordGapCenterValue - 352714,
    fullRecordGapCenterValue - 352468,
    fullRecordGapCenterValue - 352414,
    fullRecordGapCenterValue - 352362,
    fullRecordGapCenterValue - 352258,
    fullRecordGapCenterValue - 352174,
    fullRecordGapCenterValue - 352168,
    fullRecordGapCenterValue - 352162,
    fullRecordGapCenterValue - 352074,
    fullRecordGapCenterValue - 352000,
    fullRecordGapCenterValue - 351958,
    fullRecordGapCenterValue - 351942,
    fullRecordGapCenterValue - 351892,
    fullRecordGapCenterValue - 351658,
    fullRecordGapCenterValue - 351622,
    fullRecordGapCenterValue - 351544,
    fullRecordGapCenterValue - 351514,
    fullRecordGapCenterValue - 351474,
    fullRecordGapCenterValue - 351402,
    fullRecordGapCenterValue - 351304,
    fullRecordGapCenterValue - 351294,
    fullRecordGapCenterValue - 351262,
    fullRecordGapCenterValue - 351244,
    fullRecordGapCenterValue - 351112,
    fullRecordGapCenterValue - 350884,
    fullRecordGapCenterValue - 350788,
    fullRecordGapCenterValue - 350698,
    fullRecordGapCenterValue - 350634,
    fullRecordGapCenterValue - 350572,
    fullRecordGapCenterValue - 350524,
    fullRecordGapCenterValue - 350502,
    fullRecordGapCenterValue - 350418,
    fullRecordGapCenterValue - 350214,
    fullRecordGapCenterValue - 349978,
    fullRecordGapCenterValue - 349918,
    fullRecordGapCenterValue - 349834,
    fullRecordGapCenterValue - 349732,
    fullRecordGapCenterValue - 349708,
    fullRecordGapCenterValue - 349702,
    fullRecordGapCenterValue - 349642,
    fullRecordGapCenterValue - 349534,
    fullRecordGapCenterValue - 349498,
    fullRecordGapCenterValue - 349302,
    fullRecordGapCenterValue - 349288,
    fullRecordGapCenterValue - 349272,
    fullRecordGapCenterValue - 349242,
    fullRecordGapCenterValue - 349234,
    fullRecordGapCenterValue - 349198,
    fullRecordGapCenterValue - 349194,
    fullRecordGapCenterValue - 349192,
    fullRecordGapCenterValue - 349054,
    fullRecordGapCenterValue - 348904,
    fullRecordGapCenterValue - 348892,
    fullRecordGapCenterValue - 348882,
    fullRecordGapCenterValue - 348724,
    fullRecordGapCenterValue - 348562,
    fullRecordGapCenterValue - 348438,
    fullRecordGapCenterValue - 348298,
    fullRecordGapCenterValue - 348294,
    fullRecordGapCenterValue - 348148,
    fullRecordGapCenterValue - 348078,
    fullRecordGapCenterValue - 348052,
    fullRecordGapCenterValue - 347938,
    fullRecordGapCenterValue - 347848,
    fullRecordGapCenterValue - 347818,
    fullRecordGapCenterValue - 347734,
    fullRecordGapCenterValue - 347722,
    fullRecordGapCenterValue - 347682,
    fullRecordGapCenterValue - 347554,
    fullRecordGapCenterValue - 347482,
    fullRecordGapCenterValue - 347458,
    fullRecordGapCenterValue - 347394,
    fullRecordGapCenterValue - 347224,
    fullRecordGapCenterValue - 347128,
    fullRecordGapCenterValue - 347034,
    fullRecordGapCenterValue - 346972,
    fullRecordGapCenterValue - 346722,
    fullRecordGapCenterValue - 346714,
    fullRecordGapCenterValue - 346638,
    fullRecordGapCenterValue - 346618,
    fullRecordGapCenterValue - 346552,
    fullRecordGapCenterValue - 346348,
    fullRecordGapCenterValue - 346282,
    fullRecordGapCenterValue - 346168,
    fullRecordGapCenterValue - 346162,
    fullRecordGapCenterValue - 346078,
    fullRecordGapCenterValue - 346002,
    fullRecordGapCenterValue - 345964,
    fullRecordGapCenterValue - 345784,
    fullRecordGapCenterValue - 345754,
    fullRecordGapCenterValue - 345744,
    fullRecordGapCenterValue - 345742,
    fullRecordGapCenterValue - 345718,
    fullRecordGapCenterValue - 345658,
    fullRecordGapCenterValue - 345652,
    fullRecordGapCenterValue - 345600,
    fullRecordGapCenterValue - 345354,
    fullRecordGapCenterValue - 345342,
    fullRecordGapCenterValue - 345292,
    fullRecordGapCenterValue - 345244,
    fullRecordGapCenterValue - 345208,
    fullRecordGapCenterValue - 345174,
    fullRecordGapCenterValue - 345172,
    fullRecordGapCenterValue - 345064,
    fullRecordGapCenterValue - 345034,
    fullRecordGapCenterValue - 345018,
    fullRecordGapCenterValue - 344958,
    fullRecordGapCenterValue - 344922,
    fullRecordGapCenterValue - 344742,
    fullRecordGapCenterValue - 344662,
    fullRecordGapCenterValue - 344644,
    fullRecordGapCenterValue - 344614,
    fullRecordGapCenterValue - 344572,
    fullRecordGapCenterValue - 344518,
    fullRecordGapCenterValue - 344452,
    fullRecordGapCenterValue - 344334,
    fullRecordGapCenterValue - 344332,
    fullRecordGapCenterValue - 344308,
    fullRecordGapCenterValue - 344298,
    fullRecordGapCenterValue - 344064,
    fullRecordGapCenterValue - 343762,
    fullRecordGapCenterValue - 343738,
    fullRecordGapCenterValue - 343614,
    fullRecordGapCenterValue - 343612,
    fullRecordGapCenterValue - 343522,
    fullRecordGapCenterValue - 343318,
    fullRecordGapCenterValue - 342898,
    fullRecordGapCenterValue - 342682,
    fullRecordGapCenterValue - 342634,
    fullRecordGapCenterValue - 342534,
    fullRecordGapCenterValue - 342508,
    fullRecordGapCenterValue - 342502,
    fullRecordGapCenterValue - 342484,
    fullRecordGapCenterValue - 342438,
    fullRecordGapCenterValue - 342388,
    fullRecordGapCenterValue - 342124,
    fullRecordGapCenterValue - 342094,
    fullRecordGapCenterValue - 342052,
    fullRecordGapCenterValue - 341914,
    fullRecordGapCenterValue - 341898,
    fullRecordGapCenterValue - 341854,
    fullRecordGapCenterValue - 341812,
    fullRecordGapCenterValue - 341742,
    fullRecordGapCenterValue - 341358,
    fullRecordGapCenterValue - 341338,
    fullRecordGapCenterValue - 341218,
    fullRecordGapCenterValue - 341212,
    fullRecordGapCenterValue - 341142,
    fullRecordGapCenterValue - 341058,
    fullRecordGapCenterValue - 340972,
    fullRecordGapCenterValue - 340962,
    fullRecordGapCenterValue - 340878,
    fullRecordGapCenterValue - 340854,
    fullRecordGapCenterValue - 340702,
    fullRecordGapCenterValue - 340638,
    fullRecordGapCenterValue - 340534,
    fullRecordGapCenterValue - 340422,
    fullRecordGapCenterValue - 340378,
    fullRecordGapCenterValue - 340372,
    fullRecordGapCenterValue - 340324,
    fullRecordGapCenterValue - 340282,
    fullRecordGapCenterValue - 340108,
    fullRecordGapCenterValue - 340084,
    fullRecordGapCenterValue - 340042,
    fullRecordGapCenterValue - 339982,
    fullRecordGapCenterValue - 339964,
    fullRecordGapCenterValue - 339954,
    fullRecordGapCenterValue - 339874,
    fullRecordGapCenterValue - 339868,
    fullRecordGapCenterValue - 339778,
    fullRecordGapCenterValue - 339652,
    fullRecordGapCenterValue - 339594,
    fullRecordGapCenterValue - 339582,
    fullRecordGapCenterValue - 339538,
    fullRecordGapCenterValue - 339418,
    fullRecordGapCenterValue - 339414,
    fullRecordGapCenterValue - 339258,
    fullRecordGapCenterValue - 339198,
    fullRecordGapCenterValue - 339114,
    fullRecordGapCenterValue - 338862,
    fullRecordGapCenterValue - 338818,
    fullRecordGapCenterValue - 338788,
    fullRecordGapCenterValue - 338722,
    fullRecordGapCenterValue - 338692,
    fullRecordGapCenterValue - 338658,
    fullRecordGapCenterValue - 338614,
    fullRecordGapCenterValue - 338502,
    fullRecordGapCenterValue - 338482,
    fullRecordGapCenterValue - 338398,
    fullRecordGapCenterValue - 338362,
    fullRecordGapCenterValue - 338158,
    fullRecordGapCenterValue - 338134,
    fullRecordGapCenterValue - 338098,
    fullRecordGapCenterValue - 338014,
    fullRecordGapCenterValue - 337998,
    fullRecordGapCenterValue - 337920,
    fullRecordGapCenterValue - 337798,
    fullRecordGapCenterValue - 337774,
    fullRecordGapCenterValue - 337684,
    fullRecordGapCenterValue - 337602,
    fullRecordGapCenterValue - 337500,
    fullRecordGapCenterValue - 337438,
    fullRecordGapCenterValue - 337354,
    fullRecordGapCenterValue - 337252,
    fullRecordGapCenterValue - 337234,
    fullRecordGapCenterValue - 337228,
    fullRecordGapCenterValue - 337074,
    fullRecordGapCenterValue - 337054,
    fullRecordGapCenterValue - 336898,
    fullRecordGapCenterValue - 336892,
    fullRecordGapCenterValue - 336844,
    fullRecordGapCenterValue - 336798,
    fullRecordGapCenterValue - 336594,
    fullRecordGapCenterValue - 336508,
    fullRecordGapCenterValue - 336394,
    fullRecordGapCenterValue - 336268,
    fullRecordGapCenterValue - 336244,
    fullRecordGapCenterValue - 336178,
    fullRecordGapCenterValue - 335932,
    fullRecordGapCenterValue - 335802,
    fullRecordGapCenterValue - 335782,
    fullRecordGapCenterValue - 335758,
    fullRecordGapCenterValue - 335554,
    fullRecordGapCenterValue - 335494,
    fullRecordGapCenterValue - 335458,
    fullRecordGapCenterValue - 335382,
    fullRecordGapCenterValue - 335254,
    fullRecordGapCenterValue - 335194,
    fullRecordGapCenterValue - 335092,
    fullRecordGapCenterValue - 335058,
    fullRecordGapCenterValue - 335022,
    fullRecordGapCenterValue - 334974,
    fullRecordGapCenterValue - 334942,
    fullRecordGapCenterValue - 334914,
    fullRecordGapCenterValue - 334758,
    fullRecordGapCenterValue - 334612,
    fullRecordGapCenterValue - 334534,
    fullRecordGapCenterValue - 334522,
    fullRecordGapCenterValue - 334498,
    fullRecordGapCenterValue - 334302,
    fullRecordGapCenterValue - 334234,
    fullRecordGapCenterValue - 334182,
    fullRecordGapCenterValue - 334102,
    fullRecordGapCenterValue - 334078,
    fullRecordGapCenterValue - 334018,
    fullRecordGapCenterValue - 334002,
    fullRecordGapCenterValue - 333798,
    fullRecordGapCenterValue - 333742]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00006_fermat : ∀ n ∈ fullRecordGapRow00006_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01281_not_prime : ¬(recordGapCenter - 353482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353482]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01282_not_prime : ¬(recordGapCenter - 353454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353454]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01283_not_prime : ¬(recordGapCenter - 353422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353422]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01284_not_prime : ¬(recordGapCenter - 353308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353308]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01285_not_prime : ¬(recordGapCenter - 353194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353194]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01286_not_prime : ¬(recordGapCenter - 353062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353062]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01287_not_prime : ¬(recordGapCenter - 352984).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352984]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01288_not_prime : ¬(recordGapCenter - 352722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352722]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01289_not_prime : ¬(recordGapCenter - 352714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352714]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01290_not_prime : ¬(recordGapCenter - 352468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352468]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01291_not_prime : ¬(recordGapCenter - 352414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352414]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01292_not_prime : ¬(recordGapCenter - 352362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352362]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01293_not_prime : ¬(recordGapCenter - 352258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352258]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01294_not_prime : ¬(recordGapCenter - 352174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352174]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01295_not_prime : ¬(recordGapCenter - 352168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352168]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01296_not_prime : ¬(recordGapCenter - 352162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352162]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01297_not_prime : ¬(recordGapCenter - 352074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352074]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01298_not_prime : ¬(recordGapCenter - 352000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352000]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01299_not_prime : ¬(recordGapCenter - 351958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351958]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01300_not_prime : ¬(recordGapCenter - 351942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351942]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01301_not_prime : ¬(recordGapCenter - 351892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351892]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01302_not_prime : ¬(recordGapCenter - 351658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351658]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01303_not_prime : ¬(recordGapCenter - 351622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351622]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01304_not_prime : ¬(recordGapCenter - 351544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351544]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01305_not_prime : ¬(recordGapCenter - 351514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351514]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01306_not_prime : ¬(recordGapCenter - 351474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351474]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01307_not_prime : ¬(recordGapCenter - 351402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351402]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01308_not_prime : ¬(recordGapCenter - 351304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351304]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01309_not_prime : ¬(recordGapCenter - 351294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351294]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01310_not_prime : ¬(recordGapCenter - 351262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351262]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01311_not_prime : ¬(recordGapCenter - 351244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351244]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01312_not_prime : ¬(recordGapCenter - 351112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351112]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01313_not_prime : ¬(recordGapCenter - 350884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350884]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01314_not_prime : ¬(recordGapCenter - 350788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350788]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01315_not_prime : ¬(recordGapCenter - 350698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350698]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01316_not_prime : ¬(recordGapCenter - 350634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350634]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01317_not_prime : ¬(recordGapCenter - 350572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350572]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01318_not_prime : ¬(recordGapCenter - 350524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350524]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01319_not_prime : ¬(recordGapCenter - 350502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350502]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01320_not_prime : ¬(recordGapCenter - 350418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350418]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01321_not_prime : ¬(recordGapCenter - 350214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350214]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01322_not_prime : ¬(recordGapCenter - 349978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349978]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01323_not_prime : ¬(recordGapCenter - 349918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349918]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01324_not_prime : ¬(recordGapCenter - 349834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349834]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01325_not_prime : ¬(recordGapCenter - 349732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349732]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01326_not_prime : ¬(recordGapCenter - 349708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349708]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01327_not_prime : ¬(recordGapCenter - 349702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349702]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01328_not_prime : ¬(recordGapCenter - 349642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349642]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01329_not_prime : ¬(recordGapCenter - 349534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349534]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01330_not_prime : ¬(recordGapCenter - 349498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349498]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01331_not_prime : ¬(recordGapCenter - 349302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349302]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01332_not_prime : ¬(recordGapCenter - 349288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349288]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01333_not_prime : ¬(recordGapCenter - 349272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349272]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01334_not_prime : ¬(recordGapCenter - 349242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349242]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01335_not_prime : ¬(recordGapCenter - 349234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349234]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01336_not_prime : ¬(recordGapCenter - 349198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349198]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01337_not_prime : ¬(recordGapCenter - 349194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349194]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01338_not_prime : ¬(recordGapCenter - 349192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349192]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01339_not_prime : ¬(recordGapCenter - 349054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349054]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01340_not_prime : ¬(recordGapCenter - 348904).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348904]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01341_not_prime : ¬(recordGapCenter - 348892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348892]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01342_not_prime : ¬(recordGapCenter - 348882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348882]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01343_not_prime : ¬(recordGapCenter - 348724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348724]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01344_not_prime : ¬(recordGapCenter - 348562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348562]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01345_not_prime : ¬(recordGapCenter - 348438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348438]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01346_not_prime : ¬(recordGapCenter - 348298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348298]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01347_not_prime : ¬(recordGapCenter - 348294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348294]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01348_not_prime : ¬(recordGapCenter - 348148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348148]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01349_not_prime : ¬(recordGapCenter - 348078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348078]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01350_not_prime : ¬(recordGapCenter - 348052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348052]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01351_not_prime : ¬(recordGapCenter - 347938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347938]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01352_not_prime : ¬(recordGapCenter - 347848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347848]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01353_not_prime : ¬(recordGapCenter - 347818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347818]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01354_not_prime : ¬(recordGapCenter - 347734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347734]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01355_not_prime : ¬(recordGapCenter - 347722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347722]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01356_not_prime : ¬(recordGapCenter - 347682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347682]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01357_not_prime : ¬(recordGapCenter - 347554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347554]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01358_not_prime : ¬(recordGapCenter - 347482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347482]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01359_not_prime : ¬(recordGapCenter - 347458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347458]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01360_not_prime : ¬(recordGapCenter - 347394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347394]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01361_not_prime : ¬(recordGapCenter - 347224).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347224]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01362_not_prime : ¬(recordGapCenter - 347128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347128]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01363_not_prime : ¬(recordGapCenter - 347034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347034]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01364_not_prime : ¬(recordGapCenter - 346972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346972]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01365_not_prime : ¬(recordGapCenter - 346722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346722]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01366_not_prime : ¬(recordGapCenter - 346714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346714]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01367_not_prime : ¬(recordGapCenter - 346638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346638]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01368_not_prime : ¬(recordGapCenter - 346618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346618]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01369_not_prime : ¬(recordGapCenter - 346552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346552]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01370_not_prime : ¬(recordGapCenter - 346348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346348]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01371_not_prime : ¬(recordGapCenter - 346282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346282]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01372_not_prime : ¬(recordGapCenter - 346168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346168]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01373_not_prime : ¬(recordGapCenter - 346162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346162]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01374_not_prime : ¬(recordGapCenter - 346078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346078]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01375_not_prime : ¬(recordGapCenter - 346002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346002]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01376_not_prime : ¬(recordGapCenter - 345964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345964]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01377_not_prime : ¬(recordGapCenter - 345784).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345784]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01378_not_prime : ¬(recordGapCenter - 345754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345754]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01379_not_prime : ¬(recordGapCenter - 345744).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345744]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01380_not_prime : ¬(recordGapCenter - 345742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345742]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01381_not_prime : ¬(recordGapCenter - 345718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345718]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01382_not_prime : ¬(recordGapCenter - 345658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345658]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01383_not_prime : ¬(recordGapCenter - 345652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345652]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01384_not_prime : ¬(recordGapCenter - 345600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345600]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01385_not_prime : ¬(recordGapCenter - 345354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345354]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01386_not_prime : ¬(recordGapCenter - 345342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345342]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01387_not_prime : ¬(recordGapCenter - 345292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345292]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01388_not_prime : ¬(recordGapCenter - 345244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345244]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01389_not_prime : ¬(recordGapCenter - 345208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345208]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01390_not_prime : ¬(recordGapCenter - 345174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345174]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01391_not_prime : ¬(recordGapCenter - 345172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345172]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01392_not_prime : ¬(recordGapCenter - 345064).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345064]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01393_not_prime : ¬(recordGapCenter - 345034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345034]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01394_not_prime : ¬(recordGapCenter - 345018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345018]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01395_not_prime : ¬(recordGapCenter - 344958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344958]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01396_not_prime : ¬(recordGapCenter - 344922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344922]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01397_not_prime : ¬(recordGapCenter - 344742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344742]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01398_not_prime : ¬(recordGapCenter - 344662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344662]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01399_not_prime : ¬(recordGapCenter - 344644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344644]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01400_not_prime : ¬(recordGapCenter - 344614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344614]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01401_not_prime : ¬(recordGapCenter - 344572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344572]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01402_not_prime : ¬(recordGapCenter - 344518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344518]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01403_not_prime : ¬(recordGapCenter - 344452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344452]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01404_not_prime : ¬(recordGapCenter - 344334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344334]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01405_not_prime : ¬(recordGapCenter - 344332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344332]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01406_not_prime : ¬(recordGapCenter - 344308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344308]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01407_not_prime : ¬(recordGapCenter - 344298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344298]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01408_not_prime : ¬(recordGapCenter - 344064).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344064]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01409_not_prime : ¬(recordGapCenter - 343762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343762]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01410_not_prime : ¬(recordGapCenter - 343738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343738]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01411_not_prime : ¬(recordGapCenter - 343614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343614]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01412_not_prime : ¬(recordGapCenter - 343612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343612]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01413_not_prime : ¬(recordGapCenter - 343522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343522]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01414_not_prime : ¬(recordGapCenter - 343318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343318]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01415_not_prime : ¬(recordGapCenter - 342898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342898]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01416_not_prime : ¬(recordGapCenter - 342682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342682]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01417_not_prime : ¬(recordGapCenter - 342634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342634]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01418_not_prime : ¬(recordGapCenter - 342534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342534]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01419_not_prime : ¬(recordGapCenter - 342508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342508]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01420_not_prime : ¬(recordGapCenter - 342502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342502]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01421_not_prime : ¬(recordGapCenter - 342484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342484]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01422_not_prime : ¬(recordGapCenter - 342438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342438]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01423_not_prime : ¬(recordGapCenter - 342388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342388]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01424_not_prime : ¬(recordGapCenter - 342124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342124]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01425_not_prime : ¬(recordGapCenter - 342094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342094]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01426_not_prime : ¬(recordGapCenter - 342052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342052]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01427_not_prime : ¬(recordGapCenter - 341914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341914]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01428_not_prime : ¬(recordGapCenter - 341898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341898]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01429_not_prime : ¬(recordGapCenter - 341854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341854]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01430_not_prime : ¬(recordGapCenter - 341812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341812]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01431_not_prime : ¬(recordGapCenter - 341742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341742]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01432_not_prime : ¬(recordGapCenter - 341358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341358]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01433_not_prime : ¬(recordGapCenter - 341338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341338]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01434_not_prime : ¬(recordGapCenter - 341218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341218]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01435_not_prime : ¬(recordGapCenter - 341212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341212]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01436_not_prime : ¬(recordGapCenter - 341142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341142]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01437_not_prime : ¬(recordGapCenter - 341058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341058]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01438_not_prime : ¬(recordGapCenter - 340972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340972]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01439_not_prime : ¬(recordGapCenter - 340962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340962]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01440_not_prime : ¬(recordGapCenter - 340878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340878]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01441_not_prime : ¬(recordGapCenter - 340854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340854]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01442_not_prime : ¬(recordGapCenter - 340702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340702]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01443_not_prime : ¬(recordGapCenter - 340638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340638]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01444_not_prime : ¬(recordGapCenter - 340534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340534]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01445_not_prime : ¬(recordGapCenter - 340422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340422]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01446_not_prime : ¬(recordGapCenter - 340378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340378]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01447_not_prime : ¬(recordGapCenter - 340372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340372]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01448_not_prime : ¬(recordGapCenter - 340324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340324]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01449_not_prime : ¬(recordGapCenter - 340282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340282]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01450_not_prime : ¬(recordGapCenter - 340108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340108]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01451_not_prime : ¬(recordGapCenter - 340084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340084]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01452_not_prime : ¬(recordGapCenter - 340042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340042]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01453_not_prime : ¬(recordGapCenter - 339982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339982]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01454_not_prime : ¬(recordGapCenter - 339964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339964]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01455_not_prime : ¬(recordGapCenter - 339954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339954]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01456_not_prime : ¬(recordGapCenter - 339874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339874]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01457_not_prime : ¬(recordGapCenter - 339868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339868]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01458_not_prime : ¬(recordGapCenter - 339778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339778]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01459_not_prime : ¬(recordGapCenter - 339652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339652]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01460_not_prime : ¬(recordGapCenter - 339594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339594]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01461_not_prime : ¬(recordGapCenter - 339582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339582]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01462_not_prime : ¬(recordGapCenter - 339538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339538]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01463_not_prime : ¬(recordGapCenter - 339418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339418]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01464_not_prime : ¬(recordGapCenter - 339414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339414]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01465_not_prime : ¬(recordGapCenter - 339258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339258]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01466_not_prime : ¬(recordGapCenter - 339198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339198]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01467_not_prime : ¬(recordGapCenter - 339114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339114]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01468_not_prime : ¬(recordGapCenter - 338862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338862]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01469_not_prime : ¬(recordGapCenter - 338818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338818]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01470_not_prime : ¬(recordGapCenter - 338788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338788]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01471_not_prime : ¬(recordGapCenter - 338722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338722]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01472_not_prime : ¬(recordGapCenter - 338692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338692]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01473_not_prime : ¬(recordGapCenter - 338658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338658]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01474_not_prime : ¬(recordGapCenter - 338614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338614]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01475_not_prime : ¬(recordGapCenter - 338502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338502]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01476_not_prime : ¬(recordGapCenter - 338482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338482]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01477_not_prime : ¬(recordGapCenter - 338398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338398]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01478_not_prime : ¬(recordGapCenter - 338362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338362]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01479_not_prime : ¬(recordGapCenter - 338158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338158]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01480_not_prime : ¬(recordGapCenter - 338134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338134]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01481_not_prime : ¬(recordGapCenter - 338098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338098]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01482_not_prime : ¬(recordGapCenter - 338014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338014]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01483_not_prime : ¬(recordGapCenter - 337998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337998]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01484_not_prime : ¬(recordGapCenter - 337920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337920]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01485_not_prime : ¬(recordGapCenter - 337798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337798]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01486_not_prime : ¬(recordGapCenter - 337774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337774]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01487_not_prime : ¬(recordGapCenter - 337684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337684]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01488_not_prime : ¬(recordGapCenter - 337602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337602]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01489_not_prime : ¬(recordGapCenter - 337500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337500]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01490_not_prime : ¬(recordGapCenter - 337438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337438]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01491_not_prime : ¬(recordGapCenter - 337354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337354]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01492_not_prime : ¬(recordGapCenter - 337252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337252]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01493_not_prime : ¬(recordGapCenter - 337234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337234]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01494_not_prime : ¬(recordGapCenter - 337228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337228]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01495_not_prime : ¬(recordGapCenter - 337074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337074]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01496_not_prime : ¬(recordGapCenter - 337054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337054]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01497_not_prime : ¬(recordGapCenter - 336898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336898]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01498_not_prime : ¬(recordGapCenter - 336892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336892]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01499_not_prime : ¬(recordGapCenter - 336844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336844]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01500_not_prime : ¬(recordGapCenter - 336798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336798]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01501_not_prime : ¬(recordGapCenter - 336594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336594]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01502_not_prime : ¬(recordGapCenter - 336508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336508]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01503_not_prime : ¬(recordGapCenter - 336394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336394]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01504_not_prime : ¬(recordGapCenter - 336268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336268]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01505_not_prime : ¬(recordGapCenter - 336244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336244]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01506_not_prime : ¬(recordGapCenter - 336178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336178]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01507_not_prime : ¬(recordGapCenter - 335932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335932]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01508_not_prime : ¬(recordGapCenter - 335802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335802]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01509_not_prime : ¬(recordGapCenter - 335782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335782]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01510_not_prime : ¬(recordGapCenter - 335758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335758]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01511_not_prime : ¬(recordGapCenter - 335554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335554]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01512_not_prime : ¬(recordGapCenter - 335494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335494]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01513_not_prime : ¬(recordGapCenter - 335458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335458]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01514_not_prime : ¬(recordGapCenter - 335382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335382]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01515_not_prime : ¬(recordGapCenter - 335254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335254]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01516_not_prime : ¬(recordGapCenter - 335194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335194]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01517_not_prime : ¬(recordGapCenter - 335092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335092]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01518_not_prime : ¬(recordGapCenter - 335058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335058]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01519_not_prime : ¬(recordGapCenter - 335022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335022]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01520_not_prime : ¬(recordGapCenter - 334974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334974]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01521_not_prime : ¬(recordGapCenter - 334942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334942]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01522_not_prime : ¬(recordGapCenter - 334914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334914]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01523_not_prime : ¬(recordGapCenter - 334758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334758]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01524_not_prime : ¬(recordGapCenter - 334612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334612]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01525_not_prime : ¬(recordGapCenter - 334534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334534]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01526_not_prime : ¬(recordGapCenter - 334522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334522]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01527_not_prime : ¬(recordGapCenter - 334498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334498]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01528_not_prime : ¬(recordGapCenter - 334302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334302]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01529_not_prime : ¬(recordGapCenter - 334234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334234]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01530_not_prime : ¬(recordGapCenter - 334182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334182]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01531_not_prime : ¬(recordGapCenter - 334102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334102]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01532_not_prime : ¬(recordGapCenter - 334078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334078]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01533_not_prime : ¬(recordGapCenter - 334018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334018]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01534_not_prime : ¬(recordGapCenter - 334002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334002]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01535_not_prime : ¬(recordGapCenter - 333798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333798]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm01536_not_prime : ¬(recordGapCenter - 333742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333742]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

end PrimeFactorUnimodality
