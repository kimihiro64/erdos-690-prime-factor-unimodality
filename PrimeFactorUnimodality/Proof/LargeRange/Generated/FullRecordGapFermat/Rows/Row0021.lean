import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00021_values : List Nat :=
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
    fullRecordGapCenterValue - 348562]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00021_fermat : ∀ n ∈ fullRecordGapRow00021_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01281_not_prime : ¬(recordGapCenter - 353482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353482]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01282_not_prime : ¬(recordGapCenter - 353454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353454]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01283_not_prime : ¬(recordGapCenter - 353422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353422]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01284_not_prime : ¬(recordGapCenter - 353308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353308]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01285_not_prime : ¬(recordGapCenter - 353194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353194]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01286_not_prime : ¬(recordGapCenter - 353062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353062]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01287_not_prime : ¬(recordGapCenter - 352984).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352984]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01288_not_prime : ¬(recordGapCenter - 352722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352722]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01289_not_prime : ¬(recordGapCenter - 352714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352714]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01290_not_prime : ¬(recordGapCenter - 352468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352468]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01291_not_prime : ¬(recordGapCenter - 352414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352414]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01292_not_prime : ¬(recordGapCenter - 352362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352362]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01293_not_prime : ¬(recordGapCenter - 352258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352258]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01294_not_prime : ¬(recordGapCenter - 352174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352174]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01295_not_prime : ¬(recordGapCenter - 352168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352168]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01296_not_prime : ¬(recordGapCenter - 352162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352162]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01297_not_prime : ¬(recordGapCenter - 352074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352074]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01298_not_prime : ¬(recordGapCenter - 352000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352000]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01299_not_prime : ¬(recordGapCenter - 351958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351958]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01300_not_prime : ¬(recordGapCenter - 351942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351942]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01301_not_prime : ¬(recordGapCenter - 351892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351892]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01302_not_prime : ¬(recordGapCenter - 351658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351658]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01303_not_prime : ¬(recordGapCenter - 351622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351622]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01304_not_prime : ¬(recordGapCenter - 351544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351544]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01305_not_prime : ¬(recordGapCenter - 351514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351514]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01306_not_prime : ¬(recordGapCenter - 351474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351474]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01307_not_prime : ¬(recordGapCenter - 351402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351402]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01308_not_prime : ¬(recordGapCenter - 351304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351304]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01309_not_prime : ¬(recordGapCenter - 351294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351294]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01310_not_prime : ¬(recordGapCenter - 351262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351262]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01311_not_prime : ¬(recordGapCenter - 351244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351244]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01312_not_prime : ¬(recordGapCenter - 351112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 351112]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01313_not_prime : ¬(recordGapCenter - 350884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350884]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01314_not_prime : ¬(recordGapCenter - 350788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350788]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01315_not_prime : ¬(recordGapCenter - 350698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350698]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01316_not_prime : ¬(recordGapCenter - 350634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350634]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01317_not_prime : ¬(recordGapCenter - 350572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350572]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01318_not_prime : ¬(recordGapCenter - 350524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350524]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01319_not_prime : ¬(recordGapCenter - 350502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350502]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01320_not_prime : ¬(recordGapCenter - 350418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350418]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01321_not_prime : ¬(recordGapCenter - 350214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 350214]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01322_not_prime : ¬(recordGapCenter - 349978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349978]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01323_not_prime : ¬(recordGapCenter - 349918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349918]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01324_not_prime : ¬(recordGapCenter - 349834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349834]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01325_not_prime : ¬(recordGapCenter - 349732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349732]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01326_not_prime : ¬(recordGapCenter - 349708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349708]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01327_not_prime : ¬(recordGapCenter - 349702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349702]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01328_not_prime : ¬(recordGapCenter - 349642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349642]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01329_not_prime : ¬(recordGapCenter - 349534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349534]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01330_not_prime : ¬(recordGapCenter - 349498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349498]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01331_not_prime : ¬(recordGapCenter - 349302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349302]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01332_not_prime : ¬(recordGapCenter - 349288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349288]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01333_not_prime : ¬(recordGapCenter - 349272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349272]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01334_not_prime : ¬(recordGapCenter - 349242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349242]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01335_not_prime : ¬(recordGapCenter - 349234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349234]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01336_not_prime : ¬(recordGapCenter - 349198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349198]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01337_not_prime : ¬(recordGapCenter - 349194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349194]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01338_not_prime : ¬(recordGapCenter - 349192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349192]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01339_not_prime : ¬(recordGapCenter - 349054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 349054]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01340_not_prime : ¬(recordGapCenter - 348904).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348904]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01341_not_prime : ¬(recordGapCenter - 348892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348892]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01342_not_prime : ¬(recordGapCenter - 348882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348882]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01343_not_prime : ¬(recordGapCenter - 348724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348724]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

theorem fullRecordGapTerm01344_not_prime : ¬(recordGapCenter - 348562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348562]
  · apply fullRecordGapRow00021_fermat
    simp [fullRecordGapRow00021_values]

end PrimeFactorUnimodality
