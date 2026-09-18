import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00003_values : List Nat :=
  [fullRecordGapCenterValue - 414892,
    fullRecordGapCenterValue - 414802,
    fullRecordGapCenterValue - 414762,
    fullRecordGapCenterValue - 414724,
    fullRecordGapCenterValue - 414720,
    fullRecordGapCenterValue - 414714,
    fullRecordGapCenterValue - 414658,
    fullRecordGapCenterValue - 414628,
    fullRecordGapCenterValue - 414574,
    fullRecordGapCenterValue - 414514,
    fullRecordGapCenterValue - 414424,
    fullRecordGapCenterValue - 414402,
    fullRecordGapCenterValue - 414382,
    fullRecordGapCenterValue - 414292,
    fullRecordGapCenterValue - 414174,
    fullRecordGapCenterValue - 413952,
    fullRecordGapCenterValue - 413878,
    fullRecordGapCenterValue - 413794,
    fullRecordGapCenterValue - 413682,
    fullRecordGapCenterValue - 413572,
    fullRecordGapCenterValue - 413562,
    fullRecordGapCenterValue - 413454,
    fullRecordGapCenterValue - 413332,
    fullRecordGapCenterValue - 413272,
    fullRecordGapCenterValue - 413194,
    fullRecordGapCenterValue - 413178,
    fullRecordGapCenterValue - 412978,
    fullRecordGapCenterValue - 412954,
    fullRecordGapCenterValue - 412914,
    fullRecordGapCenterValue - 412792,
    fullRecordGapCenterValue - 412732,
    fullRecordGapCenterValue - 412662,
    fullRecordGapCenterValue - 412564,
    fullRecordGapCenterValue - 412498,
    fullRecordGapCenterValue - 412492,
    fullRecordGapCenterValue - 412474,
    fullRecordGapCenterValue - 412458,
    fullRecordGapCenterValue - 412374,
    fullRecordGapCenterValue - 412354,
    fullRecordGapCenterValue - 412194,
    fullRecordGapCenterValue - 412078,
    fullRecordGapCenterValue - 412018,
    fullRecordGapCenterValue - 411934,
    fullRecordGapCenterValue - 411898,
    fullRecordGapCenterValue - 411834,
    fullRecordGapCenterValue - 411798,
    fullRecordGapCenterValue - 411724,
    fullRecordGapCenterValue - 411694,
    fullRecordGapCenterValue - 411688,
    fullRecordGapCenterValue - 411600,
    fullRecordGapCenterValue - 411592,
    fullRecordGapCenterValue - 411402,
    fullRecordGapCenterValue - 411058,
    fullRecordGapCenterValue - 410974,
    fullRecordGapCenterValue - 410728,
    fullRecordGapCenterValue - 410694,
    fullRecordGapCenterValue - 410692,
    fullRecordGapCenterValue - 410682,
    fullRecordGapCenterValue - 410668,
    fullRecordGapCenterValue - 410638,
    fullRecordGapCenterValue - 410314,
    fullRecordGapCenterValue - 410302,
    fullRecordGapCenterValue - 410104,
    fullRecordGapCenterValue - 410092,
    fullRecordGapCenterValue - 409948,
    fullRecordGapCenterValue - 409924,
    fullRecordGapCenterValue - 409894,
    fullRecordGapCenterValue - 409804,
    fullRecordGapCenterValue - 409624,
    fullRecordGapCenterValue - 409588,
    fullRecordGapCenterValue - 409582,
    fullRecordGapCenterValue - 409434,
    fullRecordGapCenterValue - 409348,
    fullRecordGapCenterValue - 409282,
    fullRecordGapCenterValue - 409198,
    fullRecordGapCenterValue - 409114,
    fullRecordGapCenterValue - 409042,
    fullRecordGapCenterValue - 409012,
    fullRecordGapCenterValue - 408922,
    fullRecordGapCenterValue - 408868,
    fullRecordGapCenterValue - 408862,
    fullRecordGapCenterValue - 408718,
    fullRecordGapCenterValue - 408678,
    fullRecordGapCenterValue - 408622,
    fullRecordGapCenterValue - 408568,
    fullRecordGapCenterValue - 408484,
    fullRecordGapCenterValue - 408354,
    fullRecordGapCenterValue - 408322,
    fullRecordGapCenterValue - 408274,
    fullRecordGapCenterValue - 408244,
    fullRecordGapCenterValue - 408240,
    fullRecordGapCenterValue - 408202,
    fullRecordGapCenterValue - 408124,
    fullRecordGapCenterValue - 408118,
    fullRecordGapCenterValue - 407998,
    fullRecordGapCenterValue - 407958,
    fullRecordGapCenterValue - 407938,
    fullRecordGapCenterValue - 407908,
    fullRecordGapCenterValue - 407634,
    fullRecordGapCenterValue - 407614,
    fullRecordGapCenterValue - 407578,
    fullRecordGapCenterValue - 407188,
    fullRecordGapCenterValue - 407182,
    fullRecordGapCenterValue - 406948,
    fullRecordGapCenterValue - 406774,
    fullRecordGapCenterValue - 406702,
    fullRecordGapCenterValue - 406444,
    fullRecordGapCenterValue - 406282,
    fullRecordGapCenterValue - 406114,
    fullRecordGapCenterValue - 406108,
    fullRecordGapCenterValue - 406024,
    fullRecordGapCenterValue - 405934,
    fullRecordGapCenterValue - 405814,
    fullRecordGapCenterValue - 405778,
    fullRecordGapCenterValue - 405718,
    fullRecordGapCenterValue - 405642,
    fullRecordGapCenterValue - 405534,
    fullRecordGapCenterValue - 405514,
    fullRecordGapCenterValue - 405402,
    fullRecordGapCenterValue - 405388,
    fullRecordGapCenterValue - 405148,
    fullRecordGapCenterValue - 405138,
    fullRecordGapCenterValue - 405124,
    fullRecordGapCenterValue - 404962,
    fullRecordGapCenterValue - 404812,
    fullRecordGapCenterValue - 404788,
    fullRecordGapCenterValue - 404728,
    fullRecordGapCenterValue - 404682,
    fullRecordGapCenterValue - 404644,
    fullRecordGapCenterValue - 404598,
    fullRecordGapCenterValue - 404578,
    fullRecordGapCenterValue - 404428,
    fullRecordGapCenterValue - 404394,
    fullRecordGapCenterValue - 404344,
    fullRecordGapCenterValue - 404242,
    fullRecordGapCenterValue - 404134,
    fullRecordGapCenterValue - 404058,
    fullRecordGapCenterValue - 403948,
    fullRecordGapCenterValue - 403842,
    fullRecordGapCenterValue - 403828,
    fullRecordGapCenterValue - 403822,
    fullRecordGapCenterValue - 403654,
    fullRecordGapCenterValue - 403582,
    fullRecordGapCenterValue - 403534,
    fullRecordGapCenterValue - 403288,
    fullRecordGapCenterValue - 403204,
    fullRecordGapCenterValue - 403200,
    fullRecordGapCenterValue - 403122,
    fullRecordGapCenterValue - 403114,
    fullRecordGapCenterValue - 402988,
    fullRecordGapCenterValue - 402964,
    fullRecordGapCenterValue - 402898,
    fullRecordGapCenterValue - 402874,
    fullRecordGapCenterValue - 402834,
    fullRecordGapCenterValue - 402618,
    fullRecordGapCenterValue - 402562,
    fullRecordGapCenterValue - 402502,
    fullRecordGapCenterValue - 402484,
    fullRecordGapCenterValue - 402474,
    fullRecordGapCenterValue - 402418,
    fullRecordGapCenterValue - 402342,
    fullRecordGapCenterValue - 402202,
    fullRecordGapCenterValue - 401848,
    fullRecordGapCenterValue - 401818,
    fullRecordGapCenterValue - 401788,
    fullRecordGapCenterValue - 401754,
    fullRecordGapCenterValue - 401734,
    fullRecordGapCenterValue - 401722,
    fullRecordGapCenterValue - 401644,
    fullRecordGapCenterValue - 401572,
    fullRecordGapCenterValue - 401334,
    fullRecordGapCenterValue - 401278,
    fullRecordGapCenterValue - 401272,
    fullRecordGapCenterValue - 401188,
    fullRecordGapCenterValue - 401182,
    fullRecordGapCenterValue - 401118,
    fullRecordGapCenterValue - 401068,
    fullRecordGapCenterValue - 401032,
    fullRecordGapCenterValue - 400984,
    fullRecordGapCenterValue - 400948,
    fullRecordGapCenterValue - 400854,
    fullRecordGapCenterValue - 400782,
    fullRecordGapCenterValue - 400762,
    fullRecordGapCenterValue - 400732,
    fullRecordGapCenterValue - 400714,
    fullRecordGapCenterValue - 400612,
    fullRecordGapCenterValue - 400354,
    fullRecordGapCenterValue - 400342,
    fullRecordGapCenterValue - 400318,
    fullRecordGapCenterValue - 400234,
    fullRecordGapCenterValue - 400182,
    fullRecordGapCenterValue - 400098,
    fullRecordGapCenterValue - 400018,
    fullRecordGapCenterValue - 400012,
    fullRecordGapCenterValue - 399934,
    fullRecordGapCenterValue - 399774,
    fullRecordGapCenterValue - 399628,
    fullRecordGapCenterValue - 399604,
    fullRecordGapCenterValue - 399558,
    fullRecordGapCenterValue - 399508,
    fullRecordGapCenterValue - 399318,
    fullRecordGapCenterValue - 399292,
    fullRecordGapCenterValue - 399198,
    fullRecordGapCenterValue - 399174,
    fullRecordGapCenterValue - 399138,
    fullRecordGapCenterValue - 399054,
    fullRecordGapCenterValue - 398914,
    fullRecordGapCenterValue - 398884,
    fullRecordGapCenterValue - 398758,
    fullRecordGapCenterValue - 398694,
    fullRecordGapCenterValue - 398668,
    fullRecordGapCenterValue - 398572,
    fullRecordGapCenterValue - 398488,
    fullRecordGapCenterValue - 398478,
    fullRecordGapCenterValue - 398362,
    fullRecordGapCenterValue - 398302,
    fullRecordGapCenterValue - 398218,
    fullRecordGapCenterValue - 398092,
    fullRecordGapCenterValue - 398082,
    fullRecordGapCenterValue - 398074,
    fullRecordGapCenterValue - 398058,
    fullRecordGapCenterValue - 397858,
    fullRecordGapCenterValue - 397798,
    fullRecordGapCenterValue - 397758,
    fullRecordGapCenterValue - 397402,
    fullRecordGapCenterValue - 397198,
    fullRecordGapCenterValue - 397108,
    fullRecordGapCenterValue - 396904,
    fullRecordGapCenterValue - 396900,
    fullRecordGapCenterValue - 396892,
    fullRecordGapCenterValue - 396822,
    fullRecordGapCenterValue - 396724,
    fullRecordGapCenterValue - 396562,
    fullRecordGapCenterValue - 396534,
    fullRecordGapCenterValue - 396442,
    fullRecordGapCenterValue - 396412,
    fullRecordGapCenterValue - 396174,
    fullRecordGapCenterValue - 395842,
    fullRecordGapCenterValue - 395818,
    fullRecordGapCenterValue - 395644,
    fullRecordGapCenterValue - 395574,
    fullRecordGapCenterValue - 395464,
    fullRecordGapCenterValue - 395394,
    fullRecordGapCenterValue - 395202,
    fullRecordGapCenterValue - 395134,
    fullRecordGapCenterValue - 395022,
    fullRecordGapCenterValue - 394734,
    fullRecordGapCenterValue - 394678,
    fullRecordGapCenterValue - 394558,
    fullRecordGapCenterValue - 394522,
    fullRecordGapCenterValue - 394314,
    fullRecordGapCenterValue - 394294,
    fullRecordGapCenterValue - 394242,
    fullRecordGapCenterValue - 394194,
    fullRecordGapCenterValue - 394018,
    fullRecordGapCenterValue - 393942]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00003_fermat : ∀ n ∈ fullRecordGapRow00003_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00513_not_prime : ¬(recordGapCenter - 414892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414892]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00514_not_prime : ¬(recordGapCenter - 414802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414802]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00515_not_prime : ¬(recordGapCenter - 414762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414762]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00516_not_prime : ¬(recordGapCenter - 414724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414724]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00517_not_prime : ¬(recordGapCenter - 414720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414720]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00518_not_prime : ¬(recordGapCenter - 414714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414714]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00519_not_prime : ¬(recordGapCenter - 414658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414658]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00520_not_prime : ¬(recordGapCenter - 414628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414628]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00521_not_prime : ¬(recordGapCenter - 414574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414574]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00522_not_prime : ¬(recordGapCenter - 414514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414514]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00523_not_prime : ¬(recordGapCenter - 414424).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414424]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00524_not_prime : ¬(recordGapCenter - 414402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414402]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00525_not_prime : ¬(recordGapCenter - 414382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414382]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00526_not_prime : ¬(recordGapCenter - 414292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414292]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00527_not_prime : ¬(recordGapCenter - 414174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414174]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00528_not_prime : ¬(recordGapCenter - 413952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413952]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00529_not_prime : ¬(recordGapCenter - 413878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413878]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00530_not_prime : ¬(recordGapCenter - 413794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413794]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00531_not_prime : ¬(recordGapCenter - 413682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413682]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00532_not_prime : ¬(recordGapCenter - 413572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413572]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00533_not_prime : ¬(recordGapCenter - 413562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413562]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00534_not_prime : ¬(recordGapCenter - 413454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413454]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00535_not_prime : ¬(recordGapCenter - 413332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413332]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00536_not_prime : ¬(recordGapCenter - 413272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413272]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00537_not_prime : ¬(recordGapCenter - 413194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413194]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00538_not_prime : ¬(recordGapCenter - 413178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413178]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00539_not_prime : ¬(recordGapCenter - 412978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412978]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00540_not_prime : ¬(recordGapCenter - 412954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412954]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00541_not_prime : ¬(recordGapCenter - 412914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412914]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00542_not_prime : ¬(recordGapCenter - 412792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412792]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00543_not_prime : ¬(recordGapCenter - 412732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412732]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00544_not_prime : ¬(recordGapCenter - 412662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412662]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00545_not_prime : ¬(recordGapCenter - 412564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412564]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00546_not_prime : ¬(recordGapCenter - 412498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412498]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00547_not_prime : ¬(recordGapCenter - 412492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412492]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00548_not_prime : ¬(recordGapCenter - 412474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412474]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00549_not_prime : ¬(recordGapCenter - 412458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412458]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00550_not_prime : ¬(recordGapCenter - 412374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412374]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00551_not_prime : ¬(recordGapCenter - 412354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412354]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00552_not_prime : ¬(recordGapCenter - 412194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412194]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00553_not_prime : ¬(recordGapCenter - 412078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412078]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00554_not_prime : ¬(recordGapCenter - 412018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412018]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00555_not_prime : ¬(recordGapCenter - 411934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411934]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00556_not_prime : ¬(recordGapCenter - 411898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411898]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00557_not_prime : ¬(recordGapCenter - 411834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411834]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00558_not_prime : ¬(recordGapCenter - 411798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411798]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00559_not_prime : ¬(recordGapCenter - 411724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411724]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00560_not_prime : ¬(recordGapCenter - 411694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411694]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00561_not_prime : ¬(recordGapCenter - 411688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411688]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00562_not_prime : ¬(recordGapCenter - 411600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411600]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00563_not_prime : ¬(recordGapCenter - 411592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411592]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00564_not_prime : ¬(recordGapCenter - 411402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411402]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00565_not_prime : ¬(recordGapCenter - 411058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411058]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00566_not_prime : ¬(recordGapCenter - 410974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410974]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00567_not_prime : ¬(recordGapCenter - 410728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410728]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00568_not_prime : ¬(recordGapCenter - 410694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410694]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00569_not_prime : ¬(recordGapCenter - 410692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410692]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00570_not_prime : ¬(recordGapCenter - 410682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410682]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00571_not_prime : ¬(recordGapCenter - 410668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410668]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00572_not_prime : ¬(recordGapCenter - 410638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410638]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00573_not_prime : ¬(recordGapCenter - 410314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410314]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00574_not_prime : ¬(recordGapCenter - 410302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410302]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00575_not_prime : ¬(recordGapCenter - 410104).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410104]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00576_not_prime : ¬(recordGapCenter - 410092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410092]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00577_not_prime : ¬(recordGapCenter - 409948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409948]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00578_not_prime : ¬(recordGapCenter - 409924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409924]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00579_not_prime : ¬(recordGapCenter - 409894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409894]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00580_not_prime : ¬(recordGapCenter - 409804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409804]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00581_not_prime : ¬(recordGapCenter - 409624).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409624]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00582_not_prime : ¬(recordGapCenter - 409588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409588]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00583_not_prime : ¬(recordGapCenter - 409582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409582]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00584_not_prime : ¬(recordGapCenter - 409434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409434]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00585_not_prime : ¬(recordGapCenter - 409348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409348]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00586_not_prime : ¬(recordGapCenter - 409282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409282]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00587_not_prime : ¬(recordGapCenter - 409198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409198]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00588_not_prime : ¬(recordGapCenter - 409114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409114]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00589_not_prime : ¬(recordGapCenter - 409042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409042]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00590_not_prime : ¬(recordGapCenter - 409012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409012]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00591_not_prime : ¬(recordGapCenter - 408922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408922]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00592_not_prime : ¬(recordGapCenter - 408868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408868]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00593_not_prime : ¬(recordGapCenter - 408862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408862]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00594_not_prime : ¬(recordGapCenter - 408718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408718]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00595_not_prime : ¬(recordGapCenter - 408678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408678]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00596_not_prime : ¬(recordGapCenter - 408622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408622]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00597_not_prime : ¬(recordGapCenter - 408568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408568]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00598_not_prime : ¬(recordGapCenter - 408484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408484]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00599_not_prime : ¬(recordGapCenter - 408354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408354]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00600_not_prime : ¬(recordGapCenter - 408322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408322]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00601_not_prime : ¬(recordGapCenter - 408274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408274]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00602_not_prime : ¬(recordGapCenter - 408244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408244]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00603_not_prime : ¬(recordGapCenter - 408240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408240]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00604_not_prime : ¬(recordGapCenter - 408202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408202]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00605_not_prime : ¬(recordGapCenter - 408124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408124]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00606_not_prime : ¬(recordGapCenter - 408118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408118]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00607_not_prime : ¬(recordGapCenter - 407998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407998]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00608_not_prime : ¬(recordGapCenter - 407958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407958]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00609_not_prime : ¬(recordGapCenter - 407938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407938]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00610_not_prime : ¬(recordGapCenter - 407908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407908]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00611_not_prime : ¬(recordGapCenter - 407634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407634]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00612_not_prime : ¬(recordGapCenter - 407614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407614]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00613_not_prime : ¬(recordGapCenter - 407578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407578]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00614_not_prime : ¬(recordGapCenter - 407188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407188]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00615_not_prime : ¬(recordGapCenter - 407182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407182]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00616_not_prime : ¬(recordGapCenter - 406948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406948]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00617_not_prime : ¬(recordGapCenter - 406774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406774]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00618_not_prime : ¬(recordGapCenter - 406702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406702]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00619_not_prime : ¬(recordGapCenter - 406444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406444]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00620_not_prime : ¬(recordGapCenter - 406282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406282]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00621_not_prime : ¬(recordGapCenter - 406114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406114]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00622_not_prime : ¬(recordGapCenter - 406108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406108]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00623_not_prime : ¬(recordGapCenter - 406024).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406024]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00624_not_prime : ¬(recordGapCenter - 405934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405934]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00625_not_prime : ¬(recordGapCenter - 405814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405814]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00626_not_prime : ¬(recordGapCenter - 405778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405778]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00627_not_prime : ¬(recordGapCenter - 405718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405718]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00628_not_prime : ¬(recordGapCenter - 405642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405642]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00629_not_prime : ¬(recordGapCenter - 405534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405534]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00630_not_prime : ¬(recordGapCenter - 405514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405514]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00631_not_prime : ¬(recordGapCenter - 405402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405402]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00632_not_prime : ¬(recordGapCenter - 405388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405388]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00633_not_prime : ¬(recordGapCenter - 405148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405148]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00634_not_prime : ¬(recordGapCenter - 405138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405138]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00635_not_prime : ¬(recordGapCenter - 405124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405124]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00636_not_prime : ¬(recordGapCenter - 404962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404962]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00637_not_prime : ¬(recordGapCenter - 404812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404812]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00638_not_prime : ¬(recordGapCenter - 404788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404788]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00639_not_prime : ¬(recordGapCenter - 404728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404728]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00640_not_prime : ¬(recordGapCenter - 404682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404682]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00641_not_prime : ¬(recordGapCenter - 404644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404644]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00642_not_prime : ¬(recordGapCenter - 404598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404598]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00643_not_prime : ¬(recordGapCenter - 404578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404578]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00644_not_prime : ¬(recordGapCenter - 404428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404428]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00645_not_prime : ¬(recordGapCenter - 404394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404394]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00646_not_prime : ¬(recordGapCenter - 404344).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404344]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00647_not_prime : ¬(recordGapCenter - 404242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404242]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00648_not_prime : ¬(recordGapCenter - 404134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404134]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00649_not_prime : ¬(recordGapCenter - 404058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404058]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00650_not_prime : ¬(recordGapCenter - 403948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403948]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00651_not_prime : ¬(recordGapCenter - 403842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403842]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00652_not_prime : ¬(recordGapCenter - 403828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403828]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00653_not_prime : ¬(recordGapCenter - 403822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403822]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00654_not_prime : ¬(recordGapCenter - 403654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403654]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00655_not_prime : ¬(recordGapCenter - 403582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403582]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00656_not_prime : ¬(recordGapCenter - 403534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403534]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00657_not_prime : ¬(recordGapCenter - 403288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403288]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00658_not_prime : ¬(recordGapCenter - 403204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403204]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00659_not_prime : ¬(recordGapCenter - 403200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403200]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00660_not_prime : ¬(recordGapCenter - 403122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403122]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00661_not_prime : ¬(recordGapCenter - 403114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403114]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00662_not_prime : ¬(recordGapCenter - 402988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402988]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00663_not_prime : ¬(recordGapCenter - 402964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402964]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00664_not_prime : ¬(recordGapCenter - 402898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402898]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00665_not_prime : ¬(recordGapCenter - 402874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402874]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00666_not_prime : ¬(recordGapCenter - 402834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402834]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00667_not_prime : ¬(recordGapCenter - 402618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402618]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00668_not_prime : ¬(recordGapCenter - 402562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402562]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00669_not_prime : ¬(recordGapCenter - 402502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402502]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00670_not_prime : ¬(recordGapCenter - 402484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402484]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00671_not_prime : ¬(recordGapCenter - 402474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402474]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00672_not_prime : ¬(recordGapCenter - 402418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402418]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00673_not_prime : ¬(recordGapCenter - 402342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402342]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00674_not_prime : ¬(recordGapCenter - 402202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402202]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00675_not_prime : ¬(recordGapCenter - 401848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401848]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00676_not_prime : ¬(recordGapCenter - 401818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401818]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00677_not_prime : ¬(recordGapCenter - 401788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401788]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00678_not_prime : ¬(recordGapCenter - 401754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401754]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00679_not_prime : ¬(recordGapCenter - 401734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401734]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00680_not_prime : ¬(recordGapCenter - 401722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401722]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00681_not_prime : ¬(recordGapCenter - 401644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401644]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00682_not_prime : ¬(recordGapCenter - 401572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401572]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00683_not_prime : ¬(recordGapCenter - 401334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401334]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00684_not_prime : ¬(recordGapCenter - 401278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401278]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00685_not_prime : ¬(recordGapCenter - 401272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401272]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00686_not_prime : ¬(recordGapCenter - 401188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401188]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00687_not_prime : ¬(recordGapCenter - 401182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401182]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00688_not_prime : ¬(recordGapCenter - 401118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401118]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00689_not_prime : ¬(recordGapCenter - 401068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401068]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00690_not_prime : ¬(recordGapCenter - 401032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401032]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00691_not_prime : ¬(recordGapCenter - 400984).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400984]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00692_not_prime : ¬(recordGapCenter - 400948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400948]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00693_not_prime : ¬(recordGapCenter - 400854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400854]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00694_not_prime : ¬(recordGapCenter - 400782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400782]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00695_not_prime : ¬(recordGapCenter - 400762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400762]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00696_not_prime : ¬(recordGapCenter - 400732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400732]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00697_not_prime : ¬(recordGapCenter - 400714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400714]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00698_not_prime : ¬(recordGapCenter - 400612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400612]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00699_not_prime : ¬(recordGapCenter - 400354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400354]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00700_not_prime : ¬(recordGapCenter - 400342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400342]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00701_not_prime : ¬(recordGapCenter - 400318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400318]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00702_not_prime : ¬(recordGapCenter - 400234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400234]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00703_not_prime : ¬(recordGapCenter - 400182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400182]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00704_not_prime : ¬(recordGapCenter - 400098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400098]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00705_not_prime : ¬(recordGapCenter - 400018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400018]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00706_not_prime : ¬(recordGapCenter - 400012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400012]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00707_not_prime : ¬(recordGapCenter - 399934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399934]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00708_not_prime : ¬(recordGapCenter - 399774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399774]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00709_not_prime : ¬(recordGapCenter - 399628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399628]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00710_not_prime : ¬(recordGapCenter - 399604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399604]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00711_not_prime : ¬(recordGapCenter - 399558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399558]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00712_not_prime : ¬(recordGapCenter - 399508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399508]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00713_not_prime : ¬(recordGapCenter - 399318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399318]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00714_not_prime : ¬(recordGapCenter - 399292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399292]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00715_not_prime : ¬(recordGapCenter - 399198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399198]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00716_not_prime : ¬(recordGapCenter - 399174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399174]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00717_not_prime : ¬(recordGapCenter - 399138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399138]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00718_not_prime : ¬(recordGapCenter - 399054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399054]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00719_not_prime : ¬(recordGapCenter - 398914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398914]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00720_not_prime : ¬(recordGapCenter - 398884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398884]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00721_not_prime : ¬(recordGapCenter - 398758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398758]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00722_not_prime : ¬(recordGapCenter - 398694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398694]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00723_not_prime : ¬(recordGapCenter - 398668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398668]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00724_not_prime : ¬(recordGapCenter - 398572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398572]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00725_not_prime : ¬(recordGapCenter - 398488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398488]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00726_not_prime : ¬(recordGapCenter - 398478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398478]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00727_not_prime : ¬(recordGapCenter - 398362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398362]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00728_not_prime : ¬(recordGapCenter - 398302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398302]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00729_not_prime : ¬(recordGapCenter - 398218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398218]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00730_not_prime : ¬(recordGapCenter - 398092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398092]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00731_not_prime : ¬(recordGapCenter - 398082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398082]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00732_not_prime : ¬(recordGapCenter - 398074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398074]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00733_not_prime : ¬(recordGapCenter - 398058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398058]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00734_not_prime : ¬(recordGapCenter - 397858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397858]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00735_not_prime : ¬(recordGapCenter - 397798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397798]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00736_not_prime : ¬(recordGapCenter - 397758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397758]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00737_not_prime : ¬(recordGapCenter - 397402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397402]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00738_not_prime : ¬(recordGapCenter - 397198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397198]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00739_not_prime : ¬(recordGapCenter - 397108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397108]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00740_not_prime : ¬(recordGapCenter - 396904).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396904]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00741_not_prime : ¬(recordGapCenter - 396900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396900]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00742_not_prime : ¬(recordGapCenter - 396892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396892]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00743_not_prime : ¬(recordGapCenter - 396822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396822]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00744_not_prime : ¬(recordGapCenter - 396724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396724]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00745_not_prime : ¬(recordGapCenter - 396562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396562]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00746_not_prime : ¬(recordGapCenter - 396534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396534]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00747_not_prime : ¬(recordGapCenter - 396442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396442]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00748_not_prime : ¬(recordGapCenter - 396412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396412]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00749_not_prime : ¬(recordGapCenter - 396174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396174]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00750_not_prime : ¬(recordGapCenter - 395842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395842]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00751_not_prime : ¬(recordGapCenter - 395818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395818]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00752_not_prime : ¬(recordGapCenter - 395644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395644]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00753_not_prime : ¬(recordGapCenter - 395574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395574]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00754_not_prime : ¬(recordGapCenter - 395464).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395464]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00755_not_prime : ¬(recordGapCenter - 395394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395394]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00756_not_prime : ¬(recordGapCenter - 395202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395202]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00757_not_prime : ¬(recordGapCenter - 395134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395134]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00758_not_prime : ¬(recordGapCenter - 395022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395022]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00759_not_prime : ¬(recordGapCenter - 394734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394734]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00760_not_prime : ¬(recordGapCenter - 394678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394678]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00761_not_prime : ¬(recordGapCenter - 394558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394558]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00762_not_prime : ¬(recordGapCenter - 394522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394522]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00763_not_prime : ¬(recordGapCenter - 394314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394314]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00764_not_prime : ¬(recordGapCenter - 394294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394294]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00765_not_prime : ¬(recordGapCenter - 394242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394242]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00766_not_prime : ¬(recordGapCenter - 394194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394194]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00767_not_prime : ¬(recordGapCenter - 394018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394018]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

theorem fullRecordGapTerm00768_not_prime : ¬(recordGapCenter - 393942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393942]
  · apply fullRecordGapRow00003_fermat
    simp [fullRecordGapRow00003_values]

end PrimeFactorUnimodality
