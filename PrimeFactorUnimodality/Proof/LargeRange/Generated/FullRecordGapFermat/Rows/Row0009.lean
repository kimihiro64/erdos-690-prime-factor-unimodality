import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00009_values : List Nat :=
  [fullRecordGapCenterValue - 288994,
    fullRecordGapCenterValue - 288892,
    fullRecordGapCenterValue - 288844,
    fullRecordGapCenterValue - 288682,
    fullRecordGapCenterValue - 288474,
    fullRecordGapCenterValue - 288322,
    fullRecordGapCenterValue - 288294,
    fullRecordGapCenterValue - 288174,
    fullRecordGapCenterValue - 288172,
    fullRecordGapCenterValue - 288124,
    fullRecordGapCenterValue - 288120,
    fullRecordGapCenterValue - 288000,
    fullRecordGapCenterValue - 287884,
    fullRecordGapCenterValue - 287662,
    fullRecordGapCenterValue - 287634,
    fullRecordGapCenterValue - 287548,
    fullRecordGapCenterValue - 287502,
    fullRecordGapCenterValue - 287458,
    fullRecordGapCenterValue - 287418,
    fullRecordGapCenterValue - 287284,
    fullRecordGapCenterValue - 286978,
    fullRecordGapCenterValue - 286954,
    fullRecordGapCenterValue - 286828,
    fullRecordGapCenterValue - 286720,
    fullRecordGapCenterValue - 286684,
    fullRecordGapCenterValue - 286674,
    fullRecordGapCenterValue - 286662,
    fullRecordGapCenterValue - 286372,
    fullRecordGapCenterValue - 286302,
    fullRecordGapCenterValue - 286282,
    fullRecordGapCenterValue - 286204,
    fullRecordGapCenterValue - 286108,
    fullRecordGapCenterValue - 285954,
    fullRecordGapCenterValue - 285942,
    fullRecordGapCenterValue - 285898,
    fullRecordGapCenterValue - 285742,
    fullRecordGapCenterValue - 285738,
    fullRecordGapCenterValue - 285598,
    fullRecordGapCenterValue - 285394,
    fullRecordGapCenterValue - 285378,
    fullRecordGapCenterValue - 285198,
    fullRecordGapCenterValue - 285148,
    fullRecordGapCenterValue - 285120,
    fullRecordGapCenterValue - 285042,
    fullRecordGapCenterValue - 284938,
    fullRecordGapCenterValue - 284932,
    fullRecordGapCenterValue - 284764,
    fullRecordGapCenterValue - 284644,
    fullRecordGapCenterValue - 284638,
    fullRecordGapCenterValue - 284592,
    fullRecordGapCenterValue - 284542,
    fullRecordGapCenterValue - 284422,
    fullRecordGapCenterValue - 284322,
    fullRecordGapCenterValue - 284302,
    fullRecordGapCenterValue - 284044,
    fullRecordGapCenterValue - 284038,
    fullRecordGapCenterValue - 283854,
    fullRecordGapCenterValue - 283828,
    fullRecordGapCenterValue - 283818,
    fullRecordGapCenterValue - 283702,
    fullRecordGapCenterValue - 283684,
    fullRecordGapCenterValue - 283614,
    fullRecordGapCenterValue - 283534,
    fullRecordGapCenterValue - 283500,
    fullRecordGapCenterValue - 283174,
    fullRecordGapCenterValue - 283134,
    fullRecordGapCenterValue - 282994,
    fullRecordGapCenterValue - 282922,
    fullRecordGapCenterValue - 282868,
    fullRecordGapCenterValue - 282774,
    fullRecordGapCenterValue - 282508,
    fullRecordGapCenterValue - 282442,
    fullRecordGapCenterValue - 282354,
    fullRecordGapCenterValue - 282292,
    fullRecordGapCenterValue - 282214,
    fullRecordGapCenterValue - 282102,
    fullRecordGapCenterValue - 281734,
    fullRecordGapCenterValue - 281518,
    fullRecordGapCenterValue - 281458,
    fullRecordGapCenterValue - 281434,
    fullRecordGapCenterValue - 281262,
    fullRecordGapCenterValue - 280954,
    fullRecordGapCenterValue - 280762,
    fullRecordGapCenterValue - 280594,
    fullRecordGapCenterValue - 280564,
    fullRecordGapCenterValue - 280542,
    fullRecordGapCenterValue - 280468,
    fullRecordGapCenterValue - 280362,
    fullRecordGapCenterValue - 280342,
    fullRecordGapCenterValue - 280338,
    fullRecordGapCenterValue - 280122,
    fullRecordGapCenterValue - 280012,
    fullRecordGapCenterValue - 279988,
    fullRecordGapCenterValue - 279982,
    fullRecordGapCenterValue - 279934,
    fullRecordGapCenterValue - 279834,
    fullRecordGapCenterValue - 279814,
    fullRecordGapCenterValue - 279724,
    fullRecordGapCenterValue - 279534,
    fullRecordGapCenterValue - 279478,
    fullRecordGapCenterValue - 279418,
    fullRecordGapCenterValue - 279402,
    fullRecordGapCenterValue - 279388,
    fullRecordGapCenterValue - 279178,
    fullRecordGapCenterValue - 279142,
    fullRecordGapCenterValue - 278934,
    fullRecordGapCenterValue - 278862,
    fullRecordGapCenterValue - 278742,
    fullRecordGapCenterValue - 278682,
    fullRecordGapCenterValue - 278644,
    fullRecordGapCenterValue - 278602,
    fullRecordGapCenterValue - 278394,
    fullRecordGapCenterValue - 278374,
    fullRecordGapCenterValue - 278338,
    fullRecordGapCenterValue - 278218,
    fullRecordGapCenterValue - 278158,
    fullRecordGapCenterValue - 277954,
    fullRecordGapCenterValue - 277918,
    fullRecordGapCenterValue - 277834,
    fullRecordGapCenterValue - 277828,
    fullRecordGapCenterValue - 277738,
    fullRecordGapCenterValue - 277708,
    fullRecordGapCenterValue - 277674,
    fullRecordGapCenterValue - 277638,
    fullRecordGapCenterValue - 277462,
    fullRecordGapCenterValue - 277374,
    fullRecordGapCenterValue - 277294,
    fullRecordGapCenterValue - 277252,
    fullRecordGapCenterValue - 277200,
    fullRecordGapCenterValue - 277162,
    fullRecordGapCenterValue - 277122,
    fullRecordGapCenterValue - 276988,
    fullRecordGapCenterValue - 276814,
    fullRecordGapCenterValue - 276618,
    fullRecordGapCenterValue - 276604,
    fullRecordGapCenterValue - 276594,
    fullRecordGapCenterValue - 276502,
    fullRecordGapCenterValue - 276358,
    fullRecordGapCenterValue - 276294,
    fullRecordGapCenterValue - 276268,
    fullRecordGapCenterValue - 276162,
    fullRecordGapCenterValue - 276154,
    fullRecordGapCenterValue - 276124,
    fullRecordGapCenterValue - 275788,
    fullRecordGapCenterValue - 275734,
    fullRecordGapCenterValue - 275718,
    fullRecordGapCenterValue - 275694,
    fullRecordGapCenterValue - 275562,
    fullRecordGapCenterValue - 275524,
    fullRecordGapCenterValue - 275214,
    fullRecordGapCenterValue - 275194,
    fullRecordGapCenterValue - 275118,
    fullRecordGapCenterValue - 274972,
    fullRecordGapCenterValue - 274902,
    fullRecordGapCenterValue - 274738,
    fullRecordGapCenterValue - 274732,
    fullRecordGapCenterValue - 274678,
    fullRecordGapCenterValue - 274578,
    fullRecordGapCenterValue - 274558,
    fullRecordGapCenterValue - 274402,
    fullRecordGapCenterValue - 274242,
    fullRecordGapCenterValue - 274084,
    fullRecordGapCenterValue - 273982,
    fullRecordGapCenterValue - 273748,
    fullRecordGapCenterValue - 273682,
    fullRecordGapCenterValue - 273622,
    fullRecordGapCenterValue - 273538,
    fullRecordGapCenterValue - 273534,
    fullRecordGapCenterValue - 273502,
    fullRecordGapCenterValue - 273454,
    fullRecordGapCenterValue - 273318,
    fullRecordGapCenterValue - 273214,
    fullRecordGapCenterValue - 273198,
    fullRecordGapCenterValue - 273018,
    fullRecordGapCenterValue - 272962,
    fullRecordGapCenterValue - 272908,
    fullRecordGapCenterValue - 272638,
    fullRecordGapCenterValue - 272284,
    fullRecordGapCenterValue - 272262,
    fullRecordGapCenterValue - 272212,
    fullRecordGapCenterValue - 272092,
    fullRecordGapCenterValue - 271974,
    fullRecordGapCenterValue - 271954,
    fullRecordGapCenterValue - 271948,
    fullRecordGapCenterValue - 271914,
    fullRecordGapCenterValue - 271842,
    fullRecordGapCenterValue - 271798,
    fullRecordGapCenterValue - 271758,
    fullRecordGapCenterValue - 271732,
    fullRecordGapCenterValue - 271578,
    fullRecordGapCenterValue - 271564,
    fullRecordGapCenterValue - 271554,
    fullRecordGapCenterValue - 271438,
    fullRecordGapCenterValue - 271294,
    fullRecordGapCenterValue - 271204,
    fullRecordGapCenterValue - 271162,
    fullRecordGapCenterValue - 270958,
    fullRecordGapCenterValue - 270898,
    fullRecordGapCenterValue - 270862,
    fullRecordGapCenterValue - 270834,
    fullRecordGapCenterValue - 270822,
    fullRecordGapCenterValue - 270694,
    fullRecordGapCenterValue - 270562,
    fullRecordGapCenterValue - 270462,
    fullRecordGapCenterValue - 270268,
    fullRecordGapCenterValue - 270262,
    fullRecordGapCenterValue - 270238,
    fullRecordGapCenterValue - 270118,
    fullRecordGapCenterValue - 270078,
    fullRecordGapCenterValue - 269842,
    fullRecordGapCenterValue - 269734,
    fullRecordGapCenterValue - 269562,
    fullRecordGapCenterValue - 269554,
    fullRecordGapCenterValue - 269398,
    fullRecordGapCenterValue - 269362,
    fullRecordGapCenterValue - 269358,
    fullRecordGapCenterValue - 269322,
    fullRecordGapCenterValue - 269092,
    fullRecordGapCenterValue - 269058,
    fullRecordGapCenterValue - 269044,
    fullRecordGapCenterValue - 268678,
    fullRecordGapCenterValue - 268638,
    fullRecordGapCenterValue - 268564,
    fullRecordGapCenterValue - 268098,
    fullRecordGapCenterValue - 268084,
    fullRecordGapCenterValue - 268012,
    fullRecordGapCenterValue - 267958,
    fullRecordGapCenterValue - 267892,
    fullRecordGapCenterValue - 267538,
    fullRecordGapCenterValue - 267522,
    fullRecordGapCenterValue - 267474,
    fullRecordGapCenterValue - 267378,
    fullRecordGapCenterValue - 267118,
    fullRecordGapCenterValue - 266998,
    fullRecordGapCenterValue - 266902,
    fullRecordGapCenterValue - 266878,
    fullRecordGapCenterValue - 266782,
    fullRecordGapCenterValue - 266758,
    fullRecordGapCenterValue - 266698,
    fullRecordGapCenterValue - 266404,
    fullRecordGapCenterValue - 266338,
    fullRecordGapCenterValue - 266298,
    fullRecordGapCenterValue - 266242,
    fullRecordGapCenterValue - 266112,
    fullRecordGapCenterValue - 265942,
    fullRecordGapCenterValue - 265858,
    fullRecordGapCenterValue - 265828,
    fullRecordGapCenterValue - 265822,
    fullRecordGapCenterValue - 265758,
    fullRecordGapCenterValue - 265674,
    fullRecordGapCenterValue - 265614,
    fullRecordGapCenterValue - 265612,
    fullRecordGapCenterValue - 265578,
    fullRecordGapCenterValue - 265498,
    fullRecordGapCenterValue - 265372,
    fullRecordGapCenterValue - 265348]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00009_fermat : ∀ n ∈ fullRecordGapRow00009_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02049_not_prime : ¬(recordGapCenter - 288994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288994]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02050_not_prime : ¬(recordGapCenter - 288892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288892]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02051_not_prime : ¬(recordGapCenter - 288844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288844]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02052_not_prime : ¬(recordGapCenter - 288682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288682]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02053_not_prime : ¬(recordGapCenter - 288474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288474]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02054_not_prime : ¬(recordGapCenter - 288322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288322]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02055_not_prime : ¬(recordGapCenter - 288294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288294]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02056_not_prime : ¬(recordGapCenter - 288174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288174]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02057_not_prime : ¬(recordGapCenter - 288172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288172]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02058_not_prime : ¬(recordGapCenter - 288124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288124]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02059_not_prime : ¬(recordGapCenter - 288120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288120]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02060_not_prime : ¬(recordGapCenter - 288000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 288000]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02061_not_prime : ¬(recordGapCenter - 287884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287884]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02062_not_prime : ¬(recordGapCenter - 287662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287662]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02063_not_prime : ¬(recordGapCenter - 287634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287634]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02064_not_prime : ¬(recordGapCenter - 287548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287548]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02065_not_prime : ¬(recordGapCenter - 287502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287502]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02066_not_prime : ¬(recordGapCenter - 287458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287458]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02067_not_prime : ¬(recordGapCenter - 287418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287418]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02068_not_prime : ¬(recordGapCenter - 287284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 287284]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02069_not_prime : ¬(recordGapCenter - 286978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286978]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02070_not_prime : ¬(recordGapCenter - 286954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286954]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02071_not_prime : ¬(recordGapCenter - 286828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286828]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02072_not_prime : ¬(recordGapCenter - 286720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286720]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02073_not_prime : ¬(recordGapCenter - 286684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286684]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02074_not_prime : ¬(recordGapCenter - 286674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286674]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02075_not_prime : ¬(recordGapCenter - 286662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286662]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02076_not_prime : ¬(recordGapCenter - 286372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286372]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02077_not_prime : ¬(recordGapCenter - 286302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286302]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02078_not_prime : ¬(recordGapCenter - 286282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286282]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02079_not_prime : ¬(recordGapCenter - 286204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286204]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02080_not_prime : ¬(recordGapCenter - 286108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 286108]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02081_not_prime : ¬(recordGapCenter - 285954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285954]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02082_not_prime : ¬(recordGapCenter - 285942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285942]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02083_not_prime : ¬(recordGapCenter - 285898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285898]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02084_not_prime : ¬(recordGapCenter - 285742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285742]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02085_not_prime : ¬(recordGapCenter - 285738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285738]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02086_not_prime : ¬(recordGapCenter - 285598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285598]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02087_not_prime : ¬(recordGapCenter - 285394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285394]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02088_not_prime : ¬(recordGapCenter - 285378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285378]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02089_not_prime : ¬(recordGapCenter - 285198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285198]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02090_not_prime : ¬(recordGapCenter - 285148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285148]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02091_not_prime : ¬(recordGapCenter - 285120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285120]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02092_not_prime : ¬(recordGapCenter - 285042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 285042]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02093_not_prime : ¬(recordGapCenter - 284938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284938]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02094_not_prime : ¬(recordGapCenter - 284932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284932]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02095_not_prime : ¬(recordGapCenter - 284764).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284764]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02096_not_prime : ¬(recordGapCenter - 284644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284644]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02097_not_prime : ¬(recordGapCenter - 284638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284638]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02098_not_prime : ¬(recordGapCenter - 284592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284592]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02099_not_prime : ¬(recordGapCenter - 284542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284542]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02100_not_prime : ¬(recordGapCenter - 284422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284422]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02101_not_prime : ¬(recordGapCenter - 284322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284322]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02102_not_prime : ¬(recordGapCenter - 284302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284302]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02103_not_prime : ¬(recordGapCenter - 284044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284044]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02104_not_prime : ¬(recordGapCenter - 284038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 284038]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02105_not_prime : ¬(recordGapCenter - 283854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283854]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02106_not_prime : ¬(recordGapCenter - 283828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283828]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02107_not_prime : ¬(recordGapCenter - 283818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283818]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02108_not_prime : ¬(recordGapCenter - 283702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283702]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02109_not_prime : ¬(recordGapCenter - 283684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283684]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02110_not_prime : ¬(recordGapCenter - 283614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283614]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02111_not_prime : ¬(recordGapCenter - 283534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283534]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02112_not_prime : ¬(recordGapCenter - 283500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283500]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02113_not_prime : ¬(recordGapCenter - 283174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283174]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02114_not_prime : ¬(recordGapCenter - 283134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283134]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02115_not_prime : ¬(recordGapCenter - 282994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282994]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02116_not_prime : ¬(recordGapCenter - 282922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282922]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02117_not_prime : ¬(recordGapCenter - 282868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282868]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02118_not_prime : ¬(recordGapCenter - 282774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282774]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02119_not_prime : ¬(recordGapCenter - 282508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282508]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02120_not_prime : ¬(recordGapCenter - 282442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282442]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02121_not_prime : ¬(recordGapCenter - 282354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282354]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02122_not_prime : ¬(recordGapCenter - 282292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282292]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02123_not_prime : ¬(recordGapCenter - 282214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282214]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02124_not_prime : ¬(recordGapCenter - 282102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282102]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02125_not_prime : ¬(recordGapCenter - 281734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281734]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02126_not_prime : ¬(recordGapCenter - 281518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281518]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02127_not_prime : ¬(recordGapCenter - 281458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281458]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02128_not_prime : ¬(recordGapCenter - 281434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281434]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02129_not_prime : ¬(recordGapCenter - 281262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281262]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02130_not_prime : ¬(recordGapCenter - 280954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280954]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02131_not_prime : ¬(recordGapCenter - 280762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280762]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02132_not_prime : ¬(recordGapCenter - 280594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280594]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02133_not_prime : ¬(recordGapCenter - 280564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280564]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02134_not_prime : ¬(recordGapCenter - 280542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280542]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02135_not_prime : ¬(recordGapCenter - 280468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280468]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02136_not_prime : ¬(recordGapCenter - 280362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280362]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02137_not_prime : ¬(recordGapCenter - 280342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280342]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02138_not_prime : ¬(recordGapCenter - 280338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280338]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02139_not_prime : ¬(recordGapCenter - 280122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280122]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02140_not_prime : ¬(recordGapCenter - 280012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280012]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02141_not_prime : ¬(recordGapCenter - 279988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279988]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02142_not_prime : ¬(recordGapCenter - 279982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279982]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02143_not_prime : ¬(recordGapCenter - 279934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279934]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02144_not_prime : ¬(recordGapCenter - 279834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279834]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02145_not_prime : ¬(recordGapCenter - 279814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279814]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02146_not_prime : ¬(recordGapCenter - 279724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279724]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02147_not_prime : ¬(recordGapCenter - 279534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279534]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02148_not_prime : ¬(recordGapCenter - 279478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279478]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02149_not_prime : ¬(recordGapCenter - 279418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279418]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02150_not_prime : ¬(recordGapCenter - 279402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279402]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02151_not_prime : ¬(recordGapCenter - 279388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279388]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02152_not_prime : ¬(recordGapCenter - 279178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279178]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02153_not_prime : ¬(recordGapCenter - 279142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279142]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02154_not_prime : ¬(recordGapCenter - 278934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278934]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02155_not_prime : ¬(recordGapCenter - 278862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278862]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02156_not_prime : ¬(recordGapCenter - 278742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278742]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02157_not_prime : ¬(recordGapCenter - 278682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278682]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02158_not_prime : ¬(recordGapCenter - 278644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278644]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02159_not_prime : ¬(recordGapCenter - 278602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278602]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02160_not_prime : ¬(recordGapCenter - 278394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278394]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02161_not_prime : ¬(recordGapCenter - 278374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278374]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02162_not_prime : ¬(recordGapCenter - 278338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278338]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02163_not_prime : ¬(recordGapCenter - 278218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278218]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02164_not_prime : ¬(recordGapCenter - 278158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278158]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02165_not_prime : ¬(recordGapCenter - 277954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277954]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02166_not_prime : ¬(recordGapCenter - 277918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277918]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02167_not_prime : ¬(recordGapCenter - 277834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277834]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02168_not_prime : ¬(recordGapCenter - 277828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277828]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02169_not_prime : ¬(recordGapCenter - 277738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277738]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02170_not_prime : ¬(recordGapCenter - 277708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277708]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02171_not_prime : ¬(recordGapCenter - 277674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277674]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02172_not_prime : ¬(recordGapCenter - 277638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277638]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02173_not_prime : ¬(recordGapCenter - 277462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277462]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02174_not_prime : ¬(recordGapCenter - 277374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277374]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02175_not_prime : ¬(recordGapCenter - 277294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277294]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02176_not_prime : ¬(recordGapCenter - 277252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277252]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02177_not_prime : ¬(recordGapCenter - 277200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277200]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02178_not_prime : ¬(recordGapCenter - 277162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277162]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02179_not_prime : ¬(recordGapCenter - 277122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277122]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02180_not_prime : ¬(recordGapCenter - 276988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276988]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02181_not_prime : ¬(recordGapCenter - 276814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276814]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02182_not_prime : ¬(recordGapCenter - 276618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276618]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02183_not_prime : ¬(recordGapCenter - 276604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276604]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02184_not_prime : ¬(recordGapCenter - 276594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276594]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02185_not_prime : ¬(recordGapCenter - 276502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276502]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02186_not_prime : ¬(recordGapCenter - 276358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276358]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02187_not_prime : ¬(recordGapCenter - 276294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276294]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02188_not_prime : ¬(recordGapCenter - 276268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276268]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02189_not_prime : ¬(recordGapCenter - 276162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276162]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02190_not_prime : ¬(recordGapCenter - 276154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276154]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02191_not_prime : ¬(recordGapCenter - 276124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276124]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02192_not_prime : ¬(recordGapCenter - 275788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275788]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02193_not_prime : ¬(recordGapCenter - 275734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275734]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02194_not_prime : ¬(recordGapCenter - 275718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275718]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02195_not_prime : ¬(recordGapCenter - 275694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275694]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02196_not_prime : ¬(recordGapCenter - 275562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275562]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02197_not_prime : ¬(recordGapCenter - 275524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275524]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02198_not_prime : ¬(recordGapCenter - 275214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275214]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02199_not_prime : ¬(recordGapCenter - 275194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275194]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02200_not_prime : ¬(recordGapCenter - 275118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275118]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02201_not_prime : ¬(recordGapCenter - 274972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274972]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02202_not_prime : ¬(recordGapCenter - 274902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274902]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02203_not_prime : ¬(recordGapCenter - 274738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274738]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02204_not_prime : ¬(recordGapCenter - 274732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274732]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02205_not_prime : ¬(recordGapCenter - 274678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274678]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02206_not_prime : ¬(recordGapCenter - 274578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274578]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02207_not_prime : ¬(recordGapCenter - 274558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274558]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02208_not_prime : ¬(recordGapCenter - 274402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274402]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02209_not_prime : ¬(recordGapCenter - 274242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274242]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02210_not_prime : ¬(recordGapCenter - 274084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274084]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02211_not_prime : ¬(recordGapCenter - 273982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273982]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02212_not_prime : ¬(recordGapCenter - 273748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273748]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02213_not_prime : ¬(recordGapCenter - 273682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273682]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02214_not_prime : ¬(recordGapCenter - 273622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273622]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02215_not_prime : ¬(recordGapCenter - 273538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273538]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02216_not_prime : ¬(recordGapCenter - 273534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273534]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02217_not_prime : ¬(recordGapCenter - 273502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273502]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02218_not_prime : ¬(recordGapCenter - 273454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273454]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02219_not_prime : ¬(recordGapCenter - 273318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273318]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02220_not_prime : ¬(recordGapCenter - 273214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273214]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02221_not_prime : ¬(recordGapCenter - 273198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273198]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02222_not_prime : ¬(recordGapCenter - 273018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273018]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02223_not_prime : ¬(recordGapCenter - 272962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272962]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02224_not_prime : ¬(recordGapCenter - 272908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272908]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02225_not_prime : ¬(recordGapCenter - 272638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272638]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02226_not_prime : ¬(recordGapCenter - 272284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272284]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02227_not_prime : ¬(recordGapCenter - 272262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272262]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02228_not_prime : ¬(recordGapCenter - 272212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272212]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02229_not_prime : ¬(recordGapCenter - 272092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272092]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02230_not_prime : ¬(recordGapCenter - 271974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271974]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02231_not_prime : ¬(recordGapCenter - 271954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271954]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02232_not_prime : ¬(recordGapCenter - 271948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271948]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02233_not_prime : ¬(recordGapCenter - 271914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271914]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02234_not_prime : ¬(recordGapCenter - 271842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271842]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02235_not_prime : ¬(recordGapCenter - 271798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271798]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02236_not_prime : ¬(recordGapCenter - 271758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271758]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02237_not_prime : ¬(recordGapCenter - 271732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271732]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02238_not_prime : ¬(recordGapCenter - 271578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271578]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02239_not_prime : ¬(recordGapCenter - 271564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271564]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02240_not_prime : ¬(recordGapCenter - 271554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271554]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02241_not_prime : ¬(recordGapCenter - 271438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271438]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02242_not_prime : ¬(recordGapCenter - 271294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271294]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02243_not_prime : ¬(recordGapCenter - 271204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271204]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02244_not_prime : ¬(recordGapCenter - 271162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271162]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02245_not_prime : ¬(recordGapCenter - 270958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270958]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02246_not_prime : ¬(recordGapCenter - 270898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270898]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02247_not_prime : ¬(recordGapCenter - 270862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270862]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02248_not_prime : ¬(recordGapCenter - 270834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270834]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02249_not_prime : ¬(recordGapCenter - 270822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270822]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02250_not_prime : ¬(recordGapCenter - 270694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270694]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02251_not_prime : ¬(recordGapCenter - 270562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270562]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02252_not_prime : ¬(recordGapCenter - 270462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270462]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02253_not_prime : ¬(recordGapCenter - 270268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270268]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02254_not_prime : ¬(recordGapCenter - 270262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270262]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02255_not_prime : ¬(recordGapCenter - 270238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270238]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02256_not_prime : ¬(recordGapCenter - 270118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270118]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02257_not_prime : ¬(recordGapCenter - 270078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270078]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02258_not_prime : ¬(recordGapCenter - 269842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269842]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02259_not_prime : ¬(recordGapCenter - 269734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269734]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02260_not_prime : ¬(recordGapCenter - 269562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269562]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02261_not_prime : ¬(recordGapCenter - 269554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269554]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02262_not_prime : ¬(recordGapCenter - 269398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269398]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02263_not_prime : ¬(recordGapCenter - 269362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269362]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02264_not_prime : ¬(recordGapCenter - 269358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269358]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02265_not_prime : ¬(recordGapCenter - 269322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269322]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02266_not_prime : ¬(recordGapCenter - 269092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269092]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02267_not_prime : ¬(recordGapCenter - 269058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269058]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02268_not_prime : ¬(recordGapCenter - 269044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 269044]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02269_not_prime : ¬(recordGapCenter - 268678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268678]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02270_not_prime : ¬(recordGapCenter - 268638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268638]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02271_not_prime : ¬(recordGapCenter - 268564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268564]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02272_not_prime : ¬(recordGapCenter - 268098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268098]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02273_not_prime : ¬(recordGapCenter - 268084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268084]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02274_not_prime : ¬(recordGapCenter - 268012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 268012]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02275_not_prime : ¬(recordGapCenter - 267958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267958]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02276_not_prime : ¬(recordGapCenter - 267892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267892]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02277_not_prime : ¬(recordGapCenter - 267538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267538]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02278_not_prime : ¬(recordGapCenter - 267522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267522]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02279_not_prime : ¬(recordGapCenter - 267474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267474]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02280_not_prime : ¬(recordGapCenter - 267378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267378]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02281_not_prime : ¬(recordGapCenter - 267118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 267118]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02282_not_prime : ¬(recordGapCenter - 266998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266998]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02283_not_prime : ¬(recordGapCenter - 266902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266902]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02284_not_prime : ¬(recordGapCenter - 266878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266878]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02285_not_prime : ¬(recordGapCenter - 266782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266782]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02286_not_prime : ¬(recordGapCenter - 266758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266758]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02287_not_prime : ¬(recordGapCenter - 266698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266698]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02288_not_prime : ¬(recordGapCenter - 266404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266404]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02289_not_prime : ¬(recordGapCenter - 266338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266338]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02290_not_prime : ¬(recordGapCenter - 266298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266298]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02291_not_prime : ¬(recordGapCenter - 266242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266242]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02292_not_prime : ¬(recordGapCenter - 266112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 266112]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02293_not_prime : ¬(recordGapCenter - 265942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265942]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02294_not_prime : ¬(recordGapCenter - 265858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265858]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02295_not_prime : ¬(recordGapCenter - 265828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265828]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02296_not_prime : ¬(recordGapCenter - 265822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265822]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02297_not_prime : ¬(recordGapCenter - 265758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265758]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02298_not_prime : ¬(recordGapCenter - 265674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265674]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02299_not_prime : ¬(recordGapCenter - 265614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265614]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02300_not_prime : ¬(recordGapCenter - 265612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265612]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02301_not_prime : ¬(recordGapCenter - 265578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265578]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02302_not_prime : ¬(recordGapCenter - 265498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265498]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02303_not_prime : ¬(recordGapCenter - 265372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265372]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm02304_not_prime : ¬(recordGapCenter - 265348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 265348]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

end PrimeFactorUnimodality
