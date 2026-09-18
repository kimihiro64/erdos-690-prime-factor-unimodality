import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00130_values : List Nat :=
  [fullRecordGapCenterValue + 487790,
    fullRecordGapCenterValue + 487796,
    fullRecordGapCenterValue + 487842,
    fullRecordGapCenterValue + 487946,
    fullRecordGapCenterValue + 488090,
    fullRecordGapCenterValue + 488216,
    fullRecordGapCenterValue + 488276,
    fullRecordGapCenterValue + 488282,
    fullRecordGapCenterValue + 488318,
    fullRecordGapCenterValue + 488468,
    fullRecordGapCenterValue + 488526,
    fullRecordGapCenterValue + 488582,
    fullRecordGapCenterValue + 488666,
    fullRecordGapCenterValue + 488678,
    fullRecordGapCenterValue + 488702,
    fullRecordGapCenterValue + 488762,
    fullRecordGapCenterValue + 488786,
    fullRecordGapCenterValue + 488822,
    fullRecordGapCenterValue + 488828,
    fullRecordGapCenterValue + 488876,
    fullRecordGapCenterValue + 489092,
    fullRecordGapCenterValue + 489198,
    fullRecordGapCenterValue + 489282,
    fullRecordGapCenterValue + 489318,
    fullRecordGapCenterValue + 489378,
    fullRecordGapCenterValue + 489506,
    fullRecordGapCenterValue + 489548,
    fullRecordGapCenterValue + 489882,
    fullRecordGapCenterValue + 489890,
    fullRecordGapCenterValue + 490026,
    fullRecordGapCenterValue + 490058,
    fullRecordGapCenterValue + 490206,
    fullRecordGapCenterValue + 490316,
    fullRecordGapCenterValue + 490346,
    fullRecordGapCenterValue + 490362,
    fullRecordGapCenterValue + 490436,
    fullRecordGapCenterValue + 490502,
    fullRecordGapCenterValue + 490598,
    fullRecordGapCenterValue + 490638,
    fullRecordGapCenterValue + 490712,
    fullRecordGapCenterValue + 490766,
    fullRecordGapCenterValue + 490856,
    fullRecordGapCenterValue + 491012,
    fullRecordGapCenterValue + 491030,
    fullRecordGapCenterValue + 491090,
    fullRecordGapCenterValue + 491258,
    fullRecordGapCenterValue + 491298,
    fullRecordGapCenterValue + 491306,
    fullRecordGapCenterValue + 491396,
    fullRecordGapCenterValue + 491528,
    fullRecordGapCenterValue + 491570,
    fullRecordGapCenterValue + 491702,
    fullRecordGapCenterValue + 491726,
    fullRecordGapCenterValue + 491822,
    fullRecordGapCenterValue + 491838,
    fullRecordGapCenterValue + 491930,
    fullRecordGapCenterValue + 492068,
    fullRecordGapCenterValue + 492146,
    fullRecordGapCenterValue + 492186,
    fullRecordGapCenterValue + 492230,
    fullRecordGapCenterValue + 492266,
    fullRecordGapCenterValue + 492306,
    fullRecordGapCenterValue + 492308,
    fullRecordGapCenterValue + 492332]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00130_fermat : ∀ n ∈ fullRecordGapRow00130_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08257_not_prime : ¬(recordGapCenter + 487790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487790]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08258_not_prime : ¬(recordGapCenter + 487796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487796]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08259_not_prime : ¬(recordGapCenter + 487842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487842]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08260_not_prime : ¬(recordGapCenter + 487946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487946]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08261_not_prime : ¬(recordGapCenter + 488090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488090]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08262_not_prime : ¬(recordGapCenter + 488216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488216]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08263_not_prime : ¬(recordGapCenter + 488276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488276]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08264_not_prime : ¬(recordGapCenter + 488282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488282]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08265_not_prime : ¬(recordGapCenter + 488318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488318]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08266_not_prime : ¬(recordGapCenter + 488468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488468]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08267_not_prime : ¬(recordGapCenter + 488526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488526]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08268_not_prime : ¬(recordGapCenter + 488582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488582]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08269_not_prime : ¬(recordGapCenter + 488666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488666]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08270_not_prime : ¬(recordGapCenter + 488678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488678]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08271_not_prime : ¬(recordGapCenter + 488702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488702]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08272_not_prime : ¬(recordGapCenter + 488762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488762]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08273_not_prime : ¬(recordGapCenter + 488786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488786]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08274_not_prime : ¬(recordGapCenter + 488822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488822]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08275_not_prime : ¬(recordGapCenter + 488828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488828]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08276_not_prime : ¬(recordGapCenter + 488876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488876]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08277_not_prime : ¬(recordGapCenter + 489092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489092]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08278_not_prime : ¬(recordGapCenter + 489198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489198]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08279_not_prime : ¬(recordGapCenter + 489282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489282]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08280_not_prime : ¬(recordGapCenter + 489318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489318]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08281_not_prime : ¬(recordGapCenter + 489378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489378]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08282_not_prime : ¬(recordGapCenter + 489506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489506]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08283_not_prime : ¬(recordGapCenter + 489548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489548]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08284_not_prime : ¬(recordGapCenter + 489882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489882]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08285_not_prime : ¬(recordGapCenter + 489890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489890]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08286_not_prime : ¬(recordGapCenter + 490026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490026]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08287_not_prime : ¬(recordGapCenter + 490058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490058]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08288_not_prime : ¬(recordGapCenter + 490206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490206]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08289_not_prime : ¬(recordGapCenter + 490316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490316]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08290_not_prime : ¬(recordGapCenter + 490346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490346]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08291_not_prime : ¬(recordGapCenter + 490362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490362]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08292_not_prime : ¬(recordGapCenter + 490436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490436]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08293_not_prime : ¬(recordGapCenter + 490502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490502]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08294_not_prime : ¬(recordGapCenter + 490598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490598]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08295_not_prime : ¬(recordGapCenter + 490638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490638]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08296_not_prime : ¬(recordGapCenter + 490712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490712]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08297_not_prime : ¬(recordGapCenter + 490766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490766]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08298_not_prime : ¬(recordGapCenter + 490856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490856]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08299_not_prime : ¬(recordGapCenter + 491012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491012]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08300_not_prime : ¬(recordGapCenter + 491030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491030]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08301_not_prime : ¬(recordGapCenter + 491090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491090]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08302_not_prime : ¬(recordGapCenter + 491258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491258]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08303_not_prime : ¬(recordGapCenter + 491298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491298]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08304_not_prime : ¬(recordGapCenter + 491306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491306]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08305_not_prime : ¬(recordGapCenter + 491396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491396]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08306_not_prime : ¬(recordGapCenter + 491528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491528]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08307_not_prime : ¬(recordGapCenter + 491570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491570]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08308_not_prime : ¬(recordGapCenter + 491702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491702]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08309_not_prime : ¬(recordGapCenter + 491726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491726]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08310_not_prime : ¬(recordGapCenter + 491822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491822]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08311_not_prime : ¬(recordGapCenter + 491838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491838]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08312_not_prime : ¬(recordGapCenter + 491930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491930]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08313_not_prime : ¬(recordGapCenter + 492068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492068]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08314_not_prime : ¬(recordGapCenter + 492146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492146]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08315_not_prime : ¬(recordGapCenter + 492186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492186]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08316_not_prime : ¬(recordGapCenter + 492230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492230]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08317_not_prime : ¬(recordGapCenter + 492266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492266]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08318_not_prime : ¬(recordGapCenter + 492306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492306]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08319_not_prime : ¬(recordGapCenter + 492308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492308]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

theorem fullRecordGapTerm08320_not_prime : ¬(recordGapCenter + 492332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492332]
  · apply fullRecordGapRow00130_fermat
    simp [fullRecordGapRow00130_values]

end PrimeFactorUnimodality
