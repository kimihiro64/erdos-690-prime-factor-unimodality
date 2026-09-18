import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00122_values : List Nat :=
  [fullRecordGapCenterValue + 451166,
    fullRecordGapCenterValue + 451190,
    fullRecordGapCenterValue + 451208,
    fullRecordGapCenterValue + 451266,
    fullRecordGapCenterValue + 451448,
    fullRecordGapCenterValue + 451466,
    fullRecordGapCenterValue + 451538,
    fullRecordGapCenterValue + 451610,
    fullRecordGapCenterValue + 451658,
    fullRecordGapCenterValue + 451778,
    fullRecordGapCenterValue + 451838,
    fullRecordGapCenterValue + 451862,
    fullRecordGapCenterValue + 451868,
    fullRecordGapCenterValue + 451910,
    fullRecordGapCenterValue + 452198,
    fullRecordGapCenterValue + 452202,
    fullRecordGapCenterValue + 452246,
    fullRecordGapCenterValue + 452252,
    fullRecordGapCenterValue + 452258,
    fullRecordGapCenterValue + 452282,
    fullRecordGapCenterValue + 452330,
    fullRecordGapCenterValue + 452366,
    fullRecordGapCenterValue + 452418,
    fullRecordGapCenterValue + 452622,
    fullRecordGapCenterValue + 452630,
    fullRecordGapCenterValue + 452636,
    fullRecordGapCenterValue + 452760,
    fullRecordGapCenterValue + 452930,
    fullRecordGapCenterValue + 452966,
    fullRecordGapCenterValue + 453126,
    fullRecordGapCenterValue + 453318,
    fullRecordGapCenterValue + 453342,
    fullRecordGapCenterValue + 453426,
    fullRecordGapCenterValue + 453428,
    fullRecordGapCenterValue + 453462,
    fullRecordGapCenterValue + 453666,
    fullRecordGapCenterValue + 453686,
    fullRecordGapCenterValue + 453750,
    fullRecordGapCenterValue + 453770,
    fullRecordGapCenterValue + 453806,
    fullRecordGapCenterValue + 453846,
    fullRecordGapCenterValue + 453890,
    fullRecordGapCenterValue + 453918,
    fullRecordGapCenterValue + 454052,
    fullRecordGapCenterValue + 454136,
    fullRecordGapCenterValue + 454218,
    fullRecordGapCenterValue + 454232,
    fullRecordGapCenterValue + 454262,
    fullRecordGapCenterValue + 454382,
    fullRecordGapCenterValue + 454598,
    fullRecordGapCenterValue + 454616,
    fullRecordGapCenterValue + 454686,
    fullRecordGapCenterValue + 454742,
    fullRecordGapCenterValue + 454856,
    fullRecordGapCenterValue + 454892,
    fullRecordGapCenterValue + 454910,
    fullRecordGapCenterValue + 454998,
    fullRecordGapCenterValue + 455108,
    fullRecordGapCenterValue + 455162,
    fullRecordGapCenterValue + 455222,
    fullRecordGapCenterValue + 455372,
    fullRecordGapCenterValue + 455570,
    fullRecordGapCenterValue + 455586,
    fullRecordGapCenterValue + 455646]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00122_fermat : ∀ n ∈ fullRecordGapRow00122_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07745_not_prime : ¬(recordGapCenter + 451166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451166]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07746_not_prime : ¬(recordGapCenter + 451190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451190]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07747_not_prime : ¬(recordGapCenter + 451208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451208]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07748_not_prime : ¬(recordGapCenter + 451266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451266]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07749_not_prime : ¬(recordGapCenter + 451448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451448]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07750_not_prime : ¬(recordGapCenter + 451466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451466]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07751_not_prime : ¬(recordGapCenter + 451538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451538]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07752_not_prime : ¬(recordGapCenter + 451610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451610]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07753_not_prime : ¬(recordGapCenter + 451658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451658]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07754_not_prime : ¬(recordGapCenter + 451778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451778]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07755_not_prime : ¬(recordGapCenter + 451838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451838]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07756_not_prime : ¬(recordGapCenter + 451862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451862]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07757_not_prime : ¬(recordGapCenter + 451868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451868]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07758_not_prime : ¬(recordGapCenter + 451910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451910]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07759_not_prime : ¬(recordGapCenter + 452198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452198]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07760_not_prime : ¬(recordGapCenter + 452202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452202]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07761_not_prime : ¬(recordGapCenter + 452246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452246]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07762_not_prime : ¬(recordGapCenter + 452252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452252]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07763_not_prime : ¬(recordGapCenter + 452258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452258]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07764_not_prime : ¬(recordGapCenter + 452282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452282]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07765_not_prime : ¬(recordGapCenter + 452330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452330]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07766_not_prime : ¬(recordGapCenter + 452366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452366]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07767_not_prime : ¬(recordGapCenter + 452418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452418]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07768_not_prime : ¬(recordGapCenter + 452622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452622]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07769_not_prime : ¬(recordGapCenter + 452630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452630]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07770_not_prime : ¬(recordGapCenter + 452636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452636]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07771_not_prime : ¬(recordGapCenter + 452760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452760]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07772_not_prime : ¬(recordGapCenter + 452930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452930]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07773_not_prime : ¬(recordGapCenter + 452966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 452966]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07774_not_prime : ¬(recordGapCenter + 453126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453126]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07775_not_prime : ¬(recordGapCenter + 453318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453318]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07776_not_prime : ¬(recordGapCenter + 453342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453342]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07777_not_prime : ¬(recordGapCenter + 453426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453426]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07778_not_prime : ¬(recordGapCenter + 453428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453428]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07779_not_prime : ¬(recordGapCenter + 453462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453462]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07780_not_prime : ¬(recordGapCenter + 453666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453666]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07781_not_prime : ¬(recordGapCenter + 453686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453686]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07782_not_prime : ¬(recordGapCenter + 453750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453750]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07783_not_prime : ¬(recordGapCenter + 453770).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453770]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07784_not_prime : ¬(recordGapCenter + 453806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453806]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07785_not_prime : ¬(recordGapCenter + 453846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453846]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07786_not_prime : ¬(recordGapCenter + 453890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453890]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07787_not_prime : ¬(recordGapCenter + 453918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 453918]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07788_not_prime : ¬(recordGapCenter + 454052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454052]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07789_not_prime : ¬(recordGapCenter + 454136).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454136]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07790_not_prime : ¬(recordGapCenter + 454218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454218]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07791_not_prime : ¬(recordGapCenter + 454232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454232]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07792_not_prime : ¬(recordGapCenter + 454262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454262]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07793_not_prime : ¬(recordGapCenter + 454382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454382]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07794_not_prime : ¬(recordGapCenter + 454598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454598]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07795_not_prime : ¬(recordGapCenter + 454616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454616]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07796_not_prime : ¬(recordGapCenter + 454686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454686]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07797_not_prime : ¬(recordGapCenter + 454742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454742]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07798_not_prime : ¬(recordGapCenter + 454856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454856]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07799_not_prime : ¬(recordGapCenter + 454892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454892]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07800_not_prime : ¬(recordGapCenter + 454910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454910]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07801_not_prime : ¬(recordGapCenter + 454998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 454998]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07802_not_prime : ¬(recordGapCenter + 455108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455108]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07803_not_prime : ¬(recordGapCenter + 455162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455162]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07804_not_prime : ¬(recordGapCenter + 455222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455222]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07805_not_prime : ¬(recordGapCenter + 455372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455372]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07806_not_prime : ¬(recordGapCenter + 455570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455570]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07807_not_prime : ¬(recordGapCenter + 455586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455586]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

theorem fullRecordGapTerm07808_not_prime : ¬(recordGapCenter + 455646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455646]
  · apply fullRecordGapRow00122_fermat
    simp [fullRecordGapRow00122_values]

end PrimeFactorUnimodality
