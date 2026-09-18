import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00165_values : List Nat :=
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
    fullRecordGapCenterValue + 637322]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00165_fermat : ∀ n ∈ fullRecordGapRow00165_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10497_not_prime : ¬(recordGapCenter + 633638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633638]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10498_not_prime : ¬(recordGapCenter + 633756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633756]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10499_not_prime : ¬(recordGapCenter + 633848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633848]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10500_not_prime : ¬(recordGapCenter + 634076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634076]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10501_not_prime : ¬(recordGapCenter + 634232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634232]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10502_not_prime : ¬(recordGapCenter + 634268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634268]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10503_not_prime : ¬(recordGapCenter + 634298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634298]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10504_not_prime : ¬(recordGapCenter + 634308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634308]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10505_not_prime : ¬(recordGapCenter + 634398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634398]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10506_not_prime : ¬(recordGapCenter + 634548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634548]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10507_not_prime : ¬(recordGapCenter + 634596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634596]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10508_not_prime : ¬(recordGapCenter + 634646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634646]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10509_not_prime : ¬(recordGapCenter + 634706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634706]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10510_not_prime : ¬(recordGapCenter + 634730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634730]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10511_not_prime : ¬(recordGapCenter + 634742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634742]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10512_not_prime : ¬(recordGapCenter + 634802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634802]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10513_not_prime : ¬(recordGapCenter + 634812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634812]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10514_not_prime : ¬(recordGapCenter + 634902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 634902]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10515_not_prime : ¬(recordGapCenter + 635040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635040]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10516_not_prime : ¬(recordGapCenter + 635078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635078]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10517_not_prime : ¬(recordGapCenter + 635108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635108]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10518_not_prime : ¬(recordGapCenter + 635178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635178]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10519_not_prime : ¬(recordGapCenter + 635192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635192]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10520_not_prime : ¬(recordGapCenter + 635198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635198]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10521_not_prime : ¬(recordGapCenter + 635372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635372]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10522_not_prime : ¬(recordGapCenter + 635402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635402]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10523_not_prime : ¬(recordGapCenter + 635468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635468]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10524_not_prime : ¬(recordGapCenter + 635556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635556]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10525_not_prime : ¬(recordGapCenter + 635636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635636]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10526_not_prime : ¬(recordGapCenter + 635678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635678]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10527_not_prime : ¬(recordGapCenter + 635772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635772]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10528_not_prime : ¬(recordGapCenter + 635870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635870]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10529_not_prime : ¬(recordGapCenter + 635898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635898]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10530_not_prime : ¬(recordGapCenter + 635918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635918]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10531_not_prime : ¬(recordGapCenter + 635978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635978]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10532_not_prime : ¬(recordGapCenter + 635982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635982]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10533_not_prime : ¬(recordGapCenter + 635988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 635988]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10534_not_prime : ¬(recordGapCenter + 636002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636002]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10535_not_prime : ¬(recordGapCenter + 636062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636062]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10536_not_prime : ¬(recordGapCenter + 636078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636078]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10537_not_prime : ¬(recordGapCenter + 636146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636146]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10538_not_prime : ¬(recordGapCenter + 636186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636186]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10539_not_prime : ¬(recordGapCenter + 636248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636248]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10540_not_prime : ¬(recordGapCenter + 636392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636392]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10541_not_prime : ¬(recordGapCenter + 636422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636422]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10542_not_prime : ¬(recordGapCenter + 636458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636458]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10543_not_prime : ¬(recordGapCenter + 636476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636476]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10544_not_prime : ¬(recordGapCenter + 636578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636578]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10545_not_prime : ¬(recordGapCenter + 636612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636612]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10546_not_prime : ¬(recordGapCenter + 636668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636668]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10547_not_prime : ¬(recordGapCenter + 636710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636710]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10548_not_prime : ¬(recordGapCenter + 636806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636806]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10549_not_prime : ¬(recordGapCenter + 636836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636836]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10550_not_prime : ¬(recordGapCenter + 636932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 636932]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10551_not_prime : ¬(recordGapCenter + 637016).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637016]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10552_not_prime : ¬(recordGapCenter + 637068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637068]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10553_not_prime : ¬(recordGapCenter + 637122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637122]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10554_not_prime : ¬(recordGapCenter + 637148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637148]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10555_not_prime : ¬(recordGapCenter + 637172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637172]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10556_not_prime : ¬(recordGapCenter + 637178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637178]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10557_not_prime : ¬(recordGapCenter + 637256).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637256]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10558_not_prime : ¬(recordGapCenter + 637278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637278]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10559_not_prime : ¬(recordGapCenter + 637302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637302]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

theorem fullRecordGapTerm10560_not_prime : ¬(recordGapCenter + 637322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637322]
  · apply fullRecordGapRow00165_fermat
    simp [fullRecordGapRow00165_values]

end PrimeFactorUnimodality
