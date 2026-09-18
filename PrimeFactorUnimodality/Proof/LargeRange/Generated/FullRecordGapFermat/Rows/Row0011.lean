import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00011_values : List Nat :=
  [fullRecordGapCenterValue - 404644,
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
    fullRecordGapCenterValue - 400098]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00011_fermat : ∀ n ∈ fullRecordGapRow00011_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00641_not_prime : ¬(recordGapCenter - 404644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404644]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00642_not_prime : ¬(recordGapCenter - 404598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404598]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00643_not_prime : ¬(recordGapCenter - 404578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404578]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00644_not_prime : ¬(recordGapCenter - 404428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404428]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00645_not_prime : ¬(recordGapCenter - 404394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404394]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00646_not_prime : ¬(recordGapCenter - 404344).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404344]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00647_not_prime : ¬(recordGapCenter - 404242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404242]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00648_not_prime : ¬(recordGapCenter - 404134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404134]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00649_not_prime : ¬(recordGapCenter - 404058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404058]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00650_not_prime : ¬(recordGapCenter - 403948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403948]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00651_not_prime : ¬(recordGapCenter - 403842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403842]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00652_not_prime : ¬(recordGapCenter - 403828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403828]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00653_not_prime : ¬(recordGapCenter - 403822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403822]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00654_not_prime : ¬(recordGapCenter - 403654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403654]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00655_not_prime : ¬(recordGapCenter - 403582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403582]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00656_not_prime : ¬(recordGapCenter - 403534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403534]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00657_not_prime : ¬(recordGapCenter - 403288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403288]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00658_not_prime : ¬(recordGapCenter - 403204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403204]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00659_not_prime : ¬(recordGapCenter - 403200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403200]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00660_not_prime : ¬(recordGapCenter - 403122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403122]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00661_not_prime : ¬(recordGapCenter - 403114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 403114]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00662_not_prime : ¬(recordGapCenter - 402988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402988]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00663_not_prime : ¬(recordGapCenter - 402964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402964]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00664_not_prime : ¬(recordGapCenter - 402898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402898]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00665_not_prime : ¬(recordGapCenter - 402874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402874]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00666_not_prime : ¬(recordGapCenter - 402834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402834]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00667_not_prime : ¬(recordGapCenter - 402618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402618]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00668_not_prime : ¬(recordGapCenter - 402562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402562]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00669_not_prime : ¬(recordGapCenter - 402502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402502]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00670_not_prime : ¬(recordGapCenter - 402484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402484]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00671_not_prime : ¬(recordGapCenter - 402474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402474]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00672_not_prime : ¬(recordGapCenter - 402418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402418]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00673_not_prime : ¬(recordGapCenter - 402342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402342]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00674_not_prime : ¬(recordGapCenter - 402202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 402202]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00675_not_prime : ¬(recordGapCenter - 401848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401848]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00676_not_prime : ¬(recordGapCenter - 401818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401818]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00677_not_prime : ¬(recordGapCenter - 401788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401788]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00678_not_prime : ¬(recordGapCenter - 401754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401754]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00679_not_prime : ¬(recordGapCenter - 401734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401734]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00680_not_prime : ¬(recordGapCenter - 401722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401722]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00681_not_prime : ¬(recordGapCenter - 401644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401644]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00682_not_prime : ¬(recordGapCenter - 401572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401572]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00683_not_prime : ¬(recordGapCenter - 401334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401334]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00684_not_prime : ¬(recordGapCenter - 401278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401278]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00685_not_prime : ¬(recordGapCenter - 401272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401272]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00686_not_prime : ¬(recordGapCenter - 401188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401188]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00687_not_prime : ¬(recordGapCenter - 401182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401182]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00688_not_prime : ¬(recordGapCenter - 401118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401118]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00689_not_prime : ¬(recordGapCenter - 401068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401068]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00690_not_prime : ¬(recordGapCenter - 401032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 401032]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00691_not_prime : ¬(recordGapCenter - 400984).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400984]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00692_not_prime : ¬(recordGapCenter - 400948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400948]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00693_not_prime : ¬(recordGapCenter - 400854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400854]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00694_not_prime : ¬(recordGapCenter - 400782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400782]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00695_not_prime : ¬(recordGapCenter - 400762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400762]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00696_not_prime : ¬(recordGapCenter - 400732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400732]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00697_not_prime : ¬(recordGapCenter - 400714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400714]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00698_not_prime : ¬(recordGapCenter - 400612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400612]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00699_not_prime : ¬(recordGapCenter - 400354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400354]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00700_not_prime : ¬(recordGapCenter - 400342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400342]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00701_not_prime : ¬(recordGapCenter - 400318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400318]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00702_not_prime : ¬(recordGapCenter - 400234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400234]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00703_not_prime : ¬(recordGapCenter - 400182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400182]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm00704_not_prime : ¬(recordGapCenter - 400098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400098]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

end PrimeFactorUnimodality
