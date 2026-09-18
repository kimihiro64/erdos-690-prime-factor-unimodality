import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00016_values : List Nat :=
  [fullRecordGapCenterValue - 379972,
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
theorem fullRecordGapRow00016_fermat : ∀ n ∈ fullRecordGapRow00016_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00961_not_prime : ¬(recordGapCenter - 379972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379972]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00962_not_prime : ¬(recordGapCenter - 379902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379902]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00963_not_prime : ¬(recordGapCenter - 379804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379804]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00964_not_prime : ¬(recordGapCenter - 379774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379774]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00965_not_prime : ¬(recordGapCenter - 379672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379672]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00966_not_prime : ¬(recordGapCenter - 379594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379594]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00967_not_prime : ¬(recordGapCenter - 379528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379528]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00968_not_prime : ¬(recordGapCenter - 379402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379402]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00969_not_prime : ¬(recordGapCenter - 379348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379348]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00970_not_prime : ¬(recordGapCenter - 379342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379342]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00971_not_prime : ¬(recordGapCenter - 379234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379234]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00972_not_prime : ¬(recordGapCenter - 379194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379194]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00973_not_prime : ¬(recordGapCenter - 379074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379074]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00974_not_prime : ¬(recordGapCenter - 379048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379048]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00975_not_prime : ¬(recordGapCenter - 378958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378958]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00976_not_prime : ¬(recordGapCenter - 378894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378894]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00977_not_prime : ¬(recordGapCenter - 378892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378892]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00978_not_prime : ¬(recordGapCenter - 378874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378874]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00979_not_prime : ¬(recordGapCenter - 378748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378748]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00980_not_prime : ¬(recordGapCenter - 378622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378622]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00981_not_prime : ¬(recordGapCenter - 378618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378618]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00982_not_prime : ¬(recordGapCenter - 378604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378604]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00983_not_prime : ¬(recordGapCenter - 378412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378412]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00984_not_prime : ¬(recordGapCenter - 378172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378172]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00985_not_prime : ¬(recordGapCenter - 378124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378124]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00986_not_prime : ¬(recordGapCenter - 378034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 378034]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00987_not_prime : ¬(recordGapCenter - 377998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377998]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00988_not_prime : ¬(recordGapCenter - 377934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377934]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00989_not_prime : ¬(recordGapCenter - 377932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377932]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00990_not_prime : ¬(recordGapCenter - 377908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377908]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00991_not_prime : ¬(recordGapCenter - 377878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377878]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00992_not_prime : ¬(recordGapCenter - 377512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377512]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00993_not_prime : ¬(recordGapCenter - 377382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377382]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00994_not_prime : ¬(recordGapCenter - 377362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377362]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00995_not_prime : ¬(recordGapCenter - 377218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377218]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00996_not_prime : ¬(recordGapCenter - 377032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 377032]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00997_not_prime : ¬(recordGapCenter - 376962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376962]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00998_not_prime : ¬(recordGapCenter - 376834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376834]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm00999_not_prime : ¬(recordGapCenter - 376738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376738]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01000_not_prime : ¬(recordGapCenter - 376702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376702]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01001_not_prime : ¬(recordGapCenter - 376638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376638]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01002_not_prime : ¬(recordGapCenter - 376582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376582]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01003_not_prime : ¬(recordGapCenter - 376518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376518]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01004_not_prime : ¬(recordGapCenter - 376294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376294]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01005_not_prime : ¬(recordGapCenter - 376122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 376122]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01006_not_prime : ¬(recordGapCenter - 375868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375868]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01007_not_prime : ¬(recordGapCenter - 375798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375798]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01008_not_prime : ¬(recordGapCenter - 375748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375748]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01009_not_prime : ¬(recordGapCenter - 375652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375652]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01010_not_prime : ¬(recordGapCenter - 375618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375618]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01011_not_prime : ¬(recordGapCenter - 375604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375604]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01012_not_prime : ¬(recordGapCenter - 375442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375442]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01013_not_prime : ¬(recordGapCenter - 375378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375378]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01014_not_prime : ¬(recordGapCenter - 375294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375294]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01015_not_prime : ¬(recordGapCenter - 375262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375262]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01016_not_prime : ¬(recordGapCenter - 375244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375244]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01017_not_prime : ¬(recordGapCenter - 375118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375118]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01018_not_prime : ¬(recordGapCenter - 375094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375094]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01019_not_prime : ¬(recordGapCenter - 375000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 375000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01020_not_prime : ¬(recordGapCenter - 374982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374982]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01021_not_prime : ¬(recordGapCenter - 374898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374898]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01022_not_prime : ¬(recordGapCenter - 374674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374674]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01023_not_prime : ¬(recordGapCenter - 374548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374548]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm01024_not_prime : ¬(recordGapCenter - 374502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374502]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

end PrimeFactorUnimodality
