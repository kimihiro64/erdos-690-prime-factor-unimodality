import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00017_values : List Nat :=
  [fullRecordGapCenterValue - 374434,
    fullRecordGapCenterValue - 374278,
    fullRecordGapCenterValue - 374254,
    fullRecordGapCenterValue - 374182,
    fullRecordGapCenterValue - 374098,
    fullRecordGapCenterValue - 373972,
    fullRecordGapCenterValue - 373852,
    fullRecordGapCenterValue - 373818,
    fullRecordGapCenterValue - 373782,
    fullRecordGapCenterValue - 373624,
    fullRecordGapCenterValue - 373522,
    fullRecordGapCenterValue - 373398,
    fullRecordGapCenterValue - 373294,
    fullRecordGapCenterValue - 373162,
    fullRecordGapCenterValue - 373134,
    fullRecordGapCenterValue - 373012,
    fullRecordGapCenterValue - 372958,
    fullRecordGapCenterValue - 372874,
    fullRecordGapCenterValue - 372858,
    fullRecordGapCenterValue - 372754,
    fullRecordGapCenterValue - 372748,
    fullRecordGapCenterValue - 372634,
    fullRecordGapCenterValue - 372622,
    fullRecordGapCenterValue - 372594,
    fullRecordGapCenterValue - 372454,
    fullRecordGapCenterValue - 372342,
    fullRecordGapCenterValue - 372322,
    fullRecordGapCenterValue - 372238,
    fullRecordGapCenterValue - 372234,
    fullRecordGapCenterValue - 372102,
    fullRecordGapCenterValue - 372018,
    fullRecordGapCenterValue - 372004,
    fullRecordGapCenterValue - 371922,
    fullRecordGapCenterValue - 371662,
    fullRecordGapCenterValue - 371608,
    fullRecordGapCenterValue - 371578,
    fullRecordGapCenterValue - 371494,
    fullRecordGapCenterValue - 371250,
    fullRecordGapCenterValue - 371242,
    fullRecordGapCenterValue - 371062,
    fullRecordGapCenterValue - 371058,
    fullRecordGapCenterValue - 370914,
    fullRecordGapCenterValue - 370654,
    fullRecordGapCenterValue - 370618,
    fullRecordGapCenterValue - 370564,
    fullRecordGapCenterValue - 370542,
    fullRecordGapCenterValue - 370534,
    fullRecordGapCenterValue - 370492,
    fullRecordGapCenterValue - 370354,
    fullRecordGapCenterValue - 370218,
    fullRecordGapCenterValue - 370114,
    fullRecordGapCenterValue - 370102,
    fullRecordGapCenterValue - 370054,
    fullRecordGapCenterValue - 370012,
    fullRecordGapCenterValue - 369994,
    fullRecordGapCenterValue - 369654,
    fullRecordGapCenterValue - 369618,
    fullRecordGapCenterValue - 369600,
    fullRecordGapCenterValue - 369532,
    fullRecordGapCenterValue - 369508,
    fullRecordGapCenterValue - 369498,
    fullRecordGapCenterValue - 369388,
    fullRecordGapCenterValue - 369268,
    fullRecordGapCenterValue - 369214]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00017_fermat : ∀ n ∈ fullRecordGapRow00017_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01025_not_prime : ¬(recordGapCenter - 374434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374434]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01026_not_prime : ¬(recordGapCenter - 374278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374278]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01027_not_prime : ¬(recordGapCenter - 374254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374254]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01028_not_prime : ¬(recordGapCenter - 374182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374182]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01029_not_prime : ¬(recordGapCenter - 374098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374098]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01030_not_prime : ¬(recordGapCenter - 373972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373972]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01031_not_prime : ¬(recordGapCenter - 373852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373852]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01032_not_prime : ¬(recordGapCenter - 373818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373818]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01033_not_prime : ¬(recordGapCenter - 373782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373782]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01034_not_prime : ¬(recordGapCenter - 373624).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373624]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01035_not_prime : ¬(recordGapCenter - 373522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373522]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01036_not_prime : ¬(recordGapCenter - 373398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373398]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01037_not_prime : ¬(recordGapCenter - 373294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373294]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01038_not_prime : ¬(recordGapCenter - 373162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373162]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01039_not_prime : ¬(recordGapCenter - 373134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373134]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01040_not_prime : ¬(recordGapCenter - 373012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373012]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01041_not_prime : ¬(recordGapCenter - 372958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372958]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01042_not_prime : ¬(recordGapCenter - 372874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372874]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01043_not_prime : ¬(recordGapCenter - 372858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372858]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01044_not_prime : ¬(recordGapCenter - 372754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372754]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01045_not_prime : ¬(recordGapCenter - 372748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372748]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01046_not_prime : ¬(recordGapCenter - 372634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372634]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01047_not_prime : ¬(recordGapCenter - 372622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372622]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01048_not_prime : ¬(recordGapCenter - 372594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372594]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01049_not_prime : ¬(recordGapCenter - 372454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372454]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01050_not_prime : ¬(recordGapCenter - 372342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372342]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01051_not_prime : ¬(recordGapCenter - 372322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372322]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01052_not_prime : ¬(recordGapCenter - 372238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372238]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01053_not_prime : ¬(recordGapCenter - 372234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372234]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01054_not_prime : ¬(recordGapCenter - 372102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372102]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01055_not_prime : ¬(recordGapCenter - 372018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372018]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01056_not_prime : ¬(recordGapCenter - 372004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372004]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01057_not_prime : ¬(recordGapCenter - 371922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371922]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01058_not_prime : ¬(recordGapCenter - 371662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371662]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01059_not_prime : ¬(recordGapCenter - 371608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371608]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01060_not_prime : ¬(recordGapCenter - 371578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371578]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01061_not_prime : ¬(recordGapCenter - 371494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371494]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01062_not_prime : ¬(recordGapCenter - 371250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371250]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01063_not_prime : ¬(recordGapCenter - 371242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371242]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01064_not_prime : ¬(recordGapCenter - 371062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371062]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01065_not_prime : ¬(recordGapCenter - 371058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371058]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01066_not_prime : ¬(recordGapCenter - 370914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370914]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01067_not_prime : ¬(recordGapCenter - 370654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370654]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01068_not_prime : ¬(recordGapCenter - 370618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370618]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01069_not_prime : ¬(recordGapCenter - 370564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370564]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01070_not_prime : ¬(recordGapCenter - 370542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370542]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01071_not_prime : ¬(recordGapCenter - 370534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370534]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01072_not_prime : ¬(recordGapCenter - 370492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370492]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01073_not_prime : ¬(recordGapCenter - 370354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370354]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01074_not_prime : ¬(recordGapCenter - 370218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370218]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01075_not_prime : ¬(recordGapCenter - 370114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370114]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01076_not_prime : ¬(recordGapCenter - 370102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370102]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01077_not_prime : ¬(recordGapCenter - 370054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370054]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01078_not_prime : ¬(recordGapCenter - 370012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370012]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01079_not_prime : ¬(recordGapCenter - 369994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369994]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01080_not_prime : ¬(recordGapCenter - 369654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369654]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01081_not_prime : ¬(recordGapCenter - 369618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369618]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01082_not_prime : ¬(recordGapCenter - 369600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369600]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01083_not_prime : ¬(recordGapCenter - 369532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369532]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01084_not_prime : ¬(recordGapCenter - 369508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369508]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01085_not_prime : ¬(recordGapCenter - 369498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369498]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01086_not_prime : ¬(recordGapCenter - 369388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369388]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01087_not_prime : ¬(recordGapCenter - 369268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369268]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm01088_not_prime : ¬(recordGapCenter - 369214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369214]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

end PrimeFactorUnimodality
