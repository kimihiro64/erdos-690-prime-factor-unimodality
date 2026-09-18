import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00023_values : List Nat :=
  [fullRecordGapCenterValue - 343762,
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
    fullRecordGapCenterValue - 338692]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00023_fermat : ∀ n ∈ fullRecordGapRow00023_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01409_not_prime : ¬(recordGapCenter - 343762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343762]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01410_not_prime : ¬(recordGapCenter - 343738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343738]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01411_not_prime : ¬(recordGapCenter - 343614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343614]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01412_not_prime : ¬(recordGapCenter - 343612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343612]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01413_not_prime : ¬(recordGapCenter - 343522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343522]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01414_not_prime : ¬(recordGapCenter - 343318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 343318]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01415_not_prime : ¬(recordGapCenter - 342898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342898]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01416_not_prime : ¬(recordGapCenter - 342682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342682]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01417_not_prime : ¬(recordGapCenter - 342634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342634]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01418_not_prime : ¬(recordGapCenter - 342534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342534]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01419_not_prime : ¬(recordGapCenter - 342508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342508]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01420_not_prime : ¬(recordGapCenter - 342502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342502]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01421_not_prime : ¬(recordGapCenter - 342484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342484]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01422_not_prime : ¬(recordGapCenter - 342438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342438]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01423_not_prime : ¬(recordGapCenter - 342388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342388]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01424_not_prime : ¬(recordGapCenter - 342124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342124]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01425_not_prime : ¬(recordGapCenter - 342094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342094]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01426_not_prime : ¬(recordGapCenter - 342052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 342052]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01427_not_prime : ¬(recordGapCenter - 341914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341914]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01428_not_prime : ¬(recordGapCenter - 341898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341898]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01429_not_prime : ¬(recordGapCenter - 341854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341854]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01430_not_prime : ¬(recordGapCenter - 341812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341812]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01431_not_prime : ¬(recordGapCenter - 341742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341742]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01432_not_prime : ¬(recordGapCenter - 341358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341358]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01433_not_prime : ¬(recordGapCenter - 341338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341338]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01434_not_prime : ¬(recordGapCenter - 341218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341218]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01435_not_prime : ¬(recordGapCenter - 341212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341212]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01436_not_prime : ¬(recordGapCenter - 341142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341142]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01437_not_prime : ¬(recordGapCenter - 341058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 341058]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01438_not_prime : ¬(recordGapCenter - 340972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340972]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01439_not_prime : ¬(recordGapCenter - 340962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340962]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01440_not_prime : ¬(recordGapCenter - 340878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340878]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01441_not_prime : ¬(recordGapCenter - 340854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340854]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01442_not_prime : ¬(recordGapCenter - 340702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340702]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01443_not_prime : ¬(recordGapCenter - 340638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340638]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01444_not_prime : ¬(recordGapCenter - 340534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340534]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01445_not_prime : ¬(recordGapCenter - 340422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340422]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01446_not_prime : ¬(recordGapCenter - 340378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340378]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01447_not_prime : ¬(recordGapCenter - 340372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340372]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01448_not_prime : ¬(recordGapCenter - 340324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340324]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01449_not_prime : ¬(recordGapCenter - 340282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340282]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01450_not_prime : ¬(recordGapCenter - 340108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340108]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01451_not_prime : ¬(recordGapCenter - 340084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340084]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01452_not_prime : ¬(recordGapCenter - 340042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 340042]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01453_not_prime : ¬(recordGapCenter - 339982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339982]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01454_not_prime : ¬(recordGapCenter - 339964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339964]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01455_not_prime : ¬(recordGapCenter - 339954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339954]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01456_not_prime : ¬(recordGapCenter - 339874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339874]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01457_not_prime : ¬(recordGapCenter - 339868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339868]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01458_not_prime : ¬(recordGapCenter - 339778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339778]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01459_not_prime : ¬(recordGapCenter - 339652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339652]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01460_not_prime : ¬(recordGapCenter - 339594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339594]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01461_not_prime : ¬(recordGapCenter - 339582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339582]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01462_not_prime : ¬(recordGapCenter - 339538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339538]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01463_not_prime : ¬(recordGapCenter - 339418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339418]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01464_not_prime : ¬(recordGapCenter - 339414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339414]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01465_not_prime : ¬(recordGapCenter - 339258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339258]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01466_not_prime : ¬(recordGapCenter - 339198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339198]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01467_not_prime : ¬(recordGapCenter - 339114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 339114]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01468_not_prime : ¬(recordGapCenter - 338862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338862]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01469_not_prime : ¬(recordGapCenter - 338818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338818]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01470_not_prime : ¬(recordGapCenter - 338788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338788]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01471_not_prime : ¬(recordGapCenter - 338722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338722]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

theorem fullRecordGapTerm01472_not_prime : ¬(recordGapCenter - 338692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338692]
  · apply fullRecordGapRow00023_fermat
    simp [fullRecordGapRow00023_values]

end PrimeFactorUnimodality
