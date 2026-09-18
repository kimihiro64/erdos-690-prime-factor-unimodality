import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00028_values : List Nat :=
  [fullRecordGapCenterValue - 316698,
    fullRecordGapCenterValue - 316614,
    fullRecordGapCenterValue - 316612,
    fullRecordGapCenterValue - 316542,
    fullRecordGapCenterValue - 316362,
    fullRecordGapCenterValue - 316258,
    fullRecordGapCenterValue - 316252,
    fullRecordGapCenterValue - 316182,
    fullRecordGapCenterValue - 316038,
    fullRecordGapCenterValue - 315982,
    fullRecordGapCenterValue - 315762,
    fullRecordGapCenterValue - 315654,
    fullRecordGapCenterValue - 315598,
    fullRecordGapCenterValue - 315508,
    fullRecordGapCenterValue - 315474,
    fullRecordGapCenterValue - 315292,
    fullRecordGapCenterValue - 315174,
    fullRecordGapCenterValue - 315142,
    fullRecordGapCenterValue - 314914,
    fullRecordGapCenterValue - 314788,
    fullRecordGapCenterValue - 314718,
    fullRecordGapCenterValue - 314614,
    fullRecordGapCenterValue - 314554,
    fullRecordGapCenterValue - 314332,
    fullRecordGapCenterValue - 314284,
    fullRecordGapCenterValue - 314178,
    fullRecordGapCenterValue - 314068,
    fullRecordGapCenterValue - 314044,
    fullRecordGapCenterValue - 314038,
    fullRecordGapCenterValue - 313942,
    fullRecordGapCenterValue - 313798,
    fullRecordGapCenterValue - 313774,
    fullRecordGapCenterValue - 313602,
    fullRecordGapCenterValue - 313600,
    fullRecordGapCenterValue - 313422,
    fullRecordGapCenterValue - 313414,
    fullRecordGapCenterValue - 313338,
    fullRecordGapCenterValue - 313134,
    fullRecordGapCenterValue - 313078,
    fullRecordGapCenterValue - 312982,
    fullRecordGapCenterValue - 312934,
    fullRecordGapCenterValue - 312882,
    fullRecordGapCenterValue - 312874,
    fullRecordGapCenterValue - 312772,
    fullRecordGapCenterValue - 312484,
    fullRecordGapCenterValue - 312414,
    fullRecordGapCenterValue - 312342,
    fullRecordGapCenterValue - 312262,
    fullRecordGapCenterValue - 312142,
    fullRecordGapCenterValue - 312028,
    fullRecordGapCenterValue - 311908,
    fullRecordGapCenterValue - 311862,
    fullRecordGapCenterValue - 311850,
    fullRecordGapCenterValue - 311782,
    fullRecordGapCenterValue - 311602,
    fullRecordGapCenterValue - 311554,
    fullRecordGapCenterValue - 311478,
    fullRecordGapCenterValue - 311442,
    fullRecordGapCenterValue - 311434,
    fullRecordGapCenterValue - 311394,
    fullRecordGapCenterValue - 311218,
    fullRecordGapCenterValue - 311118,
    fullRecordGapCenterValue - 311034,
    fullRecordGapCenterValue - 310852]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00028_fermat : ∀ n ∈ fullRecordGapRow00028_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01729_not_prime : ¬(recordGapCenter - 316698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316698]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01730_not_prime : ¬(recordGapCenter - 316614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316614]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01731_not_prime : ¬(recordGapCenter - 316612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316612]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01732_not_prime : ¬(recordGapCenter - 316542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316542]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01733_not_prime : ¬(recordGapCenter - 316362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316362]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01734_not_prime : ¬(recordGapCenter - 316258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316258]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01735_not_prime : ¬(recordGapCenter - 316252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316252]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01736_not_prime : ¬(recordGapCenter - 316182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316182]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01737_not_prime : ¬(recordGapCenter - 316038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316038]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01738_not_prime : ¬(recordGapCenter - 315982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315982]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01739_not_prime : ¬(recordGapCenter - 315762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315762]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01740_not_prime : ¬(recordGapCenter - 315654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315654]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01741_not_prime : ¬(recordGapCenter - 315598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315598]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01742_not_prime : ¬(recordGapCenter - 315508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315508]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01743_not_prime : ¬(recordGapCenter - 315474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315474]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01744_not_prime : ¬(recordGapCenter - 315292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315292]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01745_not_prime : ¬(recordGapCenter - 315174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315174]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01746_not_prime : ¬(recordGapCenter - 315142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 315142]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01747_not_prime : ¬(recordGapCenter - 314914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314914]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01748_not_prime : ¬(recordGapCenter - 314788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314788]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01749_not_prime : ¬(recordGapCenter - 314718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314718]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01750_not_prime : ¬(recordGapCenter - 314614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314614]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01751_not_prime : ¬(recordGapCenter - 314554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314554]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01752_not_prime : ¬(recordGapCenter - 314332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314332]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01753_not_prime : ¬(recordGapCenter - 314284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314284]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01754_not_prime : ¬(recordGapCenter - 314178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314178]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01755_not_prime : ¬(recordGapCenter - 314068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314068]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01756_not_prime : ¬(recordGapCenter - 314044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314044]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01757_not_prime : ¬(recordGapCenter - 314038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 314038]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01758_not_prime : ¬(recordGapCenter - 313942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313942]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01759_not_prime : ¬(recordGapCenter - 313798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313798]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01760_not_prime : ¬(recordGapCenter - 313774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313774]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01761_not_prime : ¬(recordGapCenter - 313602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313602]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01762_not_prime : ¬(recordGapCenter - 313600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313600]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01763_not_prime : ¬(recordGapCenter - 313422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313422]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01764_not_prime : ¬(recordGapCenter - 313414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313414]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01765_not_prime : ¬(recordGapCenter - 313338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313338]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01766_not_prime : ¬(recordGapCenter - 313134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313134]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01767_not_prime : ¬(recordGapCenter - 313078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 313078]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01768_not_prime : ¬(recordGapCenter - 312982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312982]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01769_not_prime : ¬(recordGapCenter - 312934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312934]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01770_not_prime : ¬(recordGapCenter - 312882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312882]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01771_not_prime : ¬(recordGapCenter - 312874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312874]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01772_not_prime : ¬(recordGapCenter - 312772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312772]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01773_not_prime : ¬(recordGapCenter - 312484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312484]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01774_not_prime : ¬(recordGapCenter - 312414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312414]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01775_not_prime : ¬(recordGapCenter - 312342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312342]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01776_not_prime : ¬(recordGapCenter - 312262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312262]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01777_not_prime : ¬(recordGapCenter - 312142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312142]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01778_not_prime : ¬(recordGapCenter - 312028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 312028]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01779_not_prime : ¬(recordGapCenter - 311908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311908]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01780_not_prime : ¬(recordGapCenter - 311862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311862]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01781_not_prime : ¬(recordGapCenter - 311850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311850]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01782_not_prime : ¬(recordGapCenter - 311782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311782]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01783_not_prime : ¬(recordGapCenter - 311602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311602]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01784_not_prime : ¬(recordGapCenter - 311554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311554]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01785_not_prime : ¬(recordGapCenter - 311478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311478]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01786_not_prime : ¬(recordGapCenter - 311442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311442]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01787_not_prime : ¬(recordGapCenter - 311434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311434]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01788_not_prime : ¬(recordGapCenter - 311394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311394]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01789_not_prime : ¬(recordGapCenter - 311218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311218]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01790_not_prime : ¬(recordGapCenter - 311118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311118]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01791_not_prime : ¬(recordGapCenter - 311034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 311034]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm01792_not_prime : ¬(recordGapCenter - 310852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310852]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

end PrimeFactorUnimodality
