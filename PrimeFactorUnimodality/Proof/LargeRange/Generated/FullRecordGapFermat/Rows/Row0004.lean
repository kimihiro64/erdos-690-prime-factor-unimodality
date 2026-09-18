import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00004_values : List Nat :=
  [fullRecordGapCenterValue - 439870,
    fullRecordGapCenterValue - 439864,
    fullRecordGapCenterValue - 439834,
    fullRecordGapCenterValue - 439690,
    fullRecordGapCenterValue - 439618,
    fullRecordGapCenterValue - 439554,
    fullRecordGapCenterValue - 439522,
    fullRecordGapCenterValue - 439422,
    fullRecordGapCenterValue - 439378,
    fullRecordGapCenterValue - 439372,
    fullRecordGapCenterValue - 439354,
    fullRecordGapCenterValue - 439324,
    fullRecordGapCenterValue - 438868,
    fullRecordGapCenterValue - 438808,
    fullRecordGapCenterValue - 438778,
    fullRecordGapCenterValue - 438762,
    fullRecordGapCenterValue - 438562,
    fullRecordGapCenterValue - 438388,
    fullRecordGapCenterValue - 438378,
    fullRecordGapCenterValue - 438258,
    fullRecordGapCenterValue - 438234,
    fullRecordGapCenterValue - 438184,
    fullRecordGapCenterValue - 438114,
    fullRecordGapCenterValue - 438078,
    fullRecordGapCenterValue - 437982,
    fullRecordGapCenterValue - 437812,
    fullRecordGapCenterValue - 437622,
    fullRecordGapCenterValue - 437590,
    fullRecordGapCenterValue - 437538,
    fullRecordGapCenterValue - 437530,
    fullRecordGapCenterValue - 437434,
    fullRecordGapCenterValue - 437422,
    fullRecordGapCenterValue - 437400,
    fullRecordGapCenterValue - 437358,
    fullRecordGapCenterValue - 437334,
    fullRecordGapCenterValue - 437314,
    fullRecordGapCenterValue - 437182,
    fullRecordGapCenterValue - 437170,
    fullRecordGapCenterValue - 437098,
    fullRecordGapCenterValue - 437068,
    fullRecordGapCenterValue - 436762,
    fullRecordGapCenterValue - 436684,
    fullRecordGapCenterValue - 436578,
    fullRecordGapCenterValue - 436510,
    fullRecordGapCenterValue - 436504,
    fullRecordGapCenterValue - 436498,
    fullRecordGapCenterValue - 436362,
    fullRecordGapCenterValue - 436312,
    fullRecordGapCenterValue - 436270,
    fullRecordGapCenterValue - 436252,
    fullRecordGapCenterValue - 436138,
    fullRecordGapCenterValue - 436134,
    fullRecordGapCenterValue - 436074,
    fullRecordGapCenterValue - 436042,
    fullRecordGapCenterValue - 435970,
    fullRecordGapCenterValue - 435964,
    fullRecordGapCenterValue - 435958,
    fullRecordGapCenterValue - 435894,
    fullRecordGapCenterValue - 435882,
    fullRecordGapCenterValue - 435874,
    fullRecordGapCenterValue - 435858,
    fullRecordGapCenterValue - 435844,
    fullRecordGapCenterValue - 435738,
    fullRecordGapCenterValue - 435718]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00004_fermat : ∀ n ∈ fullRecordGapRow00004_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00193_not_prime : ¬(recordGapCenter - 439870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439870]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00194_not_prime : ¬(recordGapCenter - 439864).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439864]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00195_not_prime : ¬(recordGapCenter - 439834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439834]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00196_not_prime : ¬(recordGapCenter - 439690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439690]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00197_not_prime : ¬(recordGapCenter - 439618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439618]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00198_not_prime : ¬(recordGapCenter - 439554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439554]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00199_not_prime : ¬(recordGapCenter - 439522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439522]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00200_not_prime : ¬(recordGapCenter - 439422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439422]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00201_not_prime : ¬(recordGapCenter - 439378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439378]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00202_not_prime : ¬(recordGapCenter - 439372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439372]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00203_not_prime : ¬(recordGapCenter - 439354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439354]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00204_not_prime : ¬(recordGapCenter - 439324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 439324]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00205_not_prime : ¬(recordGapCenter - 438868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438868]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00206_not_prime : ¬(recordGapCenter - 438808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438808]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00207_not_prime : ¬(recordGapCenter - 438778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438778]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00208_not_prime : ¬(recordGapCenter - 438762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438762]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00209_not_prime : ¬(recordGapCenter - 438562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438562]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00210_not_prime : ¬(recordGapCenter - 438388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438388]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00211_not_prime : ¬(recordGapCenter - 438378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438378]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00212_not_prime : ¬(recordGapCenter - 438258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438258]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00213_not_prime : ¬(recordGapCenter - 438234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438234]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00214_not_prime : ¬(recordGapCenter - 438184).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438184]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00215_not_prime : ¬(recordGapCenter - 438114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438114]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00216_not_prime : ¬(recordGapCenter - 438078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 438078]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00217_not_prime : ¬(recordGapCenter - 437982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437982]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00218_not_prime : ¬(recordGapCenter - 437812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437812]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00219_not_prime : ¬(recordGapCenter - 437622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437622]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00220_not_prime : ¬(recordGapCenter - 437590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437590]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00221_not_prime : ¬(recordGapCenter - 437538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437538]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00222_not_prime : ¬(recordGapCenter - 437530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437530]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00223_not_prime : ¬(recordGapCenter - 437434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437434]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00224_not_prime : ¬(recordGapCenter - 437422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437422]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00225_not_prime : ¬(recordGapCenter - 437400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437400]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00226_not_prime : ¬(recordGapCenter - 437358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437358]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00227_not_prime : ¬(recordGapCenter - 437334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437334]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00228_not_prime : ¬(recordGapCenter - 437314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437314]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00229_not_prime : ¬(recordGapCenter - 437182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437182]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00230_not_prime : ¬(recordGapCenter - 437170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437170]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00231_not_prime : ¬(recordGapCenter - 437098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437098]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00232_not_prime : ¬(recordGapCenter - 437068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 437068]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00233_not_prime : ¬(recordGapCenter - 436762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436762]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00234_not_prime : ¬(recordGapCenter - 436684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436684]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00235_not_prime : ¬(recordGapCenter - 436578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436578]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00236_not_prime : ¬(recordGapCenter - 436510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436510]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00237_not_prime : ¬(recordGapCenter - 436504).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436504]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00238_not_prime : ¬(recordGapCenter - 436498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436498]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00239_not_prime : ¬(recordGapCenter - 436362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436362]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00240_not_prime : ¬(recordGapCenter - 436312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436312]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00241_not_prime : ¬(recordGapCenter - 436270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436270]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00242_not_prime : ¬(recordGapCenter - 436252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436252]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00243_not_prime : ¬(recordGapCenter - 436138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436138]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00244_not_prime : ¬(recordGapCenter - 436134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436134]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00245_not_prime : ¬(recordGapCenter - 436074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436074]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00246_not_prime : ¬(recordGapCenter - 436042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 436042]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00247_not_prime : ¬(recordGapCenter - 435970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435970]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00248_not_prime : ¬(recordGapCenter - 435964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435964]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00249_not_prime : ¬(recordGapCenter - 435958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435958]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00250_not_prime : ¬(recordGapCenter - 435894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435894]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00251_not_prime : ¬(recordGapCenter - 435882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435882]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00252_not_prime : ¬(recordGapCenter - 435874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435874]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00253_not_prime : ¬(recordGapCenter - 435858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435858]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00254_not_prime : ¬(recordGapCenter - 435844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435844]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00255_not_prime : ¬(recordGapCenter - 435738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435738]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

theorem fullRecordGapTerm00256_not_prime : ¬(recordGapCenter - 435718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435718]
  · apply fullRecordGapRow00004_fermat
    simp [fullRecordGapRow00004_values]

end PrimeFactorUnimodality
