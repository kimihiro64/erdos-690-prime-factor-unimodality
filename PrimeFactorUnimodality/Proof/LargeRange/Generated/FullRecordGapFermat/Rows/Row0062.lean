import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00062_values : List Nat :=
  [fullRecordGapCenterValue + 6480,
    fullRecordGapCenterValue + 6720,
    fullRecordGapCenterValue + 7056,
    fullRecordGapCenterValue + 7128,
    fullRecordGapCenterValue + 7290,
    fullRecordGapCenterValue + 7500,
    fullRecordGapCenterValue + 7560,
    fullRecordGapCenterValue + 7920,
    fullRecordGapCenterValue + 8192,
    fullRecordGapCenterValue + 8712,
    fullRecordGapCenterValue + 8748,
    fullRecordGapCenterValue + 8750,
    fullRecordGapCenterValue + 9000,
    fullRecordGapCenterValue + 9216,
    fullRecordGapCenterValue + 9240,
    fullRecordGapCenterValue + 9408,
    fullRecordGapCenterValue + 9600,
    fullRecordGapCenterValue + 9702,
    fullRecordGapCenterValue + 9900,
    fullRecordGapCenterValue + 10368,
    fullRecordGapCenterValue + 10692,
    fullRecordGapCenterValue + 10976,
    fullRecordGapCenterValue + 12000,
    fullRecordGapCenterValue + 12320,
    fullRecordGapCenterValue + 12348,
    fullRecordGapCenterValue + 12500,
    fullRecordGapCenterValue + 12600,
    fullRecordGapCenterValue + 13230,
    fullRecordGapCenterValue + 13310,
    fullRecordGapCenterValue + 13440,
    fullRecordGapCenterValue + 13860,
    fullRecordGapCenterValue + 14112,
    fullRecordGapCenterValue + 14336,
    fullRecordGapCenterValue + 14400,
    fullRecordGapCenterValue + 14850,
    fullRecordGapCenterValue + 15246,
    fullRecordGapCenterValue + 15750,
    fullRecordGapCenterValue + 16170,
    fullRecordGapCenterValue + 16200,
    fullRecordGapCenterValue + 16632,
    fullRecordGapCenterValue + 16800,
    fullRecordGapCenterValue + 16940,
    fullRecordGapCenterValue + 17150,
    fullRecordGapCenterValue + 17280,
    fullRecordGapCenterValue + 17496,
    fullRecordGapCenterValue + 17600,
    fullRecordGapCenterValue + 17820,
    fullRecordGapCenterValue + 18000,
    fullRecordGapCenterValue + 18480,
    fullRecordGapCenterValue + 18816,
    fullRecordGapCenterValue + 18900,
    fullRecordGapCenterValue + 19008,
    fullRecordGapCenterValue + 19440,
    fullRecordGapCenterValue + 19602,
    fullRecordGapCenterValue + 20480,
    fullRecordGapCenterValue + 20580,
    fullRecordGapCenterValue + 20736,
    fullRecordGapCenterValue + 21168,
    fullRecordGapCenterValue + 21560,
    fullRecordGapCenterValue + 21780,
    fullRecordGapCenterValue + 22176,
    fullRecordGapCenterValue + 22400,
    fullRecordGapCenterValue + 22500,
    fullRecordGapCenterValue + 22680]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00062_fermat : ∀ n ∈ fullRecordGapRow00062_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03905_not_prime : ¬(recordGapCenter + 6480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 6480]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03906_not_prime : ¬(recordGapCenter + 6720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 6720]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03907_not_prime : ¬(recordGapCenter + 7056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7056]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03908_not_prime : ¬(recordGapCenter + 7128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7128]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03909_not_prime : ¬(recordGapCenter + 7290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7290]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03910_not_prime : ¬(recordGapCenter + 7500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7500]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03911_not_prime : ¬(recordGapCenter + 7560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7560]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03912_not_prime : ¬(recordGapCenter + 7920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7920]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03913_not_prime : ¬(recordGapCenter + 8192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 8192]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03914_not_prime : ¬(recordGapCenter + 8712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 8712]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03915_not_prime : ¬(recordGapCenter + 8748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 8748]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03916_not_prime : ¬(recordGapCenter + 8750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 8750]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03917_not_prime : ¬(recordGapCenter + 9000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9000]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03918_not_prime : ¬(recordGapCenter + 9216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9216]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03919_not_prime : ¬(recordGapCenter + 9240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9240]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03920_not_prime : ¬(recordGapCenter + 9408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9408]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03921_not_prime : ¬(recordGapCenter + 9600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9600]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03922_not_prime : ¬(recordGapCenter + 9702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9702]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03923_not_prime : ¬(recordGapCenter + 9900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9900]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03924_not_prime : ¬(recordGapCenter + 10368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 10368]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03925_not_prime : ¬(recordGapCenter + 10692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 10692]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03926_not_prime : ¬(recordGapCenter + 10976).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 10976]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03927_not_prime : ¬(recordGapCenter + 12000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12000]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03928_not_prime : ¬(recordGapCenter + 12320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12320]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03929_not_prime : ¬(recordGapCenter + 12348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12348]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03930_not_prime : ¬(recordGapCenter + 12500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12500]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03931_not_prime : ¬(recordGapCenter + 12600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12600]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03932_not_prime : ¬(recordGapCenter + 13230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 13230]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03933_not_prime : ¬(recordGapCenter + 13310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 13310]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03934_not_prime : ¬(recordGapCenter + 13440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 13440]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03935_not_prime : ¬(recordGapCenter + 13860).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 13860]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03936_not_prime : ¬(recordGapCenter + 14112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 14112]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03937_not_prime : ¬(recordGapCenter + 14336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 14336]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03938_not_prime : ¬(recordGapCenter + 14400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 14400]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03939_not_prime : ¬(recordGapCenter + 14850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 14850]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03940_not_prime : ¬(recordGapCenter + 15246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 15246]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03941_not_prime : ¬(recordGapCenter + 15750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 15750]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03942_not_prime : ¬(recordGapCenter + 16170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16170]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03943_not_prime : ¬(recordGapCenter + 16200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16200]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03944_not_prime : ¬(recordGapCenter + 16632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16632]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03945_not_prime : ¬(recordGapCenter + 16800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16800]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03946_not_prime : ¬(recordGapCenter + 16940).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16940]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03947_not_prime : ¬(recordGapCenter + 17150).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17150]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03948_not_prime : ¬(recordGapCenter + 17280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17280]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03949_not_prime : ¬(recordGapCenter + 17496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17496]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03950_not_prime : ¬(recordGapCenter + 17600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17600]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03951_not_prime : ¬(recordGapCenter + 17820).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17820]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03952_not_prime : ¬(recordGapCenter + 18000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 18000]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03953_not_prime : ¬(recordGapCenter + 18480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 18480]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03954_not_prime : ¬(recordGapCenter + 18816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 18816]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03955_not_prime : ¬(recordGapCenter + 18900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 18900]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03956_not_prime : ¬(recordGapCenter + 19008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 19008]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03957_not_prime : ¬(recordGapCenter + 19440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 19440]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03958_not_prime : ¬(recordGapCenter + 19602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 19602]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03959_not_prime : ¬(recordGapCenter + 20480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 20480]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03960_not_prime : ¬(recordGapCenter + 20580).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 20580]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03961_not_prime : ¬(recordGapCenter + 20736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 20736]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03962_not_prime : ¬(recordGapCenter + 21168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 21168]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03963_not_prime : ¬(recordGapCenter + 21560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 21560]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03964_not_prime : ¬(recordGapCenter + 21780).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 21780]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03965_not_prime : ¬(recordGapCenter + 22176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 22176]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03966_not_prime : ¬(recordGapCenter + 22400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 22400]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03967_not_prime : ¬(recordGapCenter + 22500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 22500]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

theorem fullRecordGapTerm03968_not_prime : ¬(recordGapCenter + 22680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 22680]
  · apply fullRecordGapRow00062_fermat
    simp [fullRecordGapRow00062_values]

end PrimeFactorUnimodality
