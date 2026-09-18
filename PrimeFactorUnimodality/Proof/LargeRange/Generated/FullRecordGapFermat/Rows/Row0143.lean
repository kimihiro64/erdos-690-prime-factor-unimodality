import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00143_values : List Nat :=
  [fullRecordGapCenterValue + 543908,
    fullRecordGapCenterValue + 544058,
    fullRecordGapCenterValue + 544062,
    fullRecordGapCenterValue + 544182,
    fullRecordGapCenterValue + 544190,
    fullRecordGapCenterValue + 544332,
    fullRecordGapCenterValue + 544472,
    fullRecordGapCenterValue + 544490,
    fullRecordGapCenterValue + 544500,
    fullRecordGapCenterValue + 544526,
    fullRecordGapCenterValue + 544532,
    fullRecordGapCenterValue + 544568,
    fullRecordGapCenterValue + 544598,
    fullRecordGapCenterValue + 544652,
    fullRecordGapCenterValue + 544682,
    fullRecordGapCenterValue + 544722,
    fullRecordGapCenterValue + 544758,
    fullRecordGapCenterValue + 544766,
    fullRecordGapCenterValue + 544772,
    fullRecordGapCenterValue + 544818,
    fullRecordGapCenterValue + 544926,
    fullRecordGapCenterValue + 545066,
    fullRecordGapCenterValue + 545078,
    fullRecordGapCenterValue + 545126,
    fullRecordGapCenterValue + 545210,
    fullRecordGapCenterValue + 545268,
    fullRecordGapCenterValue + 545276,
    fullRecordGapCenterValue + 545318,
    fullRecordGapCenterValue + 545672,
    fullRecordGapCenterValue + 545822,
    fullRecordGapCenterValue + 546002,
    fullRecordGapCenterValue + 546092,
    fullRecordGapCenterValue + 546198,
    fullRecordGapCenterValue + 546236,
    fullRecordGapCenterValue + 546362,
    fullRecordGapCenterValue + 546386,
    fullRecordGapCenterValue + 546396,
    fullRecordGapCenterValue + 546470,
    fullRecordGapCenterValue + 546486,
    fullRecordGapCenterValue + 546488,
    fullRecordGapCenterValue + 546578,
    fullRecordGapCenterValue + 546596,
    fullRecordGapCenterValue + 546632,
    fullRecordGapCenterValue + 546726,
    fullRecordGapCenterValue + 546836,
    fullRecordGapCenterValue + 546866,
    fullRecordGapCenterValue + 546908,
    fullRecordGapCenterValue + 546932,
    fullRecordGapCenterValue + 546978,
    fullRecordGapCenterValue + 547226,
    fullRecordGapCenterValue + 547418,
    fullRecordGapCenterValue + 547458,
    fullRecordGapCenterValue + 547478,
    fullRecordGapCenterValue + 547556,
    fullRecordGapCenterValue + 547746,
    fullRecordGapCenterValue + 547782,
    fullRecordGapCenterValue + 547790,
    fullRecordGapCenterValue + 547908,
    fullRecordGapCenterValue + 547958,
    fullRecordGapCenterValue + 548076,
    fullRecordGapCenterValue + 548186,
    fullRecordGapCenterValue + 548292,
    fullRecordGapCenterValue + 548312,
    fullRecordGapCenterValue + 548322]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00143_fermat : ∀ n ∈ fullRecordGapRow00143_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09089_not_prime : ¬(recordGapCenter + 543908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 543908]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09090_not_prime : ¬(recordGapCenter + 544058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544058]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09091_not_prime : ¬(recordGapCenter + 544062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544062]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09092_not_prime : ¬(recordGapCenter + 544182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544182]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09093_not_prime : ¬(recordGapCenter + 544190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544190]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09094_not_prime : ¬(recordGapCenter + 544332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544332]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09095_not_prime : ¬(recordGapCenter + 544472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544472]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09096_not_prime : ¬(recordGapCenter + 544490).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544490]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09097_not_prime : ¬(recordGapCenter + 544500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544500]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09098_not_prime : ¬(recordGapCenter + 544526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544526]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09099_not_prime : ¬(recordGapCenter + 544532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544532]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09100_not_prime : ¬(recordGapCenter + 544568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544568]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09101_not_prime : ¬(recordGapCenter + 544598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544598]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09102_not_prime : ¬(recordGapCenter + 544652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544652]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09103_not_prime : ¬(recordGapCenter + 544682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544682]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09104_not_prime : ¬(recordGapCenter + 544722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544722]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09105_not_prime : ¬(recordGapCenter + 544758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544758]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09106_not_prime : ¬(recordGapCenter + 544766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544766]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09107_not_prime : ¬(recordGapCenter + 544772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544772]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09108_not_prime : ¬(recordGapCenter + 544818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544818]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09109_not_prime : ¬(recordGapCenter + 544926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 544926]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09110_not_prime : ¬(recordGapCenter + 545066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545066]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09111_not_prime : ¬(recordGapCenter + 545078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545078]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09112_not_prime : ¬(recordGapCenter + 545126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545126]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09113_not_prime : ¬(recordGapCenter + 545210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545210]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09114_not_prime : ¬(recordGapCenter + 545268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545268]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09115_not_prime : ¬(recordGapCenter + 545276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545276]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09116_not_prime : ¬(recordGapCenter + 545318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545318]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09117_not_prime : ¬(recordGapCenter + 545672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545672]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09118_not_prime : ¬(recordGapCenter + 545822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 545822]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09119_not_prime : ¬(recordGapCenter + 546002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546002]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09120_not_prime : ¬(recordGapCenter + 546092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546092]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09121_not_prime : ¬(recordGapCenter + 546198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546198]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09122_not_prime : ¬(recordGapCenter + 546236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546236]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09123_not_prime : ¬(recordGapCenter + 546362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546362]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09124_not_prime : ¬(recordGapCenter + 546386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546386]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09125_not_prime : ¬(recordGapCenter + 546396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546396]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09126_not_prime : ¬(recordGapCenter + 546470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546470]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09127_not_prime : ¬(recordGapCenter + 546486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546486]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09128_not_prime : ¬(recordGapCenter + 546488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546488]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09129_not_prime : ¬(recordGapCenter + 546578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546578]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09130_not_prime : ¬(recordGapCenter + 546596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546596]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09131_not_prime : ¬(recordGapCenter + 546632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546632]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09132_not_prime : ¬(recordGapCenter + 546726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546726]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09133_not_prime : ¬(recordGapCenter + 546836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546836]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09134_not_prime : ¬(recordGapCenter + 546866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546866]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09135_not_prime : ¬(recordGapCenter + 546908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546908]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09136_not_prime : ¬(recordGapCenter + 546932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546932]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09137_not_prime : ¬(recordGapCenter + 546978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 546978]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09138_not_prime : ¬(recordGapCenter + 547226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547226]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09139_not_prime : ¬(recordGapCenter + 547418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547418]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09140_not_prime : ¬(recordGapCenter + 547458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547458]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09141_not_prime : ¬(recordGapCenter + 547478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547478]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09142_not_prime : ¬(recordGapCenter + 547556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547556]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09143_not_prime : ¬(recordGapCenter + 547746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547746]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09144_not_prime : ¬(recordGapCenter + 547782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547782]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09145_not_prime : ¬(recordGapCenter + 547790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547790]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09146_not_prime : ¬(recordGapCenter + 547908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547908]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09147_not_prime : ¬(recordGapCenter + 547958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 547958]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09148_not_prime : ¬(recordGapCenter + 548076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548076]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09149_not_prime : ¬(recordGapCenter + 548186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548186]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09150_not_prime : ¬(recordGapCenter + 548292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548292]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09151_not_prime : ¬(recordGapCenter + 548312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548312]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

theorem fullRecordGapTerm09152_not_prime : ¬(recordGapCenter + 548322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548322]
  · apply fullRecordGapRow00143_fermat
    simp [fullRecordGapRow00143_values]

end PrimeFactorUnimodality
