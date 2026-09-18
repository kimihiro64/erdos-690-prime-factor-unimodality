import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00059_values : List Nat :=
  [fullRecordGapCenterValue - 11200,
    fullRecordGapCenterValue - 11088,
    fullRecordGapCenterValue - 10800,
    fullRecordGapCenterValue - 10692,
    fullRecordGapCenterValue - 10290,
    fullRecordGapCenterValue - 10000,
    fullRecordGapCenterValue - 9900,
    fullRecordGapCenterValue - 9720,
    fullRecordGapCenterValue - 9702,
    fullRecordGapCenterValue - 9604,
    fullRecordGapCenterValue - 9504,
    fullRecordGapCenterValue - 9240,
    fullRecordGapCenterValue - 9000,
    fullRecordGapCenterValue - 8820,
    fullRecordGapCenterValue - 7938,
    fullRecordGapCenterValue - 7840,
    fullRecordGapCenterValue - 7500,
    fullRecordGapCenterValue - 6750,
    fullRecordGapCenterValue - 6600,
    fullRecordGapCenterValue - 6468,
    fullRecordGapCenterValue - 6400,
    fullRecordGapCenterValue - 6250,
    fullRecordGapCenterValue - 6174,
    fullRecordGapCenterValue - 6160,
    fullRecordGapCenterValue - 6048,
    fullRecordGapCenterValue - 5940,
    fullRecordGapCenterValue - 5880,
    fullRecordGapCenterValue - 5670,
    fullRecordGapCenterValue - 5544,
    fullRecordGapCenterValue - 5500,
    fullRecordGapCenterValue - 5488,
    fullRecordGapCenterValue - 5400,
    fullRecordGapCenterValue - 5292,
    fullRecordGapCenterValue - 5280,
    fullRecordGapCenterValue - 5250,
    fullRecordGapCenterValue - 4840,
    fullRecordGapCenterValue - 4704,
    fullRecordGapCenterValue - 4410,
    fullRecordGapCenterValue - 4374,
    fullRecordGapCenterValue - 4224,
    fullRecordGapCenterValue - 4158,
    fullRecordGapCenterValue - 4032,
    fullRecordGapCenterValue - 3780,
    fullRecordGapCenterValue - 3750,
    fullRecordGapCenterValue - 3630,
    fullRecordGapCenterValue - 3600,
    fullRecordGapCenterValue - 3430,
    fullRecordGapCenterValue - 3388,
    fullRecordGapCenterValue - 3360,
    fullRecordGapCenterValue - 3300,
    fullRecordGapCenterValue - 3240,
    fullRecordGapCenterValue - 2904,
    fullRecordGapCenterValue - 2880,
    fullRecordGapCenterValue - 2800,
    fullRecordGapCenterValue - 2464,
    fullRecordGapCenterValue - 2352,
    fullRecordGapCenterValue - 2310,
    fullRecordGapCenterValue - 2250,
    fullRecordGapCenterValue - 2112,
    fullRecordGapCenterValue - 1980,
    fullRecordGapCenterValue - 1920,
    fullRecordGapCenterValue - 1890,
    fullRecordGapCenterValue - 1848,
    fullRecordGapCenterValue - 1750]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00059_fermat : ∀ n ∈ fullRecordGapRow00059_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03713_not_prime : ¬(recordGapCenter - 11200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 11200]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03714_not_prime : ¬(recordGapCenter - 11088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 11088]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03715_not_prime : ¬(recordGapCenter - 10800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 10800]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03716_not_prime : ¬(recordGapCenter - 10692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 10692]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03717_not_prime : ¬(recordGapCenter - 10290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 10290]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03718_not_prime : ¬(recordGapCenter - 10000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 10000]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03719_not_prime : ¬(recordGapCenter - 9900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9900]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03720_not_prime : ¬(recordGapCenter - 9720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9720]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03721_not_prime : ¬(recordGapCenter - 9702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9702]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03722_not_prime : ¬(recordGapCenter - 9604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9604]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03723_not_prime : ¬(recordGapCenter - 9504).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9504]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03724_not_prime : ¬(recordGapCenter - 9240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9240]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03725_not_prime : ¬(recordGapCenter - 9000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9000]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03726_not_prime : ¬(recordGapCenter - 8820).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 8820]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03727_not_prime : ¬(recordGapCenter - 7938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 7938]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03728_not_prime : ¬(recordGapCenter - 7840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 7840]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03729_not_prime : ¬(recordGapCenter - 7500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 7500]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03730_not_prime : ¬(recordGapCenter - 6750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6750]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03731_not_prime : ¬(recordGapCenter - 6600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6600]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03732_not_prime : ¬(recordGapCenter - 6468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6468]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03733_not_prime : ¬(recordGapCenter - 6400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6400]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03734_not_prime : ¬(recordGapCenter - 6250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6250]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03735_not_prime : ¬(recordGapCenter - 6174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6174]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03736_not_prime : ¬(recordGapCenter - 6160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6160]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03737_not_prime : ¬(recordGapCenter - 6048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6048]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03738_not_prime : ¬(recordGapCenter - 5940).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5940]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03739_not_prime : ¬(recordGapCenter - 5880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5880]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03740_not_prime : ¬(recordGapCenter - 5670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5670]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03741_not_prime : ¬(recordGapCenter - 5544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5544]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03742_not_prime : ¬(recordGapCenter - 5500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5500]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03743_not_prime : ¬(recordGapCenter - 5488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5488]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03744_not_prime : ¬(recordGapCenter - 5400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5400]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03745_not_prime : ¬(recordGapCenter - 5292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5292]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03746_not_prime : ¬(recordGapCenter - 5280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5280]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03747_not_prime : ¬(recordGapCenter - 5250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5250]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03748_not_prime : ¬(recordGapCenter - 4840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4840]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03749_not_prime : ¬(recordGapCenter - 4704).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4704]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03750_not_prime : ¬(recordGapCenter - 4410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4410]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03751_not_prime : ¬(recordGapCenter - 4374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4374]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03752_not_prime : ¬(recordGapCenter - 4224).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4224]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03753_not_prime : ¬(recordGapCenter - 4158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4158]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03754_not_prime : ¬(recordGapCenter - 4032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4032]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03755_not_prime : ¬(recordGapCenter - 3780).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3780]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03756_not_prime : ¬(recordGapCenter - 3750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3750]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03757_not_prime : ¬(recordGapCenter - 3630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3630]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03758_not_prime : ¬(recordGapCenter - 3600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3600]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03759_not_prime : ¬(recordGapCenter - 3430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3430]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03760_not_prime : ¬(recordGapCenter - 3388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3388]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03761_not_prime : ¬(recordGapCenter - 3360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3360]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03762_not_prime : ¬(recordGapCenter - 3300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3300]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03763_not_prime : ¬(recordGapCenter - 3240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3240]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03764_not_prime : ¬(recordGapCenter - 2904).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2904]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03765_not_prime : ¬(recordGapCenter - 2880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2880]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03766_not_prime : ¬(recordGapCenter - 2800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2800]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03767_not_prime : ¬(recordGapCenter - 2464).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2464]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03768_not_prime : ¬(recordGapCenter - 2352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2352]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03769_not_prime : ¬(recordGapCenter - 2310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2310]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03770_not_prime : ¬(recordGapCenter - 2250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2250]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03771_not_prime : ¬(recordGapCenter - 2112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2112]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03772_not_prime : ¬(recordGapCenter - 1980).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1980]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03773_not_prime : ¬(recordGapCenter - 1920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1920]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03774_not_prime : ¬(recordGapCenter - 1890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1890]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03775_not_prime : ¬(recordGapCenter - 1848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1848]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

theorem fullRecordGapTerm03776_not_prime : ¬(recordGapCenter - 1750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1750]
  · apply fullRecordGapRow00059_fermat
    simp [fullRecordGapRow00059_values]

end PrimeFactorUnimodality
