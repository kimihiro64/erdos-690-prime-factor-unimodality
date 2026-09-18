import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00057_values : List Nat :=
  [fullRecordGapCenterValue - 87994,
    fullRecordGapCenterValue - 87442,
    fullRecordGapCenterValue - 87318,
    fullRecordGapCenterValue - 87154,
    fullRecordGapCenterValue - 86902,
    fullRecordGapCenterValue - 86854,
    fullRecordGapCenterValue - 86638,
    fullRecordGapCenterValue - 86400,
    fullRecordGapCenterValue - 84672,
    fullRecordGapCenterValue - 81648,
    fullRecordGapCenterValue - 81000,
    fullRecordGapCenterValue - 80850,
    fullRecordGapCenterValue - 80190,
    fullRecordGapCenterValue - 78400,
    fullRecordGapCenterValue - 76800,
    fullRecordGapCenterValue - 76032,
    fullRecordGapCenterValue - 74088,
    fullRecordGapCenterValue - 73920,
    fullRecordGapCenterValue - 73728,
    fullRecordGapCenterValue - 72900,
    fullRecordGapCenterValue - 72030,
    fullRecordGapCenterValue - 71874,
    fullRecordGapCenterValue - 71280,
    fullRecordGapCenterValue - 70560,
    fullRecordGapCenterValue - 69300,
    fullRecordGapCenterValue - 68992,
    fullRecordGapCenterValue - 68040,
    fullRecordGapCenterValue - 67584,
    fullRecordGapCenterValue - 67228,
    fullRecordGapCenterValue - 67200,
    fullRecordGapCenterValue - 65340,
    fullRecordGapCenterValue - 63888,
    fullRecordGapCenterValue - 63000,
    fullRecordGapCenterValue - 62208,
    fullRecordGapCenterValue - 61740,
    fullRecordGapCenterValue - 60480,
    fullRecordGapCenterValue - 57750,
    fullRecordGapCenterValue - 57624,
    fullRecordGapCenterValue - 56250,
    fullRecordGapCenterValue - 55440,
    fullRecordGapCenterValue - 54450,
    fullRecordGapCenterValue - 54208,
    fullRecordGapCenterValue - 53760,
    fullRecordGapCenterValue - 52800,
    fullRecordGapCenterValue - 51744,
    fullRecordGapCenterValue - 49392,
    fullRecordGapCenterValue - 49000,
    fullRecordGapCenterValue - 48510,
    fullRecordGapCenterValue - 48400,
    fullRecordGapCenterValue - 48114,
    fullRecordGapCenterValue - 47250,
    fullRecordGapCenterValue - 46464,
    fullRecordGapCenterValue - 46080,
    fullRecordGapCenterValue - 45000,
    fullRecordGapCenterValue - 44550,
    fullRecordGapCenterValue - 43200,
    fullRecordGapCenterValue - 42768,
    fullRecordGapCenterValue - 42592,
    fullRecordGapCenterValue - 41250,
    fullRecordGapCenterValue - 41160,
    fullRecordGapCenterValue - 40960,
    fullRecordGapCenterValue - 40824,
    fullRecordGapCenterValue - 39930,
    fullRecordGapCenterValue - 39690]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00057_fermat : ∀ n ∈ fullRecordGapRow00057_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03585_not_prime : ¬(recordGapCenter - 87994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 87994]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03586_not_prime : ¬(recordGapCenter - 87442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 87442]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03587_not_prime : ¬(recordGapCenter - 87318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 87318]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03588_not_prime : ¬(recordGapCenter - 87154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 87154]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03589_not_prime : ¬(recordGapCenter - 86902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 86902]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03590_not_prime : ¬(recordGapCenter - 86854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 86854]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03591_not_prime : ¬(recordGapCenter - 86638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 86638]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03592_not_prime : ¬(recordGapCenter - 86400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 86400]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03593_not_prime : ¬(recordGapCenter - 84672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 84672]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03594_not_prime : ¬(recordGapCenter - 81648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 81648]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03595_not_prime : ¬(recordGapCenter - 81000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 81000]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03596_not_prime : ¬(recordGapCenter - 80850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 80850]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03597_not_prime : ¬(recordGapCenter - 80190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 80190]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03598_not_prime : ¬(recordGapCenter - 78400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 78400]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03599_not_prime : ¬(recordGapCenter - 76800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 76800]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03600_not_prime : ¬(recordGapCenter - 76032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 76032]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03601_not_prime : ¬(recordGapCenter - 74088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 74088]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03602_not_prime : ¬(recordGapCenter - 73920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 73920]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03603_not_prime : ¬(recordGapCenter - 73728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 73728]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03604_not_prime : ¬(recordGapCenter - 72900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 72900]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03605_not_prime : ¬(recordGapCenter - 72030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 72030]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03606_not_prime : ¬(recordGapCenter - 71874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 71874]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03607_not_prime : ¬(recordGapCenter - 71280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 71280]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03608_not_prime : ¬(recordGapCenter - 70560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 70560]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03609_not_prime : ¬(recordGapCenter - 69300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 69300]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03610_not_prime : ¬(recordGapCenter - 68992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 68992]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03611_not_prime : ¬(recordGapCenter - 68040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 68040]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03612_not_prime : ¬(recordGapCenter - 67584).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 67584]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03613_not_prime : ¬(recordGapCenter - 67228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 67228]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03614_not_prime : ¬(recordGapCenter - 67200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 67200]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03615_not_prime : ¬(recordGapCenter - 65340).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 65340]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03616_not_prime : ¬(recordGapCenter - 63888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 63888]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03617_not_prime : ¬(recordGapCenter - 63000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 63000]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03618_not_prime : ¬(recordGapCenter - 62208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 62208]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03619_not_prime : ¬(recordGapCenter - 61740).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 61740]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03620_not_prime : ¬(recordGapCenter - 60480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 60480]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03621_not_prime : ¬(recordGapCenter - 57750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 57750]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03622_not_prime : ¬(recordGapCenter - 57624).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 57624]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03623_not_prime : ¬(recordGapCenter - 56250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 56250]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03624_not_prime : ¬(recordGapCenter - 55440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 55440]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03625_not_prime : ¬(recordGapCenter - 54450).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 54450]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03626_not_prime : ¬(recordGapCenter - 54208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 54208]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03627_not_prime : ¬(recordGapCenter - 53760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 53760]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03628_not_prime : ¬(recordGapCenter - 52800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 52800]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03629_not_prime : ¬(recordGapCenter - 51744).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 51744]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03630_not_prime : ¬(recordGapCenter - 49392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 49392]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03631_not_prime : ¬(recordGapCenter - 49000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 49000]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03632_not_prime : ¬(recordGapCenter - 48510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 48510]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03633_not_prime : ¬(recordGapCenter - 48400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 48400]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03634_not_prime : ¬(recordGapCenter - 48114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 48114]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03635_not_prime : ¬(recordGapCenter - 47250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 47250]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03636_not_prime : ¬(recordGapCenter - 46464).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 46464]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03637_not_prime : ¬(recordGapCenter - 46080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 46080]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03638_not_prime : ¬(recordGapCenter - 45000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 45000]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03639_not_prime : ¬(recordGapCenter - 44550).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 44550]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03640_not_prime : ¬(recordGapCenter - 43200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 43200]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03641_not_prime : ¬(recordGapCenter - 42768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 42768]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03642_not_prime : ¬(recordGapCenter - 42592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 42592]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03643_not_prime : ¬(recordGapCenter - 41250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 41250]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03644_not_prime : ¬(recordGapCenter - 41160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 41160]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03645_not_prime : ¬(recordGapCenter - 40960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 40960]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03646_not_prime : ¬(recordGapCenter - 40824).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 40824]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03647_not_prime : ¬(recordGapCenter - 39930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 39930]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

theorem fullRecordGapTerm03648_not_prime : ¬(recordGapCenter - 39690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 39690]
  · apply fullRecordGapRow00057_fermat
    simp [fullRecordGapRow00057_values]

end PrimeFactorUnimodality
