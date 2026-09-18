import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00015_values : List Nat :=
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
    fullRecordGapCenterValue - 39690,
    fullRecordGapCenterValue - 39204,
    fullRecordGapCenterValue - 38808,
    fullRecordGapCenterValue - 38400,
    fullRecordGapCenterValue - 37422,
    fullRecordGapCenterValue - 37044,
    fullRecordGapCenterValue - 35574,
    fullRecordGapCenterValue - 34992,
    fullRecordGapCenterValue - 34848,
    fullRecordGapCenterValue - 34650,
    fullRecordGapCenterValue - 33792,
    fullRecordGapCenterValue - 33600,
    fullRecordGapCenterValue - 33264,
    fullRecordGapCenterValue - 33000,
    fullRecordGapCenterValue - 32928,
    fullRecordGapCenterValue - 32400,
    fullRecordGapCenterValue - 31944,
    fullRecordGapCenterValue - 31752,
    fullRecordGapCenterValue - 31104,
    fullRecordGapCenterValue - 30492,
    fullRecordGapCenterValue - 30184,
    fullRecordGapCenterValue - 29700,
    fullRecordGapCenterValue - 29568,
    fullRecordGapCenterValue - 29400,
    fullRecordGapCenterValue - 29040,
    fullRecordGapCenterValue - 28812,
    fullRecordGapCenterValue - 28672,
    fullRecordGapCenterValue - 27720,
    fullRecordGapCenterValue - 26880,
    fullRecordGapCenterValue - 26730,
    fullRecordGapCenterValue - 26460,
    fullRecordGapCenterValue - 24640,
    fullRecordGapCenterValue - 24192,
    fullRecordGapCenterValue - 24010,
    fullRecordGapCenterValue - 24000,
    fullRecordGapCenterValue - 23958,
    fullRecordGapCenterValue - 23814,
    fullRecordGapCenterValue - 23520,
    fullRecordGapCenterValue - 21870,
    fullRecordGapCenterValue - 21600,
    fullRecordGapCenterValue - 21504,
    fullRecordGapCenterValue - 21384,
    fullRecordGapCenterValue - 21000,
    fullRecordGapCenterValue - 20412,
    fullRecordGapCenterValue - 20160,
    fullRecordGapCenterValue - 19600,
    fullRecordGapCenterValue - 18900,
    fullRecordGapCenterValue - 17280,
    fullRecordGapCenterValue - 16632,
    fullRecordGapCenterValue - 16200,
    fullRecordGapCenterValue - 16170,
    fullRecordGapCenterValue - 15120,
    fullRecordGapCenterValue - 14520,
    fullRecordGapCenterValue - 13824,
    fullRecordGapCenterValue - 13750,
    fullRecordGapCenterValue - 13720,
    fullRecordGapCenterValue - 13500,
    fullRecordGapCenterValue - 13440,
    fullRecordGapCenterValue - 13068,
    fullRecordGapCenterValue - 12960,
    fullRecordGapCenterValue - 12672,
    fullRecordGapCenterValue - 12150,
    fullRecordGapCenterValue - 12100,
    fullRecordGapCenterValue - 11760,
    fullRecordGapCenterValue - 11340,
    fullRecordGapCenterValue - 11200,
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
    fullRecordGapCenterValue - 1750,
    fullRecordGapCenterValue - 1728,
    fullRecordGapCenterValue - 1620,
    fullRecordGapCenterValue - 1600,
    fullRecordGapCenterValue - 1584,
    fullRecordGapCenterValue - 1540,
    fullRecordGapCenterValue - 1470,
    fullRecordGapCenterValue - 1458,
    fullRecordGapCenterValue - 1372,
    fullRecordGapCenterValue - 1188,
    fullRecordGapCenterValue - 1152,
    fullRecordGapCenterValue - 1078,
    fullRecordGapCenterValue - 1000,
    fullRecordGapCenterValue - 880,
    fullRecordGapCenterValue - 810,
    fullRecordGapCenterValue - 768,
    fullRecordGapCenterValue - 648,
    fullRecordGapCenterValue - 600,
    fullRecordGapCenterValue - 594,
    fullRecordGapCenterValue - 588,
    fullRecordGapCenterValue - 462,
    fullRecordGapCenterValue - 448,
    fullRecordGapCenterValue - 420,
    fullRecordGapCenterValue - 384,
    fullRecordGapCenterValue - 352,
    fullRecordGapCenterValue - 270,
    fullRecordGapCenterValue - 252,
    fullRecordGapCenterValue - 250,
    fullRecordGapCenterValue - 240,
    fullRecordGapCenterValue - 198,
    fullRecordGapCenterValue - 192,
    fullRecordGapCenterValue - 108,
    fullRecordGapCenterValue - 100,
    fullRecordGapCenterValue - 90,
    fullRecordGapCenterValue - 88,
    fullRecordGapCenterValue - 84,
    fullRecordGapCenterValue - 60,
    fullRecordGapCenterValue - 54,
    fullRecordGapCenterValue - 24,
    fullRecordGapCenterValue - 12,
    fullRecordGapCenterValue + 66,
    fullRecordGapCenterValue + 72,
    fullRecordGapCenterValue + 96,
    fullRecordGapCenterValue + 110,
    fullRecordGapCenterValue + 126,
    fullRecordGapCenterValue + 140,
    fullRecordGapCenterValue + 162,
    fullRecordGapCenterValue + 176,
    fullRecordGapCenterValue + 192,
    fullRecordGapCenterValue + 240,
    fullRecordGapCenterValue + 252,
    fullRecordGapCenterValue + 336,
    fullRecordGapCenterValue + 350,
    fullRecordGapCenterValue + 360,
    fullRecordGapCenterValue + 420,
    fullRecordGapCenterValue + 486,
    fullRecordGapCenterValue + 512,
    fullRecordGapCenterValue + 528,
    fullRecordGapCenterValue + 560,
    fullRecordGapCenterValue + 576,
    fullRecordGapCenterValue + 588,
    fullRecordGapCenterValue + 600,
    fullRecordGapCenterValue + 660,
    fullRecordGapCenterValue + 726,
    fullRecordGapCenterValue + 882]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00015_fermat : ∀ n ∈ fullRecordGapRow00015_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03585_not_prime : ¬(recordGapCenter - 87994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 87994]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03586_not_prime : ¬(recordGapCenter - 87442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 87442]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03587_not_prime : ¬(recordGapCenter - 87318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 87318]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03588_not_prime : ¬(recordGapCenter - 87154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 87154]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03589_not_prime : ¬(recordGapCenter - 86902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 86902]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03590_not_prime : ¬(recordGapCenter - 86854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 86854]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03591_not_prime : ¬(recordGapCenter - 86638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 86638]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03592_not_prime : ¬(recordGapCenter - 86400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 86400]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03593_not_prime : ¬(recordGapCenter - 84672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 84672]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03594_not_prime : ¬(recordGapCenter - 81648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 81648]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03595_not_prime : ¬(recordGapCenter - 81000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 81000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03596_not_prime : ¬(recordGapCenter - 80850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 80850]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03597_not_prime : ¬(recordGapCenter - 80190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 80190]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03598_not_prime : ¬(recordGapCenter - 78400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 78400]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03599_not_prime : ¬(recordGapCenter - 76800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 76800]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03600_not_prime : ¬(recordGapCenter - 76032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 76032]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03601_not_prime : ¬(recordGapCenter - 74088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 74088]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03602_not_prime : ¬(recordGapCenter - 73920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 73920]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03603_not_prime : ¬(recordGapCenter - 73728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 73728]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03604_not_prime : ¬(recordGapCenter - 72900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 72900]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03605_not_prime : ¬(recordGapCenter - 72030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 72030]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03606_not_prime : ¬(recordGapCenter - 71874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 71874]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03607_not_prime : ¬(recordGapCenter - 71280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 71280]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03608_not_prime : ¬(recordGapCenter - 70560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 70560]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03609_not_prime : ¬(recordGapCenter - 69300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 69300]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03610_not_prime : ¬(recordGapCenter - 68992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 68992]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03611_not_prime : ¬(recordGapCenter - 68040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 68040]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03612_not_prime : ¬(recordGapCenter - 67584).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 67584]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03613_not_prime : ¬(recordGapCenter - 67228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 67228]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03614_not_prime : ¬(recordGapCenter - 67200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 67200]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03615_not_prime : ¬(recordGapCenter - 65340).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 65340]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03616_not_prime : ¬(recordGapCenter - 63888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 63888]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03617_not_prime : ¬(recordGapCenter - 63000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 63000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03618_not_prime : ¬(recordGapCenter - 62208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 62208]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03619_not_prime : ¬(recordGapCenter - 61740).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 61740]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03620_not_prime : ¬(recordGapCenter - 60480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 60480]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03621_not_prime : ¬(recordGapCenter - 57750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 57750]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03622_not_prime : ¬(recordGapCenter - 57624).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 57624]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03623_not_prime : ¬(recordGapCenter - 56250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 56250]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03624_not_prime : ¬(recordGapCenter - 55440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 55440]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03625_not_prime : ¬(recordGapCenter - 54450).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 54450]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03626_not_prime : ¬(recordGapCenter - 54208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 54208]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03627_not_prime : ¬(recordGapCenter - 53760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 53760]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03628_not_prime : ¬(recordGapCenter - 52800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 52800]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03629_not_prime : ¬(recordGapCenter - 51744).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 51744]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03630_not_prime : ¬(recordGapCenter - 49392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 49392]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03631_not_prime : ¬(recordGapCenter - 49000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 49000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03632_not_prime : ¬(recordGapCenter - 48510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 48510]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03633_not_prime : ¬(recordGapCenter - 48400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 48400]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03634_not_prime : ¬(recordGapCenter - 48114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 48114]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03635_not_prime : ¬(recordGapCenter - 47250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 47250]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03636_not_prime : ¬(recordGapCenter - 46464).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 46464]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03637_not_prime : ¬(recordGapCenter - 46080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 46080]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03638_not_prime : ¬(recordGapCenter - 45000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 45000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03639_not_prime : ¬(recordGapCenter - 44550).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 44550]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03640_not_prime : ¬(recordGapCenter - 43200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 43200]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03641_not_prime : ¬(recordGapCenter - 42768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 42768]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03642_not_prime : ¬(recordGapCenter - 42592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 42592]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03643_not_prime : ¬(recordGapCenter - 41250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 41250]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03644_not_prime : ¬(recordGapCenter - 41160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 41160]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03645_not_prime : ¬(recordGapCenter - 40960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 40960]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03646_not_prime : ¬(recordGapCenter - 40824).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 40824]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03647_not_prime : ¬(recordGapCenter - 39930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 39930]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03648_not_prime : ¬(recordGapCenter - 39690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 39690]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03649_not_prime : ¬(recordGapCenter - 39204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 39204]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03650_not_prime : ¬(recordGapCenter - 38808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 38808]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03651_not_prime : ¬(recordGapCenter - 38400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 38400]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03652_not_prime : ¬(recordGapCenter - 37422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 37422]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03653_not_prime : ¬(recordGapCenter - 37044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 37044]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03654_not_prime : ¬(recordGapCenter - 35574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 35574]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03655_not_prime : ¬(recordGapCenter - 34992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 34992]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03656_not_prime : ¬(recordGapCenter - 34848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 34848]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03657_not_prime : ¬(recordGapCenter - 34650).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 34650]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03658_not_prime : ¬(recordGapCenter - 33792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 33792]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03659_not_prime : ¬(recordGapCenter - 33600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 33600]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03660_not_prime : ¬(recordGapCenter - 33264).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 33264]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03661_not_prime : ¬(recordGapCenter - 33000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 33000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03662_not_prime : ¬(recordGapCenter - 32928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 32928]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03663_not_prime : ¬(recordGapCenter - 32400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 32400]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03664_not_prime : ¬(recordGapCenter - 31944).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 31944]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03665_not_prime : ¬(recordGapCenter - 31752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 31752]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03666_not_prime : ¬(recordGapCenter - 31104).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 31104]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03667_not_prime : ¬(recordGapCenter - 30492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 30492]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03668_not_prime : ¬(recordGapCenter - 30184).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 30184]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03669_not_prime : ¬(recordGapCenter - 29700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 29700]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03670_not_prime : ¬(recordGapCenter - 29568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 29568]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03671_not_prime : ¬(recordGapCenter - 29400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 29400]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03672_not_prime : ¬(recordGapCenter - 29040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 29040]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03673_not_prime : ¬(recordGapCenter - 28812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 28812]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03674_not_prime : ¬(recordGapCenter - 28672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 28672]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03675_not_prime : ¬(recordGapCenter - 27720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 27720]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03676_not_prime : ¬(recordGapCenter - 26880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 26880]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03677_not_prime : ¬(recordGapCenter - 26730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 26730]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03678_not_prime : ¬(recordGapCenter - 26460).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 26460]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03679_not_prime : ¬(recordGapCenter - 24640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24640]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03680_not_prime : ¬(recordGapCenter - 24192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24192]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03681_not_prime : ¬(recordGapCenter - 24010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24010]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03682_not_prime : ¬(recordGapCenter - 24000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03683_not_prime : ¬(recordGapCenter - 23958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 23958]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03684_not_prime : ¬(recordGapCenter - 23814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 23814]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03685_not_prime : ¬(recordGapCenter - 23520).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 23520]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03686_not_prime : ¬(recordGapCenter - 21870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21870]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03687_not_prime : ¬(recordGapCenter - 21600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21600]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03688_not_prime : ¬(recordGapCenter - 21504).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21504]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03689_not_prime : ¬(recordGapCenter - 21384).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21384]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03690_not_prime : ¬(recordGapCenter - 21000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03691_not_prime : ¬(recordGapCenter - 20412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 20412]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03692_not_prime : ¬(recordGapCenter - 20160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 20160]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03693_not_prime : ¬(recordGapCenter - 19600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 19600]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03694_not_prime : ¬(recordGapCenter - 18900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 18900]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03695_not_prime : ¬(recordGapCenter - 17280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 17280]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03696_not_prime : ¬(recordGapCenter - 16632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 16632]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03697_not_prime : ¬(recordGapCenter - 16200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 16200]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03698_not_prime : ¬(recordGapCenter - 16170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 16170]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03699_not_prime : ¬(recordGapCenter - 15120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 15120]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03700_not_prime : ¬(recordGapCenter - 14520).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 14520]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03701_not_prime : ¬(recordGapCenter - 13824).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13824]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03702_not_prime : ¬(recordGapCenter - 13750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13750]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03703_not_prime : ¬(recordGapCenter - 13720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13720]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03704_not_prime : ¬(recordGapCenter - 13500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13500]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03705_not_prime : ¬(recordGapCenter - 13440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13440]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03706_not_prime : ¬(recordGapCenter - 13068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13068]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03707_not_prime : ¬(recordGapCenter - 12960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12960]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03708_not_prime : ¬(recordGapCenter - 12672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12672]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03709_not_prime : ¬(recordGapCenter - 12150).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12150]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03710_not_prime : ¬(recordGapCenter - 12100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12100]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03711_not_prime : ¬(recordGapCenter - 11760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 11760]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03712_not_prime : ¬(recordGapCenter - 11340).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 11340]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03713_not_prime : ¬(recordGapCenter - 11200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 11200]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03714_not_prime : ¬(recordGapCenter - 11088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 11088]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03715_not_prime : ¬(recordGapCenter - 10800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 10800]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03716_not_prime : ¬(recordGapCenter - 10692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 10692]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03717_not_prime : ¬(recordGapCenter - 10290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 10290]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03718_not_prime : ¬(recordGapCenter - 10000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 10000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03719_not_prime : ¬(recordGapCenter - 9900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9900]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03720_not_prime : ¬(recordGapCenter - 9720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9720]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03721_not_prime : ¬(recordGapCenter - 9702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9702]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03722_not_prime : ¬(recordGapCenter - 9604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9604]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03723_not_prime : ¬(recordGapCenter - 9504).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9504]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03724_not_prime : ¬(recordGapCenter - 9240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9240]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03725_not_prime : ¬(recordGapCenter - 9000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 9000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03726_not_prime : ¬(recordGapCenter - 8820).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 8820]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03727_not_prime : ¬(recordGapCenter - 7938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 7938]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03728_not_prime : ¬(recordGapCenter - 7840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 7840]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03729_not_prime : ¬(recordGapCenter - 7500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 7500]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03730_not_prime : ¬(recordGapCenter - 6750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6750]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03731_not_prime : ¬(recordGapCenter - 6600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6600]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03732_not_prime : ¬(recordGapCenter - 6468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6468]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03733_not_prime : ¬(recordGapCenter - 6400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6400]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03734_not_prime : ¬(recordGapCenter - 6250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6250]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03735_not_prime : ¬(recordGapCenter - 6174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6174]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03736_not_prime : ¬(recordGapCenter - 6160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6160]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03737_not_prime : ¬(recordGapCenter - 6048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 6048]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03738_not_prime : ¬(recordGapCenter - 5940).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5940]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03739_not_prime : ¬(recordGapCenter - 5880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5880]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03740_not_prime : ¬(recordGapCenter - 5670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5670]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03741_not_prime : ¬(recordGapCenter - 5544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5544]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03742_not_prime : ¬(recordGapCenter - 5500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5500]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03743_not_prime : ¬(recordGapCenter - 5488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5488]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03744_not_prime : ¬(recordGapCenter - 5400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5400]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03745_not_prime : ¬(recordGapCenter - 5292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5292]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03746_not_prime : ¬(recordGapCenter - 5280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5280]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03747_not_prime : ¬(recordGapCenter - 5250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 5250]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03748_not_prime : ¬(recordGapCenter - 4840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4840]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03749_not_prime : ¬(recordGapCenter - 4704).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4704]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03750_not_prime : ¬(recordGapCenter - 4410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4410]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03751_not_prime : ¬(recordGapCenter - 4374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4374]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03752_not_prime : ¬(recordGapCenter - 4224).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4224]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03753_not_prime : ¬(recordGapCenter - 4158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4158]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03754_not_prime : ¬(recordGapCenter - 4032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 4032]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03755_not_prime : ¬(recordGapCenter - 3780).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3780]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03756_not_prime : ¬(recordGapCenter - 3750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3750]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03757_not_prime : ¬(recordGapCenter - 3630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3630]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03758_not_prime : ¬(recordGapCenter - 3600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3600]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03759_not_prime : ¬(recordGapCenter - 3430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3430]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03760_not_prime : ¬(recordGapCenter - 3388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3388]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03761_not_prime : ¬(recordGapCenter - 3360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3360]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03762_not_prime : ¬(recordGapCenter - 3300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3300]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03763_not_prime : ¬(recordGapCenter - 3240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 3240]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03764_not_prime : ¬(recordGapCenter - 2904).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2904]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03765_not_prime : ¬(recordGapCenter - 2880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2880]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03766_not_prime : ¬(recordGapCenter - 2800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2800]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03767_not_prime : ¬(recordGapCenter - 2464).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2464]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03768_not_prime : ¬(recordGapCenter - 2352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2352]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03769_not_prime : ¬(recordGapCenter - 2310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2310]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03770_not_prime : ¬(recordGapCenter - 2250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2250]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03771_not_prime : ¬(recordGapCenter - 2112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 2112]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03772_not_prime : ¬(recordGapCenter - 1980).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1980]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03773_not_prime : ¬(recordGapCenter - 1920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1920]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03774_not_prime : ¬(recordGapCenter - 1890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1890]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03775_not_prime : ¬(recordGapCenter - 1848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1848]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03776_not_prime : ¬(recordGapCenter - 1750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1750]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03777_not_prime : ¬(recordGapCenter - 1728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1728]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03778_not_prime : ¬(recordGapCenter - 1620).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1620]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03779_not_prime : ¬(recordGapCenter - 1600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1600]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03780_not_prime : ¬(recordGapCenter - 1584).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1584]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03781_not_prime : ¬(recordGapCenter - 1540).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1540]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03782_not_prime : ¬(recordGapCenter - 1470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1470]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03783_not_prime : ¬(recordGapCenter - 1458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1458]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03784_not_prime : ¬(recordGapCenter - 1372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1372]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03785_not_prime : ¬(recordGapCenter - 1188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1188]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03786_not_prime : ¬(recordGapCenter - 1152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1152]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03787_not_prime : ¬(recordGapCenter - 1078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1078]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03788_not_prime : ¬(recordGapCenter - 1000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 1000]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03789_not_prime : ¬(recordGapCenter - 880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 880]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03790_not_prime : ¬(recordGapCenter - 810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 810]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03791_not_prime : ¬(recordGapCenter - 768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 768]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03792_not_prime : ¬(recordGapCenter - 648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 648]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03793_not_prime : ¬(recordGapCenter - 600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 600]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03794_not_prime : ¬(recordGapCenter - 594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 594]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03795_not_prime : ¬(recordGapCenter - 588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 588]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03796_not_prime : ¬(recordGapCenter - 462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 462]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03797_not_prime : ¬(recordGapCenter - 448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03798_not_prime : ¬(recordGapCenter - 420).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03799_not_prime : ¬(recordGapCenter - 384).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03800_not_prime : ¬(recordGapCenter - 352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 352]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03801_not_prime : ¬(recordGapCenter - 270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 270]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03802_not_prime : ¬(recordGapCenter - 252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03803_not_prime : ¬(recordGapCenter - 250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03804_not_prime : ¬(recordGapCenter - 240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03805_not_prime : ¬(recordGapCenter - 198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03806_not_prime : ¬(recordGapCenter - 192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03807_not_prime : ¬(recordGapCenter - 108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03808_not_prime : ¬(recordGapCenter - 100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03809_not_prime : ¬(recordGapCenter - 90).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03810_not_prime : ¬(recordGapCenter - 88).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03811_not_prime : ¬(recordGapCenter - 84).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 84]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03812_not_prime : ¬(recordGapCenter - 60).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 60]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03813_not_prime : ¬(recordGapCenter - 54).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 54]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03814_not_prime : ¬(recordGapCenter - 24).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03815_not_prime : ¬(recordGapCenter - 12).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03816_not_prime : ¬(recordGapCenter + 66).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 66]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03817_not_prime : ¬(recordGapCenter + 72).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 72]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03818_not_prime : ¬(recordGapCenter + 96).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03819_not_prime : ¬(recordGapCenter + 110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03820_not_prime : ¬(recordGapCenter + 126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03821_not_prime : ¬(recordGapCenter + 140).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03822_not_prime : ¬(recordGapCenter + 162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03823_not_prime : ¬(recordGapCenter + 176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 176]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03824_not_prime : ¬(recordGapCenter + 192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03825_not_prime : ¬(recordGapCenter + 240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03826_not_prime : ¬(recordGapCenter + 252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 252]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03827_not_prime : ¬(recordGapCenter + 336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03828_not_prime : ¬(recordGapCenter + 350).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03829_not_prime : ¬(recordGapCenter + 360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03830_not_prime : ¬(recordGapCenter + 420).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03831_not_prime : ¬(recordGapCenter + 486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03832_not_prime : ¬(recordGapCenter + 512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03833_not_prime : ¬(recordGapCenter + 528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03834_not_prime : ¬(recordGapCenter + 560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03835_not_prime : ¬(recordGapCenter + 576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03836_not_prime : ¬(recordGapCenter + 588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 588]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03837_not_prime : ¬(recordGapCenter + 600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03838_not_prime : ¬(recordGapCenter + 660).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 660]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03839_not_prime : ¬(recordGapCenter + 726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 726]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm03840_not_prime : ¬(recordGapCenter + 882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 882]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

end PrimeFactorUnimodality
