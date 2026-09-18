import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00016_values : List Nat :=
  [fullRecordGapCenterValue + 968,
    fullRecordGapCenterValue + 990,
    fullRecordGapCenterValue + 1050,
    fullRecordGapCenterValue + 1200,
    fullRecordGapCenterValue + 1260,
    fullRecordGapCenterValue + 1320,
    fullRecordGapCenterValue + 1386,
    fullRecordGapCenterValue + 1452,
    fullRecordGapCenterValue + 1500,
    fullRecordGapCenterValue + 1620,
    fullRecordGapCenterValue + 1650,
    fullRecordGapCenterValue + 1680,
    fullRecordGapCenterValue + 1782,
    fullRecordGapCenterValue + 1848,
    fullRecordGapCenterValue + 2016,
    fullRecordGapCenterValue + 2048,
    fullRecordGapCenterValue + 2058,
    fullRecordGapCenterValue + 2100,
    fullRecordGapCenterValue + 2112,
    fullRecordGapCenterValue + 2156,
    fullRecordGapCenterValue + 2160,
    fullRecordGapCenterValue + 2178,
    fullRecordGapCenterValue + 2352,
    fullRecordGapCenterValue + 2376,
    fullRecordGapCenterValue + 2430,
    fullRecordGapCenterValue + 2450,
    fullRecordGapCenterValue + 2640,
    fullRecordGapCenterValue + 2646,
    fullRecordGapCenterValue + 2772,
    fullRecordGapCenterValue + 2816,
    fullRecordGapCenterValue + 2916,
    fullRecordGapCenterValue + 2940,
    fullRecordGapCenterValue + 2970,
    fullRecordGapCenterValue + 3168,
    fullRecordGapCenterValue + 3200,
    fullRecordGapCenterValue + 3360,
    fullRecordGapCenterValue + 3402,
    fullRecordGapCenterValue + 3456,
    fullRecordGapCenterValue + 3500,
    fullRecordGapCenterValue + 3630,
    fullRecordGapCenterValue + 3696,
    fullRecordGapCenterValue + 3750,
    fullRecordGapCenterValue + 3872,
    fullRecordGapCenterValue + 3920,
    fullRecordGapCenterValue + 3960,
    fullRecordGapCenterValue + 4158,
    fullRecordGapCenterValue + 4320,
    fullRecordGapCenterValue + 4536,
    fullRecordGapCenterValue + 4608,
    fullRecordGapCenterValue + 4860,
    fullRecordGapCenterValue + 4928,
    fullRecordGapCenterValue + 4950,
    fullRecordGapCenterValue + 5000,
    fullRecordGapCenterValue + 5120,
    fullRecordGapCenterValue + 5280,
    fullRecordGapCenterValue + 5292,
    fullRecordGapCenterValue + 5346,
    fullRecordGapCenterValue + 5390,
    fullRecordGapCenterValue + 5670,
    fullRecordGapCenterValue + 5808,
    fullRecordGapCenterValue + 5832,
    fullRecordGapCenterValue + 5880,
    fullRecordGapCenterValue + 6300,
    fullRecordGapCenterValue + 6336,
    fullRecordGapCenterValue + 6480,
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
    fullRecordGapCenterValue + 22680,
    fullRecordGapCenterValue + 23040,
    fullRecordGapCenterValue + 23328,
    fullRecordGapCenterValue + 24000,
    fullRecordGapCenterValue + 24192,
    fullRecordGapCenterValue + 24300,
    fullRecordGapCenterValue + 24500,
    fullRecordGapCenterValue + 24696,
    fullRecordGapCenterValue + 24750,
    fullRecordGapCenterValue + 24948,
    fullRecordGapCenterValue + 25410,
    fullRecordGapCenterValue + 26250,
    fullRecordGapCenterValue + 26460,
    fullRecordGapCenterValue + 27440,
    fullRecordGapCenterValue + 27648,
    fullRecordGapCenterValue + 27720,
    fullRecordGapCenterValue + 28800,
    fullRecordGapCenterValue + 29160,
    fullRecordGapCenterValue + 29568,
    fullRecordGapCenterValue + 30240,
    fullRecordGapCenterValue + 30720,
    fullRecordGapCenterValue + 30800,
    fullRecordGapCenterValue + 32076,
    fullRecordGapCenterValue + 32340,
    fullRecordGapCenterValue + 32400,
    fullRecordGapCenterValue + 32670,
    fullRecordGapCenterValue + 33000,
    fullRecordGapCenterValue + 33600,
    fullRecordGapCenterValue + 34020,
    fullRecordGapCenterValue + 35000,
    fullRecordGapCenterValue + 35640,
    fullRecordGapCenterValue + 35840,
    fullRecordGapCenterValue + 37500,
    fullRecordGapCenterValue + 37632,
    fullRecordGapCenterValue + 38400,
    fullRecordGapCenterValue + 38880,
    fullRecordGapCenterValue + 39600,
    fullRecordGapCenterValue + 39690,
    fullRecordGapCenterValue + 40656,
    fullRecordGapCenterValue + 41472,
    fullRecordGapCenterValue + 42000,
    fullRecordGapCenterValue + 42336,
    fullRecordGapCenterValue + 43008,
    fullRecordGapCenterValue + 43200,
    fullRecordGapCenterValue + 44000,
    fullRecordGapCenterValue + 44352,
    fullRecordGapCenterValue + 45056,
    fullRecordGapCenterValue + 45276,
    fullRecordGapCenterValue + 46200,
    fullRecordGapCenterValue + 47040,
    fullRecordGapCenterValue + 47250,
    fullRecordGapCenterValue + 47432,
    fullRecordGapCenterValue + 48510,
    fullRecordGapCenterValue + 49896,
    fullRecordGapCenterValue + 50688,
    fullRecordGapCenterValue + 50820,
    fullRecordGapCenterValue + 52272,
    fullRecordGapCenterValue + 52500,
    fullRecordGapCenterValue + 53240,
    fullRecordGapCenterValue + 53760,
    fullRecordGapCenterValue + 54000,
    fullRecordGapCenterValue + 54432,
    fullRecordGapCenterValue + 56700,
    fullRecordGapCenterValue + 57600,
    fullRecordGapCenterValue + 57750,
    fullRecordGapCenterValue + 58320,
    fullRecordGapCenterValue + 60000,
    fullRecordGapCenterValue + 60750,
    fullRecordGapCenterValue + 61236,
    fullRecordGapCenterValue + 61250,
    fullRecordGapCenterValue + 61440,
    fullRecordGapCenterValue + 63000,
    fullRecordGapCenterValue + 64800,
    fullRecordGapCenterValue + 65856,
    fullRecordGapCenterValue + 67760,
    fullRecordGapCenterValue + 68600,
    fullRecordGapCenterValue + 69696,
    fullRecordGapCenterValue + 72000,
    fullRecordGapCenterValue + 72030,
    fullRecordGapCenterValue + 72600,
    fullRecordGapCenterValue + 73920,
    fullRecordGapCenterValue + 75000,
    fullRecordGapCenterValue + 76230,
    fullRecordGapCenterValue + 76800,
    fullRecordGapCenterValue + 76832,
    fullRecordGapCenterValue + 77000,
    fullRecordGapCenterValue + 77760,
    fullRecordGapCenterValue + 79200,
    fullRecordGapCenterValue + 80190,
    fullRecordGapCenterValue + 80850,
    fullRecordGapCenterValue + 83006,
    fullRecordGapCenterValue + 83160,
    fullRecordGapCenterValue + 84000,
    fullRecordGapCenterValue + 85536,
    fullRecordGapCenterValue + 86378,
    fullRecordGapCenterValue + 86402,
    fullRecordGapCenterValue + 86436,
    fullRecordGapCenterValue + 86822,
    fullRecordGapCenterValue + 87146,
    fullRecordGapCenterValue + 87318,
    fullRecordGapCenterValue + 87480,
    fullRecordGapCenterValue + 87500,
    fullRecordGapCenterValue + 87518,
    fullRecordGapCenterValue + 87566,
    fullRecordGapCenterValue + 87602,
    fullRecordGapCenterValue + 87782,
    fullRecordGapCenterValue + 87866,
    fullRecordGapCenterValue + 87938,
    fullRecordGapCenterValue + 88058,
    fullRecordGapCenterValue + 88082,
    fullRecordGapCenterValue + 88142,
    fullRecordGapCenterValue + 88200,
    fullRecordGapCenterValue + 88358,
    fullRecordGapCenterValue + 88406,
    fullRecordGapCenterValue + 88538,
    fullRecordGapCenterValue + 88742,
    fullRecordGapCenterValue + 89066,
    fullRecordGapCenterValue + 89282,
    fullRecordGapCenterValue + 89678,
    fullRecordGapCenterValue + 89918,
    fullRecordGapCenterValue + 89966,
    fullRecordGapCenterValue + 90638,
    fullRecordGapCenterValue + 90720,
    fullRecordGapCenterValue + 90722,
    fullRecordGapCenterValue + 91046,
    fullRecordGapCenterValue + 91082,
    fullRecordGapCenterValue + 91106,
    fullRecordGapCenterValue + 91476,
    fullRecordGapCenterValue + 91502]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00016_fermat : ∀ n ∈ fullRecordGapRow00016_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03841_not_prime : ¬(recordGapCenter + 968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 968]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03842_not_prime : ¬(recordGapCenter + 990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 990]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03843_not_prime : ¬(recordGapCenter + 1050).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1050]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03844_not_prime : ¬(recordGapCenter + 1200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1200]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03845_not_prime : ¬(recordGapCenter + 1260).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1260]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03846_not_prime : ¬(recordGapCenter + 1320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1320]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03847_not_prime : ¬(recordGapCenter + 1386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1386]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03848_not_prime : ¬(recordGapCenter + 1452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1452]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03849_not_prime : ¬(recordGapCenter + 1500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03850_not_prime : ¬(recordGapCenter + 1620).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1620]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03851_not_prime : ¬(recordGapCenter + 1650).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1650]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03852_not_prime : ¬(recordGapCenter + 1680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1680]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03853_not_prime : ¬(recordGapCenter + 1782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1782]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03854_not_prime : ¬(recordGapCenter + 1848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 1848]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03855_not_prime : ¬(recordGapCenter + 2016).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2016]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03856_not_prime : ¬(recordGapCenter + 2048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2048]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03857_not_prime : ¬(recordGapCenter + 2058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2058]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03858_not_prime : ¬(recordGapCenter + 2100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2100]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03859_not_prime : ¬(recordGapCenter + 2112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2112]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03860_not_prime : ¬(recordGapCenter + 2156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2156]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03861_not_prime : ¬(recordGapCenter + 2160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2160]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03862_not_prime : ¬(recordGapCenter + 2178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2178]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03863_not_prime : ¬(recordGapCenter + 2352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2352]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03864_not_prime : ¬(recordGapCenter + 2376).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2376]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03865_not_prime : ¬(recordGapCenter + 2430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2430]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03866_not_prime : ¬(recordGapCenter + 2450).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2450]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03867_not_prime : ¬(recordGapCenter + 2640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2640]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03868_not_prime : ¬(recordGapCenter + 2646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2646]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03869_not_prime : ¬(recordGapCenter + 2772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2772]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03870_not_prime : ¬(recordGapCenter + 2816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2816]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03871_not_prime : ¬(recordGapCenter + 2916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2916]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03872_not_prime : ¬(recordGapCenter + 2940).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2940]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03873_not_prime : ¬(recordGapCenter + 2970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 2970]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03874_not_prime : ¬(recordGapCenter + 3168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3168]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03875_not_prime : ¬(recordGapCenter + 3200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3200]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03876_not_prime : ¬(recordGapCenter + 3360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3360]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03877_not_prime : ¬(recordGapCenter + 3402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3402]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03878_not_prime : ¬(recordGapCenter + 3456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3456]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03879_not_prime : ¬(recordGapCenter + 3500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03880_not_prime : ¬(recordGapCenter + 3630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3630]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03881_not_prime : ¬(recordGapCenter + 3696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3696]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03882_not_prime : ¬(recordGapCenter + 3750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3750]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03883_not_prime : ¬(recordGapCenter + 3872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3872]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03884_not_prime : ¬(recordGapCenter + 3920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3920]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03885_not_prime : ¬(recordGapCenter + 3960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 3960]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03886_not_prime : ¬(recordGapCenter + 4158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4158]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03887_not_prime : ¬(recordGapCenter + 4320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4320]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03888_not_prime : ¬(recordGapCenter + 4536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4536]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03889_not_prime : ¬(recordGapCenter + 4608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4608]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03890_not_prime : ¬(recordGapCenter + 4860).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4860]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03891_not_prime : ¬(recordGapCenter + 4928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4928]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03892_not_prime : ¬(recordGapCenter + 4950).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 4950]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03893_not_prime : ¬(recordGapCenter + 5000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03894_not_prime : ¬(recordGapCenter + 5120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5120]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03895_not_prime : ¬(recordGapCenter + 5280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5280]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03896_not_prime : ¬(recordGapCenter + 5292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5292]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03897_not_prime : ¬(recordGapCenter + 5346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5346]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03898_not_prime : ¬(recordGapCenter + 5390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5390]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03899_not_prime : ¬(recordGapCenter + 5670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5670]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03900_not_prime : ¬(recordGapCenter + 5808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5808]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03901_not_prime : ¬(recordGapCenter + 5832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5832]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03902_not_prime : ¬(recordGapCenter + 5880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 5880]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03903_not_prime : ¬(recordGapCenter + 6300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 6300]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03904_not_prime : ¬(recordGapCenter + 6336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 6336]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03905_not_prime : ¬(recordGapCenter + 6480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 6480]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03906_not_prime : ¬(recordGapCenter + 6720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 6720]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03907_not_prime : ¬(recordGapCenter + 7056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7056]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03908_not_prime : ¬(recordGapCenter + 7128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7128]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03909_not_prime : ¬(recordGapCenter + 7290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7290]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03910_not_prime : ¬(recordGapCenter + 7500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03911_not_prime : ¬(recordGapCenter + 7560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7560]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03912_not_prime : ¬(recordGapCenter + 7920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 7920]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03913_not_prime : ¬(recordGapCenter + 8192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 8192]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03914_not_prime : ¬(recordGapCenter + 8712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 8712]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03915_not_prime : ¬(recordGapCenter + 8748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 8748]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03916_not_prime : ¬(recordGapCenter + 8750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 8750]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03917_not_prime : ¬(recordGapCenter + 9000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03918_not_prime : ¬(recordGapCenter + 9216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9216]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03919_not_prime : ¬(recordGapCenter + 9240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9240]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03920_not_prime : ¬(recordGapCenter + 9408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9408]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03921_not_prime : ¬(recordGapCenter + 9600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9600]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03922_not_prime : ¬(recordGapCenter + 9702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9702]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03923_not_prime : ¬(recordGapCenter + 9900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 9900]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03924_not_prime : ¬(recordGapCenter + 10368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 10368]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03925_not_prime : ¬(recordGapCenter + 10692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 10692]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03926_not_prime : ¬(recordGapCenter + 10976).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 10976]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03927_not_prime : ¬(recordGapCenter + 12000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03928_not_prime : ¬(recordGapCenter + 12320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12320]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03929_not_prime : ¬(recordGapCenter + 12348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12348]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03930_not_prime : ¬(recordGapCenter + 12500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03931_not_prime : ¬(recordGapCenter + 12600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 12600]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03932_not_prime : ¬(recordGapCenter + 13230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 13230]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03933_not_prime : ¬(recordGapCenter + 13310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 13310]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03934_not_prime : ¬(recordGapCenter + 13440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 13440]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03935_not_prime : ¬(recordGapCenter + 13860).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 13860]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03936_not_prime : ¬(recordGapCenter + 14112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 14112]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03937_not_prime : ¬(recordGapCenter + 14336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 14336]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03938_not_prime : ¬(recordGapCenter + 14400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 14400]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03939_not_prime : ¬(recordGapCenter + 14850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 14850]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03940_not_prime : ¬(recordGapCenter + 15246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 15246]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03941_not_prime : ¬(recordGapCenter + 15750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 15750]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03942_not_prime : ¬(recordGapCenter + 16170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16170]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03943_not_prime : ¬(recordGapCenter + 16200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16200]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03944_not_prime : ¬(recordGapCenter + 16632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16632]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03945_not_prime : ¬(recordGapCenter + 16800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16800]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03946_not_prime : ¬(recordGapCenter + 16940).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 16940]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03947_not_prime : ¬(recordGapCenter + 17150).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17150]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03948_not_prime : ¬(recordGapCenter + 17280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17280]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03949_not_prime : ¬(recordGapCenter + 17496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17496]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03950_not_prime : ¬(recordGapCenter + 17600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17600]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03951_not_prime : ¬(recordGapCenter + 17820).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 17820]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03952_not_prime : ¬(recordGapCenter + 18000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 18000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03953_not_prime : ¬(recordGapCenter + 18480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 18480]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03954_not_prime : ¬(recordGapCenter + 18816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 18816]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03955_not_prime : ¬(recordGapCenter + 18900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 18900]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03956_not_prime : ¬(recordGapCenter + 19008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 19008]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03957_not_prime : ¬(recordGapCenter + 19440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 19440]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03958_not_prime : ¬(recordGapCenter + 19602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 19602]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03959_not_prime : ¬(recordGapCenter + 20480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 20480]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03960_not_prime : ¬(recordGapCenter + 20580).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 20580]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03961_not_prime : ¬(recordGapCenter + 20736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 20736]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03962_not_prime : ¬(recordGapCenter + 21168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 21168]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03963_not_prime : ¬(recordGapCenter + 21560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 21560]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03964_not_prime : ¬(recordGapCenter + 21780).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 21780]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03965_not_prime : ¬(recordGapCenter + 22176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 22176]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03966_not_prime : ¬(recordGapCenter + 22400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 22400]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03967_not_prime : ¬(recordGapCenter + 22500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 22500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03968_not_prime : ¬(recordGapCenter + 22680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 22680]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03969_not_prime : ¬(recordGapCenter + 23040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 23040]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03970_not_prime : ¬(recordGapCenter + 23328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 23328]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03971_not_prime : ¬(recordGapCenter + 24000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03972_not_prime : ¬(recordGapCenter + 24192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24192]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03973_not_prime : ¬(recordGapCenter + 24300).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24300]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03974_not_prime : ¬(recordGapCenter + 24500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03975_not_prime : ¬(recordGapCenter + 24696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24696]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03976_not_prime : ¬(recordGapCenter + 24750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24750]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03977_not_prime : ¬(recordGapCenter + 24948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 24948]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03978_not_prime : ¬(recordGapCenter + 25410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 25410]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03979_not_prime : ¬(recordGapCenter + 26250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 26250]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03980_not_prime : ¬(recordGapCenter + 26460).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 26460]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03981_not_prime : ¬(recordGapCenter + 27440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 27440]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03982_not_prime : ¬(recordGapCenter + 27648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 27648]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03983_not_prime : ¬(recordGapCenter + 27720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 27720]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03984_not_prime : ¬(recordGapCenter + 28800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 28800]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03985_not_prime : ¬(recordGapCenter + 29160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 29160]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03986_not_prime : ¬(recordGapCenter + 29568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 29568]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03987_not_prime : ¬(recordGapCenter + 30240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 30240]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03988_not_prime : ¬(recordGapCenter + 30720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 30720]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03989_not_prime : ¬(recordGapCenter + 30800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 30800]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03990_not_prime : ¬(recordGapCenter + 32076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 32076]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03991_not_prime : ¬(recordGapCenter + 32340).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 32340]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03992_not_prime : ¬(recordGapCenter + 32400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 32400]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03993_not_prime : ¬(recordGapCenter + 32670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 32670]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03994_not_prime : ¬(recordGapCenter + 33000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 33000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03995_not_prime : ¬(recordGapCenter + 33600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 33600]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03996_not_prime : ¬(recordGapCenter + 34020).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 34020]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03997_not_prime : ¬(recordGapCenter + 35000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 35000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03998_not_prime : ¬(recordGapCenter + 35640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 35640]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm03999_not_prime : ¬(recordGapCenter + 35840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 35840]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04000_not_prime : ¬(recordGapCenter + 37500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 37500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04001_not_prime : ¬(recordGapCenter + 37632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 37632]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04002_not_prime : ¬(recordGapCenter + 38400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 38400]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04003_not_prime : ¬(recordGapCenter + 38880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 38880]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04004_not_prime : ¬(recordGapCenter + 39600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 39600]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04005_not_prime : ¬(recordGapCenter + 39690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 39690]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04006_not_prime : ¬(recordGapCenter + 40656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 40656]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04007_not_prime : ¬(recordGapCenter + 41472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 41472]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04008_not_prime : ¬(recordGapCenter + 42000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 42000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04009_not_prime : ¬(recordGapCenter + 42336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 42336]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04010_not_prime : ¬(recordGapCenter + 43008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 43008]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04011_not_prime : ¬(recordGapCenter + 43200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 43200]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04012_not_prime : ¬(recordGapCenter + 44000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 44000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04013_not_prime : ¬(recordGapCenter + 44352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 44352]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04014_not_prime : ¬(recordGapCenter + 45056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 45056]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04015_not_prime : ¬(recordGapCenter + 45276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 45276]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04016_not_prime : ¬(recordGapCenter + 46200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 46200]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04017_not_prime : ¬(recordGapCenter + 47040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 47040]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04018_not_prime : ¬(recordGapCenter + 47250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 47250]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04019_not_prime : ¬(recordGapCenter + 47432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 47432]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04020_not_prime : ¬(recordGapCenter + 48510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 48510]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04021_not_prime : ¬(recordGapCenter + 49896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 49896]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04022_not_prime : ¬(recordGapCenter + 50688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 50688]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04023_not_prime : ¬(recordGapCenter + 50820).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 50820]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04024_not_prime : ¬(recordGapCenter + 52272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 52272]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04025_not_prime : ¬(recordGapCenter + 52500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 52500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04026_not_prime : ¬(recordGapCenter + 53240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 53240]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04027_not_prime : ¬(recordGapCenter + 53760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 53760]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04028_not_prime : ¬(recordGapCenter + 54000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 54000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04029_not_prime : ¬(recordGapCenter + 54432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 54432]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04030_not_prime : ¬(recordGapCenter + 56700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 56700]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04031_not_prime : ¬(recordGapCenter + 57600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 57600]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04032_not_prime : ¬(recordGapCenter + 57750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 57750]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04033_not_prime : ¬(recordGapCenter + 58320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 58320]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04034_not_prime : ¬(recordGapCenter + 60000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 60000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04035_not_prime : ¬(recordGapCenter + 60750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 60750]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04036_not_prime : ¬(recordGapCenter + 61236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 61236]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04037_not_prime : ¬(recordGapCenter + 61250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 61250]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04038_not_prime : ¬(recordGapCenter + 61440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 61440]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04039_not_prime : ¬(recordGapCenter + 63000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 63000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04040_not_prime : ¬(recordGapCenter + 64800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 64800]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04041_not_prime : ¬(recordGapCenter + 65856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 65856]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04042_not_prime : ¬(recordGapCenter + 67760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 67760]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04043_not_prime : ¬(recordGapCenter + 68600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 68600]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04044_not_prime : ¬(recordGapCenter + 69696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 69696]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04045_not_prime : ¬(recordGapCenter + 72000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 72000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04046_not_prime : ¬(recordGapCenter + 72030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 72030]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04047_not_prime : ¬(recordGapCenter + 72600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 72600]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04048_not_prime : ¬(recordGapCenter + 73920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 73920]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04049_not_prime : ¬(recordGapCenter + 75000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 75000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04050_not_prime : ¬(recordGapCenter + 76230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 76230]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04051_not_prime : ¬(recordGapCenter + 76800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 76800]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04052_not_prime : ¬(recordGapCenter + 76832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 76832]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04053_not_prime : ¬(recordGapCenter + 77000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 77000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04054_not_prime : ¬(recordGapCenter + 77760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 77760]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04055_not_prime : ¬(recordGapCenter + 79200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 79200]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04056_not_prime : ¬(recordGapCenter + 80190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 80190]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04057_not_prime : ¬(recordGapCenter + 80850).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 80850]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04058_not_prime : ¬(recordGapCenter + 83006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 83006]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04059_not_prime : ¬(recordGapCenter + 83160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 83160]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04060_not_prime : ¬(recordGapCenter + 84000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 84000]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04061_not_prime : ¬(recordGapCenter + 85536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 85536]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04062_not_prime : ¬(recordGapCenter + 86378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 86378]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04063_not_prime : ¬(recordGapCenter + 86402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 86402]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04064_not_prime : ¬(recordGapCenter + 86436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 86436]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04065_not_prime : ¬(recordGapCenter + 86822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 86822]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04066_not_prime : ¬(recordGapCenter + 87146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87146]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04067_not_prime : ¬(recordGapCenter + 87318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87318]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04068_not_prime : ¬(recordGapCenter + 87480).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87480]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04069_not_prime : ¬(recordGapCenter + 87500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87500]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04070_not_prime : ¬(recordGapCenter + 87518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87518]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04071_not_prime : ¬(recordGapCenter + 87566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87566]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04072_not_prime : ¬(recordGapCenter + 87602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87602]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04073_not_prime : ¬(recordGapCenter + 87782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87782]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04074_not_prime : ¬(recordGapCenter + 87866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87866]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04075_not_prime : ¬(recordGapCenter + 87938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 87938]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04076_not_prime : ¬(recordGapCenter + 88058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88058]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04077_not_prime : ¬(recordGapCenter + 88082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88082]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04078_not_prime : ¬(recordGapCenter + 88142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88142]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04079_not_prime : ¬(recordGapCenter + 88200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88200]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04080_not_prime : ¬(recordGapCenter + 88358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88358]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04081_not_prime : ¬(recordGapCenter + 88406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88406]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04082_not_prime : ¬(recordGapCenter + 88538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88538]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04083_not_prime : ¬(recordGapCenter + 88742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 88742]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04084_not_prime : ¬(recordGapCenter + 89066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89066]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04085_not_prime : ¬(recordGapCenter + 89282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89282]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04086_not_prime : ¬(recordGapCenter + 89678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89678]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04087_not_prime : ¬(recordGapCenter + 89918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89918]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04088_not_prime : ¬(recordGapCenter + 89966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 89966]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04089_not_prime : ¬(recordGapCenter + 90638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 90638]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04090_not_prime : ¬(recordGapCenter + 90720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 90720]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04091_not_prime : ¬(recordGapCenter + 90722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 90722]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04092_not_prime : ¬(recordGapCenter + 91046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91046]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04093_not_prime : ¬(recordGapCenter + 91082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91082]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04094_not_prime : ¬(recordGapCenter + 91106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91106]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04095_not_prime : ¬(recordGapCenter + 91476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91476]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

theorem fullRecordGapTerm04096_not_prime : ¬(recordGapCenter + 91502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91502]
  · apply fullRecordGapRow00016_fermat
    simp [fullRecordGapRow00016_values]

end PrimeFactorUnimodality
