import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00013_values : List Nat :=
  [fullRecordGapCenterValue - 393868,
    fullRecordGapCenterValue - 393774,
    fullRecordGapCenterValue - 393634,
    fullRecordGapCenterValue - 393594,
    fullRecordGapCenterValue - 393592,
    fullRecordGapCenterValue - 393544,
    fullRecordGapCenterValue - 393508,
    fullRecordGapCenterValue - 393454,
    fullRecordGapCenterValue - 393378,
    fullRecordGapCenterValue - 393322,
    fullRecordGapCenterValue - 393292,
    fullRecordGapCenterValue - 393258,
    fullRecordGapCenterValue - 393222,
    fullRecordGapCenterValue - 393004,
    fullRecordGapCenterValue - 392998,
    fullRecordGapCenterValue - 392908,
    fullRecordGapCenterValue - 392878,
    fullRecordGapCenterValue - 392872,
    fullRecordGapCenterValue - 392662,
    fullRecordGapCenterValue - 392622,
    fullRecordGapCenterValue - 392542,
    fullRecordGapCenterValue - 392362,
    fullRecordGapCenterValue - 392278,
    fullRecordGapCenterValue - 392188,
    fullRecordGapCenterValue - 392164,
    fullRecordGapCenterValue - 392068,
    fullRecordGapCenterValue - 391962,
    fullRecordGapCenterValue - 391954,
    fullRecordGapCenterValue - 391858,
    fullRecordGapCenterValue - 391738,
    fullRecordGapCenterValue - 391542,
    fullRecordGapCenterValue - 391444,
    fullRecordGapCenterValue - 391314,
    fullRecordGapCenterValue - 391278,
    fullRecordGapCenterValue - 391218,
    fullRecordGapCenterValue - 391198,
    fullRecordGapCenterValue - 391078,
    fullRecordGapCenterValue - 391038,
    fullRecordGapCenterValue - 391002,
    fullRecordGapCenterValue - 390882,
    fullRecordGapCenterValue - 390844,
    fullRecordGapCenterValue - 390802,
    fullRecordGapCenterValue - 390778,
    fullRecordGapCenterValue - 390774,
    fullRecordGapCenterValue - 390738,
    fullRecordGapCenterValue - 390682,
    fullRecordGapCenterValue - 390568,
    fullRecordGapCenterValue - 390378,
    fullRecordGapCenterValue - 390322,
    fullRecordGapCenterValue - 390154,
    fullRecordGapCenterValue - 390094,
    fullRecordGapCenterValue - 390088,
    fullRecordGapCenterValue - 389982,
    fullRecordGapCenterValue - 389814,
    fullRecordGapCenterValue - 389812,
    fullRecordGapCenterValue - 389622,
    fullRecordGapCenterValue - 389542,
    fullRecordGapCenterValue - 389434,
    fullRecordGapCenterValue - 389308,
    fullRecordGapCenterValue - 389274,
    fullRecordGapCenterValue - 389262,
    fullRecordGapCenterValue - 389218,
    fullRecordGapCenterValue - 389212,
    fullRecordGapCenterValue - 389182]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00013_fermat : ∀ n ∈ fullRecordGapRow00013_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00769_not_prime : ¬(recordGapCenter - 393868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393868]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00770_not_prime : ¬(recordGapCenter - 393774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393774]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00771_not_prime : ¬(recordGapCenter - 393634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393634]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00772_not_prime : ¬(recordGapCenter - 393594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393594]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00773_not_prime : ¬(recordGapCenter - 393592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393592]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00774_not_prime : ¬(recordGapCenter - 393544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393544]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00775_not_prime : ¬(recordGapCenter - 393508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393508]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00776_not_prime : ¬(recordGapCenter - 393454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393454]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00777_not_prime : ¬(recordGapCenter - 393378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393378]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00778_not_prime : ¬(recordGapCenter - 393322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393322]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00779_not_prime : ¬(recordGapCenter - 393292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393292]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00780_not_prime : ¬(recordGapCenter - 393258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393258]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00781_not_prime : ¬(recordGapCenter - 393222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393222]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00782_not_prime : ¬(recordGapCenter - 393004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393004]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00783_not_prime : ¬(recordGapCenter - 392998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392998]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00784_not_prime : ¬(recordGapCenter - 392908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392908]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00785_not_prime : ¬(recordGapCenter - 392878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392878]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00786_not_prime : ¬(recordGapCenter - 392872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392872]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00787_not_prime : ¬(recordGapCenter - 392662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392662]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00788_not_prime : ¬(recordGapCenter - 392622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392622]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00789_not_prime : ¬(recordGapCenter - 392542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392542]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00790_not_prime : ¬(recordGapCenter - 392362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392362]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00791_not_prime : ¬(recordGapCenter - 392278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392278]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00792_not_prime : ¬(recordGapCenter - 392188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392188]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00793_not_prime : ¬(recordGapCenter - 392164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392164]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00794_not_prime : ¬(recordGapCenter - 392068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 392068]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00795_not_prime : ¬(recordGapCenter - 391962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391962]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00796_not_prime : ¬(recordGapCenter - 391954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391954]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00797_not_prime : ¬(recordGapCenter - 391858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391858]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00798_not_prime : ¬(recordGapCenter - 391738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391738]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00799_not_prime : ¬(recordGapCenter - 391542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391542]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00800_not_prime : ¬(recordGapCenter - 391444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391444]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00801_not_prime : ¬(recordGapCenter - 391314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391314]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00802_not_prime : ¬(recordGapCenter - 391278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391278]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00803_not_prime : ¬(recordGapCenter - 391218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391218]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00804_not_prime : ¬(recordGapCenter - 391198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391198]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00805_not_prime : ¬(recordGapCenter - 391078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391078]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00806_not_prime : ¬(recordGapCenter - 391038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391038]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00807_not_prime : ¬(recordGapCenter - 391002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 391002]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00808_not_prime : ¬(recordGapCenter - 390882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390882]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00809_not_prime : ¬(recordGapCenter - 390844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390844]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00810_not_prime : ¬(recordGapCenter - 390802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390802]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00811_not_prime : ¬(recordGapCenter - 390778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390778]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00812_not_prime : ¬(recordGapCenter - 390774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390774]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00813_not_prime : ¬(recordGapCenter - 390738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390738]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00814_not_prime : ¬(recordGapCenter - 390682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390682]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00815_not_prime : ¬(recordGapCenter - 390568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390568]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00816_not_prime : ¬(recordGapCenter - 390378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390378]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00817_not_prime : ¬(recordGapCenter - 390322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390322]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00818_not_prime : ¬(recordGapCenter - 390154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390154]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00819_not_prime : ¬(recordGapCenter - 390094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390094]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00820_not_prime : ¬(recordGapCenter - 390088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 390088]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00821_not_prime : ¬(recordGapCenter - 389982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389982]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00822_not_prime : ¬(recordGapCenter - 389814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389814]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00823_not_prime : ¬(recordGapCenter - 389812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389812]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00824_not_prime : ¬(recordGapCenter - 389622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389622]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00825_not_prime : ¬(recordGapCenter - 389542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389542]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00826_not_prime : ¬(recordGapCenter - 389434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389434]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00827_not_prime : ¬(recordGapCenter - 389308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389308]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00828_not_prime : ¬(recordGapCenter - 389274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389274]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00829_not_prime : ¬(recordGapCenter - 389262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389262]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00830_not_prime : ¬(recordGapCenter - 389218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389218]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00831_not_prime : ¬(recordGapCenter - 389212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389212]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

theorem fullRecordGapTerm00832_not_prime : ¬(recordGapCenter - 389182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 389182]
  · apply fullRecordGapRow00013_fermat
    simp [fullRecordGapRow00013_values]

end PrimeFactorUnimodality
