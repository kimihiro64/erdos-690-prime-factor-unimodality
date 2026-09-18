import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00024_values : List Nat :=
  [fullRecordGapCenterValue - 338658,
    fullRecordGapCenterValue - 338614,
    fullRecordGapCenterValue - 338502,
    fullRecordGapCenterValue - 338482,
    fullRecordGapCenterValue - 338398,
    fullRecordGapCenterValue - 338362,
    fullRecordGapCenterValue - 338158,
    fullRecordGapCenterValue - 338134,
    fullRecordGapCenterValue - 338098,
    fullRecordGapCenterValue - 338014,
    fullRecordGapCenterValue - 337998,
    fullRecordGapCenterValue - 337920,
    fullRecordGapCenterValue - 337798,
    fullRecordGapCenterValue - 337774,
    fullRecordGapCenterValue - 337684,
    fullRecordGapCenterValue - 337602,
    fullRecordGapCenterValue - 337500,
    fullRecordGapCenterValue - 337438,
    fullRecordGapCenterValue - 337354,
    fullRecordGapCenterValue - 337252,
    fullRecordGapCenterValue - 337234,
    fullRecordGapCenterValue - 337228,
    fullRecordGapCenterValue - 337074,
    fullRecordGapCenterValue - 337054,
    fullRecordGapCenterValue - 336898,
    fullRecordGapCenterValue - 336892,
    fullRecordGapCenterValue - 336844,
    fullRecordGapCenterValue - 336798,
    fullRecordGapCenterValue - 336594,
    fullRecordGapCenterValue - 336508,
    fullRecordGapCenterValue - 336394,
    fullRecordGapCenterValue - 336268,
    fullRecordGapCenterValue - 336244,
    fullRecordGapCenterValue - 336178,
    fullRecordGapCenterValue - 335932,
    fullRecordGapCenterValue - 335802,
    fullRecordGapCenterValue - 335782,
    fullRecordGapCenterValue - 335758,
    fullRecordGapCenterValue - 335554,
    fullRecordGapCenterValue - 335494,
    fullRecordGapCenterValue - 335458,
    fullRecordGapCenterValue - 335382,
    fullRecordGapCenterValue - 335254,
    fullRecordGapCenterValue - 335194,
    fullRecordGapCenterValue - 335092,
    fullRecordGapCenterValue - 335058,
    fullRecordGapCenterValue - 335022,
    fullRecordGapCenterValue - 334974,
    fullRecordGapCenterValue - 334942,
    fullRecordGapCenterValue - 334914,
    fullRecordGapCenterValue - 334758,
    fullRecordGapCenterValue - 334612,
    fullRecordGapCenterValue - 334534,
    fullRecordGapCenterValue - 334522,
    fullRecordGapCenterValue - 334498,
    fullRecordGapCenterValue - 334302,
    fullRecordGapCenterValue - 334234,
    fullRecordGapCenterValue - 334182,
    fullRecordGapCenterValue - 334102,
    fullRecordGapCenterValue - 334078,
    fullRecordGapCenterValue - 334018,
    fullRecordGapCenterValue - 334002,
    fullRecordGapCenterValue - 333798,
    fullRecordGapCenterValue - 333742]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00024_fermat : ∀ n ∈ fullRecordGapRow00024_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01473_not_prime : ¬(recordGapCenter - 338658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338658]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01474_not_prime : ¬(recordGapCenter - 338614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338614]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01475_not_prime : ¬(recordGapCenter - 338502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338502]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01476_not_prime : ¬(recordGapCenter - 338482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338482]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01477_not_prime : ¬(recordGapCenter - 338398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338398]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01478_not_prime : ¬(recordGapCenter - 338362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338362]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01479_not_prime : ¬(recordGapCenter - 338158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338158]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01480_not_prime : ¬(recordGapCenter - 338134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338134]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01481_not_prime : ¬(recordGapCenter - 338098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338098]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01482_not_prime : ¬(recordGapCenter - 338014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 338014]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01483_not_prime : ¬(recordGapCenter - 337998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337998]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01484_not_prime : ¬(recordGapCenter - 337920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337920]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01485_not_prime : ¬(recordGapCenter - 337798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337798]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01486_not_prime : ¬(recordGapCenter - 337774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337774]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01487_not_prime : ¬(recordGapCenter - 337684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337684]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01488_not_prime : ¬(recordGapCenter - 337602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337602]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01489_not_prime : ¬(recordGapCenter - 337500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337500]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01490_not_prime : ¬(recordGapCenter - 337438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337438]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01491_not_prime : ¬(recordGapCenter - 337354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337354]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01492_not_prime : ¬(recordGapCenter - 337252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337252]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01493_not_prime : ¬(recordGapCenter - 337234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337234]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01494_not_prime : ¬(recordGapCenter - 337228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337228]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01495_not_prime : ¬(recordGapCenter - 337074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337074]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01496_not_prime : ¬(recordGapCenter - 337054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 337054]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01497_not_prime : ¬(recordGapCenter - 336898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336898]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01498_not_prime : ¬(recordGapCenter - 336892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336892]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01499_not_prime : ¬(recordGapCenter - 336844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336844]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01500_not_prime : ¬(recordGapCenter - 336798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336798]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01501_not_prime : ¬(recordGapCenter - 336594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336594]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01502_not_prime : ¬(recordGapCenter - 336508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336508]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01503_not_prime : ¬(recordGapCenter - 336394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336394]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01504_not_prime : ¬(recordGapCenter - 336268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336268]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01505_not_prime : ¬(recordGapCenter - 336244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336244]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01506_not_prime : ¬(recordGapCenter - 336178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 336178]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01507_not_prime : ¬(recordGapCenter - 335932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335932]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01508_not_prime : ¬(recordGapCenter - 335802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335802]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01509_not_prime : ¬(recordGapCenter - 335782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335782]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01510_not_prime : ¬(recordGapCenter - 335758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335758]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01511_not_prime : ¬(recordGapCenter - 335554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335554]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01512_not_prime : ¬(recordGapCenter - 335494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335494]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01513_not_prime : ¬(recordGapCenter - 335458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335458]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01514_not_prime : ¬(recordGapCenter - 335382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335382]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01515_not_prime : ¬(recordGapCenter - 335254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335254]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01516_not_prime : ¬(recordGapCenter - 335194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335194]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01517_not_prime : ¬(recordGapCenter - 335092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335092]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01518_not_prime : ¬(recordGapCenter - 335058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335058]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01519_not_prime : ¬(recordGapCenter - 335022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 335022]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01520_not_prime : ¬(recordGapCenter - 334974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334974]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01521_not_prime : ¬(recordGapCenter - 334942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334942]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01522_not_prime : ¬(recordGapCenter - 334914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334914]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01523_not_prime : ¬(recordGapCenter - 334758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334758]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01524_not_prime : ¬(recordGapCenter - 334612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334612]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01525_not_prime : ¬(recordGapCenter - 334534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334534]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01526_not_prime : ¬(recordGapCenter - 334522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334522]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01527_not_prime : ¬(recordGapCenter - 334498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334498]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01528_not_prime : ¬(recordGapCenter - 334302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334302]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01529_not_prime : ¬(recordGapCenter - 334234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334234]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01530_not_prime : ¬(recordGapCenter - 334182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334182]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01531_not_prime : ¬(recordGapCenter - 334102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334102]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01532_not_prime : ¬(recordGapCenter - 334078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334078]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01533_not_prime : ¬(recordGapCenter - 334018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334018]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01534_not_prime : ¬(recordGapCenter - 334002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 334002]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01535_not_prime : ¬(recordGapCenter - 333798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333798]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

theorem fullRecordGapTerm01536_not_prime : ¬(recordGapCenter - 333742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333742]
  · apply fullRecordGapRow00024_fermat
    simp [fullRecordGapRow00024_values]

end PrimeFactorUnimodality
