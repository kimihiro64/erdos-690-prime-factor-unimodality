import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00164_values : List Nat :=
  [fullRecordGapCenterValue + 629106,
    fullRecordGapCenterValue + 629192,
    fullRecordGapCenterValue + 629228,
    fullRecordGapCenterValue + 629246,
    fullRecordGapCenterValue + 629270,
    fullRecordGapCenterValue + 629282,
    fullRecordGapCenterValue + 629342,
    fullRecordGapCenterValue + 629346,
    fullRecordGapCenterValue + 629426,
    fullRecordGapCenterValue + 629436,
    fullRecordGapCenterValue + 629522,
    fullRecordGapCenterValue + 629528,
    fullRecordGapCenterValue + 629598,
    fullRecordGapCenterValue + 629708,
    fullRecordGapCenterValue + 629732,
    fullRecordGapCenterValue + 629826,
    fullRecordGapCenterValue + 629828,
    fullRecordGapCenterValue + 629868,
    fullRecordGapCenterValue + 629870,
    fullRecordGapCenterValue + 630138,
    fullRecordGapCenterValue + 630182,
    fullRecordGapCenterValue + 630248,
    fullRecordGapCenterValue + 630290,
    fullRecordGapCenterValue + 630492,
    fullRecordGapCenterValue + 630548,
    fullRecordGapCenterValue + 630668,
    fullRecordGapCenterValue + 630698,
    fullRecordGapCenterValue + 630716,
    fullRecordGapCenterValue + 630822,
    fullRecordGapCenterValue + 630842,
    fullRecordGapCenterValue + 630852,
    fullRecordGapCenterValue + 630858,
    fullRecordGapCenterValue + 630932,
    fullRecordGapCenterValue + 630948,
    fullRecordGapCenterValue + 631038,
    fullRecordGapCenterValue + 631076,
    fullRecordGapCenterValue + 631130,
    fullRecordGapCenterValue + 631172,
    fullRecordGapCenterValue + 631178,
    fullRecordGapCenterValue + 631208,
    fullRecordGapCenterValue + 631310,
    fullRecordGapCenterValue + 631362,
    fullRecordGapCenterValue + 631478,
    fullRecordGapCenterValue + 631508,
    fullRecordGapCenterValue + 631662,
    fullRecordGapCenterValue + 631668,
    fullRecordGapCenterValue + 631778,
    fullRecordGapCenterValue + 631832,
    fullRecordGapCenterValue + 632006,
    fullRecordGapCenterValue + 632046,
    fullRecordGapCenterValue + 632292,
    fullRecordGapCenterValue + 632486,
    fullRecordGapCenterValue + 632508,
    fullRecordGapCenterValue + 632532,
    fullRecordGapCenterValue + 632642,
    fullRecordGapCenterValue + 632846,
    fullRecordGapCenterValue + 632906,
    fullRecordGapCenterValue + 633102,
    fullRecordGapCenterValue + 633110,
    fullRecordGapCenterValue + 633242,
    fullRecordGapCenterValue + 633246,
    fullRecordGapCenterValue + 633272,
    fullRecordGapCenterValue + 633326,
    fullRecordGapCenterValue + 633458]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00164_fermat : ∀ n ∈ fullRecordGapRow00164_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10433_not_prime : ¬(recordGapCenter + 629106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629106]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10434_not_prime : ¬(recordGapCenter + 629192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629192]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10435_not_prime : ¬(recordGapCenter + 629228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629228]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10436_not_prime : ¬(recordGapCenter + 629246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629246]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10437_not_prime : ¬(recordGapCenter + 629270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629270]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10438_not_prime : ¬(recordGapCenter + 629282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629282]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10439_not_prime : ¬(recordGapCenter + 629342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629342]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10440_not_prime : ¬(recordGapCenter + 629346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629346]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10441_not_prime : ¬(recordGapCenter + 629426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629426]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10442_not_prime : ¬(recordGapCenter + 629436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629436]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10443_not_prime : ¬(recordGapCenter + 629522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629522]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10444_not_prime : ¬(recordGapCenter + 629528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629528]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10445_not_prime : ¬(recordGapCenter + 629598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629598]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10446_not_prime : ¬(recordGapCenter + 629708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629708]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10447_not_prime : ¬(recordGapCenter + 629732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629732]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10448_not_prime : ¬(recordGapCenter + 629826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629826]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10449_not_prime : ¬(recordGapCenter + 629828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629828]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10450_not_prime : ¬(recordGapCenter + 629868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629868]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10451_not_prime : ¬(recordGapCenter + 629870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 629870]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10452_not_prime : ¬(recordGapCenter + 630138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630138]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10453_not_prime : ¬(recordGapCenter + 630182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630182]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10454_not_prime : ¬(recordGapCenter + 630248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630248]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10455_not_prime : ¬(recordGapCenter + 630290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630290]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10456_not_prime : ¬(recordGapCenter + 630492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630492]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10457_not_prime : ¬(recordGapCenter + 630548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630548]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10458_not_prime : ¬(recordGapCenter + 630668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630668]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10459_not_prime : ¬(recordGapCenter + 630698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630698]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10460_not_prime : ¬(recordGapCenter + 630716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630716]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10461_not_prime : ¬(recordGapCenter + 630822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630822]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10462_not_prime : ¬(recordGapCenter + 630842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630842]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10463_not_prime : ¬(recordGapCenter + 630852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630852]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10464_not_prime : ¬(recordGapCenter + 630858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630858]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10465_not_prime : ¬(recordGapCenter + 630932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630932]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10466_not_prime : ¬(recordGapCenter + 630948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 630948]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10467_not_prime : ¬(recordGapCenter + 631038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631038]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10468_not_prime : ¬(recordGapCenter + 631076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631076]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10469_not_prime : ¬(recordGapCenter + 631130).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631130]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10470_not_prime : ¬(recordGapCenter + 631172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631172]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10471_not_prime : ¬(recordGapCenter + 631178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631178]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10472_not_prime : ¬(recordGapCenter + 631208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631208]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10473_not_prime : ¬(recordGapCenter + 631310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631310]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10474_not_prime : ¬(recordGapCenter + 631362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631362]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10475_not_prime : ¬(recordGapCenter + 631478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631478]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10476_not_prime : ¬(recordGapCenter + 631508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631508]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10477_not_prime : ¬(recordGapCenter + 631662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631662]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10478_not_prime : ¬(recordGapCenter + 631668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631668]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10479_not_prime : ¬(recordGapCenter + 631778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631778]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10480_not_prime : ¬(recordGapCenter + 631832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 631832]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10481_not_prime : ¬(recordGapCenter + 632006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632006]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10482_not_prime : ¬(recordGapCenter + 632046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632046]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10483_not_prime : ¬(recordGapCenter + 632292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632292]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10484_not_prime : ¬(recordGapCenter + 632486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632486]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10485_not_prime : ¬(recordGapCenter + 632508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632508]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10486_not_prime : ¬(recordGapCenter + 632532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632532]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10487_not_prime : ¬(recordGapCenter + 632642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632642]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10488_not_prime : ¬(recordGapCenter + 632846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632846]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10489_not_prime : ¬(recordGapCenter + 632906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 632906]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10490_not_prime : ¬(recordGapCenter + 633102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633102]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10491_not_prime : ¬(recordGapCenter + 633110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633110]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10492_not_prime : ¬(recordGapCenter + 633242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633242]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10493_not_prime : ¬(recordGapCenter + 633246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633246]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10494_not_prime : ¬(recordGapCenter + 633272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633272]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10495_not_prime : ¬(recordGapCenter + 633326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633326]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

theorem fullRecordGapTerm10496_not_prime : ¬(recordGapCenter + 633458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 633458]
  · apply fullRecordGapRow00164_fermat
    simp [fullRecordGapRow00164_values]

end PrimeFactorUnimodality
