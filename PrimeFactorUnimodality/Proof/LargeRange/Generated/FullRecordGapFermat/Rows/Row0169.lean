import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00169_values : List Nat :=
  [fullRecordGapCenterValue + 648638,
    fullRecordGapCenterValue + 648642,
    fullRecordGapCenterValue + 648722,
    fullRecordGapCenterValue + 648762,
    fullRecordGapCenterValue + 648786,
    fullRecordGapCenterValue + 648938,
    fullRecordGapCenterValue + 648966,
    fullRecordGapCenterValue + 649010,
    fullRecordGapCenterValue + 649028,
    fullRecordGapCenterValue + 649146,
    fullRecordGapCenterValue + 649218,
    fullRecordGapCenterValue + 649266,
    fullRecordGapCenterValue + 649302,
    fullRecordGapCenterValue + 649322,
    fullRecordGapCenterValue + 649346,
    fullRecordGapCenterValue + 649526,
    fullRecordGapCenterValue + 649556,
    fullRecordGapCenterValue + 649562,
    fullRecordGapCenterValue + 649596,
    fullRecordGapCenterValue + 649598,
    fullRecordGapCenterValue + 649626,
    fullRecordGapCenterValue + 649758,
    fullRecordGapCenterValue + 649778,
    fullRecordGapCenterValue + 649862,
    fullRecordGapCenterValue + 649982,
    fullRecordGapCenterValue + 650058,
    fullRecordGapCenterValue + 650108,
    fullRecordGapCenterValue + 650126,
    fullRecordGapCenterValue + 650258,
    fullRecordGapCenterValue + 650262,
    fullRecordGapCenterValue + 650330,
    fullRecordGapCenterValue + 650402,
    fullRecordGapCenterValue + 650406,
    fullRecordGapCenterValue + 650456,
    fullRecordGapCenterValue + 650478,
    fullRecordGapCenterValue + 650496,
    fullRecordGapCenterValue + 650526,
    fullRecordGapCenterValue + 650618,
    fullRecordGapCenterValue + 650678,
    fullRecordGapCenterValue + 650708,
    fullRecordGapCenterValue + 650732,
    fullRecordGapCenterValue + 650742,
    fullRecordGapCenterValue + 650766,
    fullRecordGapCenterValue + 650846,
    fullRecordGapCenterValue + 650906,
    fullRecordGapCenterValue + 650982,
    fullRecordGapCenterValue + 650990,
    fullRecordGapCenterValue + 650996,
    fullRecordGapCenterValue + 651018,
    fullRecordGapCenterValue + 651026,
    fullRecordGapCenterValue + 651110,
    fullRecordGapCenterValue + 651198,
    fullRecordGapCenterValue + 651368,
    fullRecordGapCenterValue + 651458,
    fullRecordGapCenterValue + 651470,
    fullRecordGapCenterValue + 651516,
    fullRecordGapCenterValue + 651522,
    fullRecordGapCenterValue + 651626,
    fullRecordGapCenterValue + 651656,
    fullRecordGapCenterValue + 651668,
    fullRecordGapCenterValue + 651698,
    fullRecordGapCenterValue + 651710,
    fullRecordGapCenterValue + 651722,
    fullRecordGapCenterValue + 651782]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00169_fermat : ∀ n ∈ fullRecordGapRow00169_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10753_not_prime : ¬(recordGapCenter + 648638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648638]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10754_not_prime : ¬(recordGapCenter + 648642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648642]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10755_not_prime : ¬(recordGapCenter + 648722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648722]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10756_not_prime : ¬(recordGapCenter + 648762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648762]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10757_not_prime : ¬(recordGapCenter + 648786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648786]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10758_not_prime : ¬(recordGapCenter + 648938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648938]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10759_not_prime : ¬(recordGapCenter + 648966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 648966]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10760_not_prime : ¬(recordGapCenter + 649010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649010]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10761_not_prime : ¬(recordGapCenter + 649028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649028]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10762_not_prime : ¬(recordGapCenter + 649146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649146]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10763_not_prime : ¬(recordGapCenter + 649218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649218]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10764_not_prime : ¬(recordGapCenter + 649266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649266]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10765_not_prime : ¬(recordGapCenter + 649302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649302]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10766_not_prime : ¬(recordGapCenter + 649322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649322]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10767_not_prime : ¬(recordGapCenter + 649346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649346]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10768_not_prime : ¬(recordGapCenter + 649526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649526]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10769_not_prime : ¬(recordGapCenter + 649556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649556]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10770_not_prime : ¬(recordGapCenter + 649562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649562]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10771_not_prime : ¬(recordGapCenter + 649596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649596]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10772_not_prime : ¬(recordGapCenter + 649598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649598]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10773_not_prime : ¬(recordGapCenter + 649626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649626]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10774_not_prime : ¬(recordGapCenter + 649758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649758]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10775_not_prime : ¬(recordGapCenter + 649778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649778]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10776_not_prime : ¬(recordGapCenter + 649862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649862]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10777_not_prime : ¬(recordGapCenter + 649982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 649982]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10778_not_prime : ¬(recordGapCenter + 650058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650058]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10779_not_prime : ¬(recordGapCenter + 650108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650108]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10780_not_prime : ¬(recordGapCenter + 650126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650126]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10781_not_prime : ¬(recordGapCenter + 650258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650258]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10782_not_prime : ¬(recordGapCenter + 650262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650262]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10783_not_prime : ¬(recordGapCenter + 650330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650330]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10784_not_prime : ¬(recordGapCenter + 650402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650402]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10785_not_prime : ¬(recordGapCenter + 650406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650406]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10786_not_prime : ¬(recordGapCenter + 650456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650456]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10787_not_prime : ¬(recordGapCenter + 650478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650478]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10788_not_prime : ¬(recordGapCenter + 650496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650496]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10789_not_prime : ¬(recordGapCenter + 650526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650526]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10790_not_prime : ¬(recordGapCenter + 650618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650618]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10791_not_prime : ¬(recordGapCenter + 650678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650678]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10792_not_prime : ¬(recordGapCenter + 650708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650708]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10793_not_prime : ¬(recordGapCenter + 650732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650732]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10794_not_prime : ¬(recordGapCenter + 650742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650742]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10795_not_prime : ¬(recordGapCenter + 650766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650766]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10796_not_prime : ¬(recordGapCenter + 650846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650846]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10797_not_prime : ¬(recordGapCenter + 650906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650906]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10798_not_prime : ¬(recordGapCenter + 650982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650982]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10799_not_prime : ¬(recordGapCenter + 650990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650990]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10800_not_prime : ¬(recordGapCenter + 650996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 650996]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10801_not_prime : ¬(recordGapCenter + 651018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651018]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10802_not_prime : ¬(recordGapCenter + 651026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651026]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10803_not_prime : ¬(recordGapCenter + 651110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651110]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10804_not_prime : ¬(recordGapCenter + 651198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651198]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10805_not_prime : ¬(recordGapCenter + 651368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651368]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10806_not_prime : ¬(recordGapCenter + 651458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651458]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10807_not_prime : ¬(recordGapCenter + 651470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651470]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10808_not_prime : ¬(recordGapCenter + 651516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651516]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10809_not_prime : ¬(recordGapCenter + 651522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651522]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10810_not_prime : ¬(recordGapCenter + 651626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651626]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10811_not_prime : ¬(recordGapCenter + 651656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651656]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10812_not_prime : ¬(recordGapCenter + 651668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651668]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10813_not_prime : ¬(recordGapCenter + 651698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651698]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10814_not_prime : ¬(recordGapCenter + 651710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651710]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10815_not_prime : ¬(recordGapCenter + 651722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651722]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

theorem fullRecordGapTerm10816_not_prime : ¬(recordGapCenter + 651782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651782]
  · apply fullRecordGapRow00169_fermat
    simp [fullRecordGapRow00169_values]

end PrimeFactorUnimodality
