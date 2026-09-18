import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue10753 : Nat := fullRecordGapCenterValue + 648638

theorem fullRecordGapTerm10753_eq_value :
    recordGapCenter + 648638 = fullRecordGapValue10753 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10753_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10753 (fullRecordGapValue10753 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10753_not_prime : ¬(recordGapCenter + 648638).Prime := by
  rw [fullRecordGapTerm10753_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10753, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10753_fast_pow_mod_ne_one

def fullRecordGapValue10754 : Nat := fullRecordGapCenterValue + 648642

theorem fullRecordGapTerm10754_eq_value :
    recordGapCenter + 648642 = fullRecordGapValue10754 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10754_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10754 (fullRecordGapValue10754 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10754_not_prime : ¬(recordGapCenter + 648642).Prime := by
  rw [fullRecordGapTerm10754_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10754, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10754_fast_pow_mod_ne_one

def fullRecordGapValue10755 : Nat := fullRecordGapCenterValue + 648722

theorem fullRecordGapTerm10755_eq_value :
    recordGapCenter + 648722 = fullRecordGapValue10755 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10755_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10755 (fullRecordGapValue10755 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10755_not_prime : ¬(recordGapCenter + 648722).Prime := by
  rw [fullRecordGapTerm10755_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10755, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10755_fast_pow_mod_ne_one

def fullRecordGapValue10756 : Nat := fullRecordGapCenterValue + 648762

theorem fullRecordGapTerm10756_eq_value :
    recordGapCenter + 648762 = fullRecordGapValue10756 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10756_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10756 (fullRecordGapValue10756 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10756_not_prime : ¬(recordGapCenter + 648762).Prime := by
  rw [fullRecordGapTerm10756_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10756, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10756_fast_pow_mod_ne_one

def fullRecordGapValue10757 : Nat := fullRecordGapCenterValue + 648786

theorem fullRecordGapTerm10757_eq_value :
    recordGapCenter + 648786 = fullRecordGapValue10757 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10757_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10757 (fullRecordGapValue10757 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10757_not_prime : ¬(recordGapCenter + 648786).Prime := by
  rw [fullRecordGapTerm10757_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10757, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10757_fast_pow_mod_ne_one

def fullRecordGapValue10758 : Nat := fullRecordGapCenterValue + 648938

theorem fullRecordGapTerm10758_eq_value :
    recordGapCenter + 648938 = fullRecordGapValue10758 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10758_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10758 (fullRecordGapValue10758 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10758_not_prime : ¬(recordGapCenter + 648938).Prime := by
  rw [fullRecordGapTerm10758_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10758, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10758_fast_pow_mod_ne_one

def fullRecordGapValue10759 : Nat := fullRecordGapCenterValue + 648966

theorem fullRecordGapTerm10759_eq_value :
    recordGapCenter + 648966 = fullRecordGapValue10759 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10759_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10759 (fullRecordGapValue10759 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10759_not_prime : ¬(recordGapCenter + 648966).Prime := by
  rw [fullRecordGapTerm10759_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10759, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10759_fast_pow_mod_ne_one

def fullRecordGapValue10760 : Nat := fullRecordGapCenterValue + 649010

theorem fullRecordGapTerm10760_eq_value :
    recordGapCenter + 649010 = fullRecordGapValue10760 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10760_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10760 (fullRecordGapValue10760 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10760_not_prime : ¬(recordGapCenter + 649010).Prime := by
  rw [fullRecordGapTerm10760_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10760, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10760_fast_pow_mod_ne_one

def fullRecordGapValue10761 : Nat := fullRecordGapCenterValue + 649028

theorem fullRecordGapTerm10761_eq_value :
    recordGapCenter + 649028 = fullRecordGapValue10761 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10761_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10761 (fullRecordGapValue10761 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10761_not_prime : ¬(recordGapCenter + 649028).Prime := by
  rw [fullRecordGapTerm10761_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10761, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10761_fast_pow_mod_ne_one

def fullRecordGapValue10762 : Nat := fullRecordGapCenterValue + 649146

theorem fullRecordGapTerm10762_eq_value :
    recordGapCenter + 649146 = fullRecordGapValue10762 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10762_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10762 (fullRecordGapValue10762 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10762_not_prime : ¬(recordGapCenter + 649146).Prime := by
  rw [fullRecordGapTerm10762_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10762, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10762_fast_pow_mod_ne_one

def fullRecordGapValue10763 : Nat := fullRecordGapCenterValue + 649218

theorem fullRecordGapTerm10763_eq_value :
    recordGapCenter + 649218 = fullRecordGapValue10763 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10763_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10763 (fullRecordGapValue10763 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10763_not_prime : ¬(recordGapCenter + 649218).Prime := by
  rw [fullRecordGapTerm10763_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10763, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10763_fast_pow_mod_ne_one

def fullRecordGapValue10764 : Nat := fullRecordGapCenterValue + 649266

theorem fullRecordGapTerm10764_eq_value :
    recordGapCenter + 649266 = fullRecordGapValue10764 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10764_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10764 (fullRecordGapValue10764 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10764_not_prime : ¬(recordGapCenter + 649266).Prime := by
  rw [fullRecordGapTerm10764_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10764, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10764_fast_pow_mod_ne_one

def fullRecordGapValue10765 : Nat := fullRecordGapCenterValue + 649302

theorem fullRecordGapTerm10765_eq_value :
    recordGapCenter + 649302 = fullRecordGapValue10765 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10765_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10765 (fullRecordGapValue10765 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10765_not_prime : ¬(recordGapCenter + 649302).Prime := by
  rw [fullRecordGapTerm10765_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10765, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10765_fast_pow_mod_ne_one

def fullRecordGapValue10766 : Nat := fullRecordGapCenterValue + 649322

theorem fullRecordGapTerm10766_eq_value :
    recordGapCenter + 649322 = fullRecordGapValue10766 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10766_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10766 (fullRecordGapValue10766 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10766_not_prime : ¬(recordGapCenter + 649322).Prime := by
  rw [fullRecordGapTerm10766_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10766, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10766_fast_pow_mod_ne_one

def fullRecordGapValue10767 : Nat := fullRecordGapCenterValue + 649346

theorem fullRecordGapTerm10767_eq_value :
    recordGapCenter + 649346 = fullRecordGapValue10767 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10767_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10767 (fullRecordGapValue10767 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10767_not_prime : ¬(recordGapCenter + 649346).Prime := by
  rw [fullRecordGapTerm10767_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10767, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10767_fast_pow_mod_ne_one

def fullRecordGapValue10768 : Nat := fullRecordGapCenterValue + 649526

theorem fullRecordGapTerm10768_eq_value :
    recordGapCenter + 649526 = fullRecordGapValue10768 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10768_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10768 (fullRecordGapValue10768 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10768_not_prime : ¬(recordGapCenter + 649526).Prime := by
  rw [fullRecordGapTerm10768_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10768, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10768_fast_pow_mod_ne_one

def fullRecordGapValue10769 : Nat := fullRecordGapCenterValue + 649556

theorem fullRecordGapTerm10769_eq_value :
    recordGapCenter + 649556 = fullRecordGapValue10769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10769 (fullRecordGapValue10769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10769_not_prime : ¬(recordGapCenter + 649556).Prime := by
  rw [fullRecordGapTerm10769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10769_fast_pow_mod_ne_one

def fullRecordGapValue10770 : Nat := fullRecordGapCenterValue + 649562

theorem fullRecordGapTerm10770_eq_value :
    recordGapCenter + 649562 = fullRecordGapValue10770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10770 (fullRecordGapValue10770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10770_not_prime : ¬(recordGapCenter + 649562).Prime := by
  rw [fullRecordGapTerm10770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10770_fast_pow_mod_ne_one

def fullRecordGapValue10771 : Nat := fullRecordGapCenterValue + 649596

theorem fullRecordGapTerm10771_eq_value :
    recordGapCenter + 649596 = fullRecordGapValue10771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10771 (fullRecordGapValue10771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10771_not_prime : ¬(recordGapCenter + 649596).Prime := by
  rw [fullRecordGapTerm10771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10771_fast_pow_mod_ne_one

def fullRecordGapValue10772 : Nat := fullRecordGapCenterValue + 649598

theorem fullRecordGapTerm10772_eq_value :
    recordGapCenter + 649598 = fullRecordGapValue10772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10772 (fullRecordGapValue10772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10772_not_prime : ¬(recordGapCenter + 649598).Prime := by
  rw [fullRecordGapTerm10772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10772_fast_pow_mod_ne_one

def fullRecordGapValue10773 : Nat := fullRecordGapCenterValue + 649626

theorem fullRecordGapTerm10773_eq_value :
    recordGapCenter + 649626 = fullRecordGapValue10773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10773 (fullRecordGapValue10773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10773_not_prime : ¬(recordGapCenter + 649626).Prime := by
  rw [fullRecordGapTerm10773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10773_fast_pow_mod_ne_one

def fullRecordGapValue10774 : Nat := fullRecordGapCenterValue + 649758

theorem fullRecordGapTerm10774_eq_value :
    recordGapCenter + 649758 = fullRecordGapValue10774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10774 (fullRecordGapValue10774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10774_not_prime : ¬(recordGapCenter + 649758).Prime := by
  rw [fullRecordGapTerm10774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10774_fast_pow_mod_ne_one

def fullRecordGapValue10775 : Nat := fullRecordGapCenterValue + 649778

theorem fullRecordGapTerm10775_eq_value :
    recordGapCenter + 649778 = fullRecordGapValue10775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10775 (fullRecordGapValue10775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10775_not_prime : ¬(recordGapCenter + 649778).Prime := by
  rw [fullRecordGapTerm10775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10775_fast_pow_mod_ne_one

def fullRecordGapValue10776 : Nat := fullRecordGapCenterValue + 649862

theorem fullRecordGapTerm10776_eq_value :
    recordGapCenter + 649862 = fullRecordGapValue10776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10776 (fullRecordGapValue10776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10776_not_prime : ¬(recordGapCenter + 649862).Prime := by
  rw [fullRecordGapTerm10776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10776_fast_pow_mod_ne_one

def fullRecordGapValue10777 : Nat := fullRecordGapCenterValue + 649982

theorem fullRecordGapTerm10777_eq_value :
    recordGapCenter + 649982 = fullRecordGapValue10777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10777 (fullRecordGapValue10777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10777_not_prime : ¬(recordGapCenter + 649982).Prime := by
  rw [fullRecordGapTerm10777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10777_fast_pow_mod_ne_one

def fullRecordGapValue10778 : Nat := fullRecordGapCenterValue + 650058

theorem fullRecordGapTerm10778_eq_value :
    recordGapCenter + 650058 = fullRecordGapValue10778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10778 (fullRecordGapValue10778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10778_not_prime : ¬(recordGapCenter + 650058).Prime := by
  rw [fullRecordGapTerm10778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10778_fast_pow_mod_ne_one

def fullRecordGapValue10779 : Nat := fullRecordGapCenterValue + 650108

theorem fullRecordGapTerm10779_eq_value :
    recordGapCenter + 650108 = fullRecordGapValue10779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10779 (fullRecordGapValue10779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10779_not_prime : ¬(recordGapCenter + 650108).Prime := by
  rw [fullRecordGapTerm10779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10779_fast_pow_mod_ne_one

def fullRecordGapValue10780 : Nat := fullRecordGapCenterValue + 650126

theorem fullRecordGapTerm10780_eq_value :
    recordGapCenter + 650126 = fullRecordGapValue10780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10780 (fullRecordGapValue10780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10780_not_prime : ¬(recordGapCenter + 650126).Prime := by
  rw [fullRecordGapTerm10780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10780_fast_pow_mod_ne_one

def fullRecordGapValue10781 : Nat := fullRecordGapCenterValue + 650258

theorem fullRecordGapTerm10781_eq_value :
    recordGapCenter + 650258 = fullRecordGapValue10781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10781 (fullRecordGapValue10781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10781_not_prime : ¬(recordGapCenter + 650258).Prime := by
  rw [fullRecordGapTerm10781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10781_fast_pow_mod_ne_one

def fullRecordGapValue10782 : Nat := fullRecordGapCenterValue + 650262

theorem fullRecordGapTerm10782_eq_value :
    recordGapCenter + 650262 = fullRecordGapValue10782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10782 (fullRecordGapValue10782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10782_not_prime : ¬(recordGapCenter + 650262).Prime := by
  rw [fullRecordGapTerm10782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10782_fast_pow_mod_ne_one

def fullRecordGapValue10783 : Nat := fullRecordGapCenterValue + 650330

theorem fullRecordGapTerm10783_eq_value :
    recordGapCenter + 650330 = fullRecordGapValue10783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10783 (fullRecordGapValue10783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10783_not_prime : ¬(recordGapCenter + 650330).Prime := by
  rw [fullRecordGapTerm10783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10783_fast_pow_mod_ne_one

def fullRecordGapValue10784 : Nat := fullRecordGapCenterValue + 650402

theorem fullRecordGapTerm10784_eq_value :
    recordGapCenter + 650402 = fullRecordGapValue10784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10784 (fullRecordGapValue10784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10784_not_prime : ¬(recordGapCenter + 650402).Prime := by
  rw [fullRecordGapTerm10784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10784_fast_pow_mod_ne_one

def fullRecordGapValue10785 : Nat := fullRecordGapCenterValue + 650406

theorem fullRecordGapTerm10785_eq_value :
    recordGapCenter + 650406 = fullRecordGapValue10785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10785 (fullRecordGapValue10785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10785_not_prime : ¬(recordGapCenter + 650406).Prime := by
  rw [fullRecordGapTerm10785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10785_fast_pow_mod_ne_one

def fullRecordGapValue10786 : Nat := fullRecordGapCenterValue + 650456

theorem fullRecordGapTerm10786_eq_value :
    recordGapCenter + 650456 = fullRecordGapValue10786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10786 (fullRecordGapValue10786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10786_not_prime : ¬(recordGapCenter + 650456).Prime := by
  rw [fullRecordGapTerm10786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10786_fast_pow_mod_ne_one

def fullRecordGapValue10787 : Nat := fullRecordGapCenterValue + 650478

theorem fullRecordGapTerm10787_eq_value :
    recordGapCenter + 650478 = fullRecordGapValue10787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10787 (fullRecordGapValue10787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10787_not_prime : ¬(recordGapCenter + 650478).Prime := by
  rw [fullRecordGapTerm10787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10787_fast_pow_mod_ne_one

def fullRecordGapValue10788 : Nat := fullRecordGapCenterValue + 650496

theorem fullRecordGapTerm10788_eq_value :
    recordGapCenter + 650496 = fullRecordGapValue10788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10788 (fullRecordGapValue10788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10788_not_prime : ¬(recordGapCenter + 650496).Prime := by
  rw [fullRecordGapTerm10788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10788_fast_pow_mod_ne_one

def fullRecordGapValue10789 : Nat := fullRecordGapCenterValue + 650526

theorem fullRecordGapTerm10789_eq_value :
    recordGapCenter + 650526 = fullRecordGapValue10789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10789 (fullRecordGapValue10789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10789_not_prime : ¬(recordGapCenter + 650526).Prime := by
  rw [fullRecordGapTerm10789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10789_fast_pow_mod_ne_one

def fullRecordGapValue10790 : Nat := fullRecordGapCenterValue + 650618

theorem fullRecordGapTerm10790_eq_value :
    recordGapCenter + 650618 = fullRecordGapValue10790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10790 (fullRecordGapValue10790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10790_not_prime : ¬(recordGapCenter + 650618).Prime := by
  rw [fullRecordGapTerm10790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10790_fast_pow_mod_ne_one

def fullRecordGapValue10791 : Nat := fullRecordGapCenterValue + 650678

theorem fullRecordGapTerm10791_eq_value :
    recordGapCenter + 650678 = fullRecordGapValue10791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10791 (fullRecordGapValue10791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10791_not_prime : ¬(recordGapCenter + 650678).Prime := by
  rw [fullRecordGapTerm10791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10791_fast_pow_mod_ne_one

def fullRecordGapValue10792 : Nat := fullRecordGapCenterValue + 650708

theorem fullRecordGapTerm10792_eq_value :
    recordGapCenter + 650708 = fullRecordGapValue10792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10792 (fullRecordGapValue10792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10792_not_prime : ¬(recordGapCenter + 650708).Prime := by
  rw [fullRecordGapTerm10792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10792_fast_pow_mod_ne_one

def fullRecordGapValue10793 : Nat := fullRecordGapCenterValue + 650732

theorem fullRecordGapTerm10793_eq_value :
    recordGapCenter + 650732 = fullRecordGapValue10793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10793 (fullRecordGapValue10793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10793_not_prime : ¬(recordGapCenter + 650732).Prime := by
  rw [fullRecordGapTerm10793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10793_fast_pow_mod_ne_one

def fullRecordGapValue10794 : Nat := fullRecordGapCenterValue + 650742

theorem fullRecordGapTerm10794_eq_value :
    recordGapCenter + 650742 = fullRecordGapValue10794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10794 (fullRecordGapValue10794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10794_not_prime : ¬(recordGapCenter + 650742).Prime := by
  rw [fullRecordGapTerm10794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10794_fast_pow_mod_ne_one

def fullRecordGapValue10795 : Nat := fullRecordGapCenterValue + 650766

theorem fullRecordGapTerm10795_eq_value :
    recordGapCenter + 650766 = fullRecordGapValue10795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10795 (fullRecordGapValue10795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10795_not_prime : ¬(recordGapCenter + 650766).Prime := by
  rw [fullRecordGapTerm10795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10795_fast_pow_mod_ne_one

def fullRecordGapValue10796 : Nat := fullRecordGapCenterValue + 650846

theorem fullRecordGapTerm10796_eq_value :
    recordGapCenter + 650846 = fullRecordGapValue10796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10796 (fullRecordGapValue10796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10796_not_prime : ¬(recordGapCenter + 650846).Prime := by
  rw [fullRecordGapTerm10796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10796_fast_pow_mod_ne_one

def fullRecordGapValue10797 : Nat := fullRecordGapCenterValue + 650906

theorem fullRecordGapTerm10797_eq_value :
    recordGapCenter + 650906 = fullRecordGapValue10797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10797 (fullRecordGapValue10797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10797_not_prime : ¬(recordGapCenter + 650906).Prime := by
  rw [fullRecordGapTerm10797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10797_fast_pow_mod_ne_one

def fullRecordGapValue10798 : Nat := fullRecordGapCenterValue + 650982

theorem fullRecordGapTerm10798_eq_value :
    recordGapCenter + 650982 = fullRecordGapValue10798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10798 (fullRecordGapValue10798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10798_not_prime : ¬(recordGapCenter + 650982).Prime := by
  rw [fullRecordGapTerm10798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10798_fast_pow_mod_ne_one

def fullRecordGapValue10799 : Nat := fullRecordGapCenterValue + 650990

theorem fullRecordGapTerm10799_eq_value :
    recordGapCenter + 650990 = fullRecordGapValue10799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10799 (fullRecordGapValue10799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10799_not_prime : ¬(recordGapCenter + 650990).Prime := by
  rw [fullRecordGapTerm10799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10799_fast_pow_mod_ne_one

def fullRecordGapValue10800 : Nat := fullRecordGapCenterValue + 650996

theorem fullRecordGapTerm10800_eq_value :
    recordGapCenter + 650996 = fullRecordGapValue10800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10800 (fullRecordGapValue10800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10800_not_prime : ¬(recordGapCenter + 650996).Prime := by
  rw [fullRecordGapTerm10800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10800_fast_pow_mod_ne_one

def fullRecordGapValue10801 : Nat := fullRecordGapCenterValue + 651018

theorem fullRecordGapTerm10801_eq_value :
    recordGapCenter + 651018 = fullRecordGapValue10801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10801 (fullRecordGapValue10801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10801_not_prime : ¬(recordGapCenter + 651018).Prime := by
  rw [fullRecordGapTerm10801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10801_fast_pow_mod_ne_one

def fullRecordGapValue10802 : Nat := fullRecordGapCenterValue + 651026

theorem fullRecordGapTerm10802_eq_value :
    recordGapCenter + 651026 = fullRecordGapValue10802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10802 (fullRecordGapValue10802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10802_not_prime : ¬(recordGapCenter + 651026).Prime := by
  rw [fullRecordGapTerm10802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10802_fast_pow_mod_ne_one

def fullRecordGapValue10803 : Nat := fullRecordGapCenterValue + 651110

theorem fullRecordGapTerm10803_eq_value :
    recordGapCenter + 651110 = fullRecordGapValue10803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10803 (fullRecordGapValue10803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10803_not_prime : ¬(recordGapCenter + 651110).Prime := by
  rw [fullRecordGapTerm10803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10803_fast_pow_mod_ne_one

def fullRecordGapValue10804 : Nat := fullRecordGapCenterValue + 651198

theorem fullRecordGapTerm10804_eq_value :
    recordGapCenter + 651198 = fullRecordGapValue10804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10804 (fullRecordGapValue10804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10804_not_prime : ¬(recordGapCenter + 651198).Prime := by
  rw [fullRecordGapTerm10804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10804_fast_pow_mod_ne_one

def fullRecordGapValue10805 : Nat := fullRecordGapCenterValue + 651368

theorem fullRecordGapTerm10805_eq_value :
    recordGapCenter + 651368 = fullRecordGapValue10805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10805 (fullRecordGapValue10805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10805_not_prime : ¬(recordGapCenter + 651368).Prime := by
  rw [fullRecordGapTerm10805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10805_fast_pow_mod_ne_one

def fullRecordGapValue10806 : Nat := fullRecordGapCenterValue + 651458

theorem fullRecordGapTerm10806_eq_value :
    recordGapCenter + 651458 = fullRecordGapValue10806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10806 (fullRecordGapValue10806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10806_not_prime : ¬(recordGapCenter + 651458).Prime := by
  rw [fullRecordGapTerm10806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10806_fast_pow_mod_ne_one

def fullRecordGapValue10807 : Nat := fullRecordGapCenterValue + 651470

theorem fullRecordGapTerm10807_eq_value :
    recordGapCenter + 651470 = fullRecordGapValue10807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10807 (fullRecordGapValue10807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10807_not_prime : ¬(recordGapCenter + 651470).Prime := by
  rw [fullRecordGapTerm10807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10807_fast_pow_mod_ne_one

def fullRecordGapValue10808 : Nat := fullRecordGapCenterValue + 651516

theorem fullRecordGapTerm10808_eq_value :
    recordGapCenter + 651516 = fullRecordGapValue10808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10808 (fullRecordGapValue10808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10808_not_prime : ¬(recordGapCenter + 651516).Prime := by
  rw [fullRecordGapTerm10808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10808_fast_pow_mod_ne_one

def fullRecordGapValue10809 : Nat := fullRecordGapCenterValue + 651522

theorem fullRecordGapTerm10809_eq_value :
    recordGapCenter + 651522 = fullRecordGapValue10809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10809 (fullRecordGapValue10809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10809_not_prime : ¬(recordGapCenter + 651522).Prime := by
  rw [fullRecordGapTerm10809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10809_fast_pow_mod_ne_one

def fullRecordGapValue10810 : Nat := fullRecordGapCenterValue + 651626

theorem fullRecordGapTerm10810_eq_value :
    recordGapCenter + 651626 = fullRecordGapValue10810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10810 (fullRecordGapValue10810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10810_not_prime : ¬(recordGapCenter + 651626).Prime := by
  rw [fullRecordGapTerm10810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10810_fast_pow_mod_ne_one

def fullRecordGapValue10811 : Nat := fullRecordGapCenterValue + 651656

theorem fullRecordGapTerm10811_eq_value :
    recordGapCenter + 651656 = fullRecordGapValue10811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10811 (fullRecordGapValue10811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10811_not_prime : ¬(recordGapCenter + 651656).Prime := by
  rw [fullRecordGapTerm10811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10811_fast_pow_mod_ne_one

def fullRecordGapValue10812 : Nat := fullRecordGapCenterValue + 651668

theorem fullRecordGapTerm10812_eq_value :
    recordGapCenter + 651668 = fullRecordGapValue10812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10812 (fullRecordGapValue10812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10812_not_prime : ¬(recordGapCenter + 651668).Prime := by
  rw [fullRecordGapTerm10812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10812_fast_pow_mod_ne_one

def fullRecordGapValue10813 : Nat := fullRecordGapCenterValue + 651698

theorem fullRecordGapTerm10813_eq_value :
    recordGapCenter + 651698 = fullRecordGapValue10813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10813 (fullRecordGapValue10813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10813_not_prime : ¬(recordGapCenter + 651698).Prime := by
  rw [fullRecordGapTerm10813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10813_fast_pow_mod_ne_one

def fullRecordGapValue10814 : Nat := fullRecordGapCenterValue + 651710

theorem fullRecordGapTerm10814_eq_value :
    recordGapCenter + 651710 = fullRecordGapValue10814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10814 (fullRecordGapValue10814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10814_not_prime : ¬(recordGapCenter + 651710).Prime := by
  rw [fullRecordGapTerm10814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10814_fast_pow_mod_ne_one

def fullRecordGapValue10815 : Nat := fullRecordGapCenterValue + 651722

theorem fullRecordGapTerm10815_eq_value :
    recordGapCenter + 651722 = fullRecordGapValue10815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10815 (fullRecordGapValue10815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10815_not_prime : ¬(recordGapCenter + 651722).Prime := by
  rw [fullRecordGapTerm10815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10815_fast_pow_mod_ne_one

def fullRecordGapValue10816 : Nat := fullRecordGapCenterValue + 651782

theorem fullRecordGapTerm10816_eq_value :
    recordGapCenter + 651782 = fullRecordGapValue10816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10816 (fullRecordGapValue10816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10816_not_prime : ¬(recordGapCenter + 651782).Prime := by
  rw [fullRecordGapTerm10816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10816_fast_pow_mod_ne_one

def fullRecordGapValue10817 : Nat := fullRecordGapCenterValue + 651786

theorem fullRecordGapTerm10817_eq_value :
    recordGapCenter + 651786 = fullRecordGapValue10817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10817 (fullRecordGapValue10817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10817_not_prime : ¬(recordGapCenter + 651786).Prime := by
  rw [fullRecordGapTerm10817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10817_fast_pow_mod_ne_one

def fullRecordGapValue10818 : Nat := fullRecordGapCenterValue + 651788

theorem fullRecordGapTerm10818_eq_value :
    recordGapCenter + 651788 = fullRecordGapValue10818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10818 (fullRecordGapValue10818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10818_not_prime : ¬(recordGapCenter + 651788).Prime := by
  rw [fullRecordGapTerm10818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10818_fast_pow_mod_ne_one

def fullRecordGapValue10819 : Nat := fullRecordGapCenterValue + 651842

theorem fullRecordGapTerm10819_eq_value :
    recordGapCenter + 651842 = fullRecordGapValue10819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10819 (fullRecordGapValue10819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10819_not_prime : ¬(recordGapCenter + 651842).Prime := by
  rw [fullRecordGapTerm10819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10819_fast_pow_mod_ne_one

def fullRecordGapValue10820 : Nat := fullRecordGapCenterValue + 651876

theorem fullRecordGapTerm10820_eq_value :
    recordGapCenter + 651876 = fullRecordGapValue10820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10820 (fullRecordGapValue10820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10820_not_prime : ¬(recordGapCenter + 651876).Prime := by
  rw [fullRecordGapTerm10820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10820_fast_pow_mod_ne_one

def fullRecordGapValue10821 : Nat := fullRecordGapCenterValue + 651956

theorem fullRecordGapTerm10821_eq_value :
    recordGapCenter + 651956 = fullRecordGapValue10821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10821 (fullRecordGapValue10821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10821_not_prime : ¬(recordGapCenter + 651956).Prime := by
  rw [fullRecordGapTerm10821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10821_fast_pow_mod_ne_one

def fullRecordGapValue10822 : Nat := fullRecordGapCenterValue + 651998

theorem fullRecordGapTerm10822_eq_value :
    recordGapCenter + 651998 = fullRecordGapValue10822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10822 (fullRecordGapValue10822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10822_not_prime : ¬(recordGapCenter + 651998).Prime := by
  rw [fullRecordGapTerm10822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10822_fast_pow_mod_ne_one

def fullRecordGapValue10823 : Nat := fullRecordGapCenterValue + 652022

theorem fullRecordGapTerm10823_eq_value :
    recordGapCenter + 652022 = fullRecordGapValue10823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10823 (fullRecordGapValue10823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10823_not_prime : ¬(recordGapCenter + 652022).Prime := by
  rw [fullRecordGapTerm10823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10823_fast_pow_mod_ne_one

def fullRecordGapValue10824 : Nat := fullRecordGapCenterValue + 652046

theorem fullRecordGapTerm10824_eq_value :
    recordGapCenter + 652046 = fullRecordGapValue10824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10824 (fullRecordGapValue10824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10824_not_prime : ¬(recordGapCenter + 652046).Prime := by
  rw [fullRecordGapTerm10824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10824_fast_pow_mod_ne_one

def fullRecordGapValue10825 : Nat := fullRecordGapCenterValue + 652166

theorem fullRecordGapTerm10825_eq_value :
    recordGapCenter + 652166 = fullRecordGapValue10825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10825 (fullRecordGapValue10825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10825_not_prime : ¬(recordGapCenter + 652166).Prime := by
  rw [fullRecordGapTerm10825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10825_fast_pow_mod_ne_one

def fullRecordGapValue10826 : Nat := fullRecordGapCenterValue + 652190

theorem fullRecordGapTerm10826_eq_value :
    recordGapCenter + 652190 = fullRecordGapValue10826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10826 (fullRecordGapValue10826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10826_not_prime : ¬(recordGapCenter + 652190).Prime := by
  rw [fullRecordGapTerm10826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10826_fast_pow_mod_ne_one

def fullRecordGapValue10827 : Nat := fullRecordGapCenterValue + 652226

theorem fullRecordGapTerm10827_eq_value :
    recordGapCenter + 652226 = fullRecordGapValue10827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10827 (fullRecordGapValue10827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10827_not_prime : ¬(recordGapCenter + 652226).Prime := by
  rw [fullRecordGapTerm10827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10827_fast_pow_mod_ne_one

def fullRecordGapValue10828 : Nat := fullRecordGapCenterValue + 652332

theorem fullRecordGapTerm10828_eq_value :
    recordGapCenter + 652332 = fullRecordGapValue10828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10828 (fullRecordGapValue10828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10828_not_prime : ¬(recordGapCenter + 652332).Prime := by
  rw [fullRecordGapTerm10828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10828_fast_pow_mod_ne_one

def fullRecordGapValue10829 : Nat := fullRecordGapCenterValue + 652436

theorem fullRecordGapTerm10829_eq_value :
    recordGapCenter + 652436 = fullRecordGapValue10829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10829 (fullRecordGapValue10829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10829_not_prime : ¬(recordGapCenter + 652436).Prime := by
  rw [fullRecordGapTerm10829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10829_fast_pow_mod_ne_one

def fullRecordGapValue10830 : Nat := fullRecordGapCenterValue + 652452

theorem fullRecordGapTerm10830_eq_value :
    recordGapCenter + 652452 = fullRecordGapValue10830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10830 (fullRecordGapValue10830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10830_not_prime : ¬(recordGapCenter + 652452).Prime := by
  rw [fullRecordGapTerm10830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10830_fast_pow_mod_ne_one

def fullRecordGapValue10831 : Nat := fullRecordGapCenterValue + 652502

theorem fullRecordGapTerm10831_eq_value :
    recordGapCenter + 652502 = fullRecordGapValue10831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10831 (fullRecordGapValue10831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10831_not_prime : ¬(recordGapCenter + 652502).Prime := by
  rw [fullRecordGapTerm10831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10831_fast_pow_mod_ne_one

def fullRecordGapValue10832 : Nat := fullRecordGapCenterValue + 652566

theorem fullRecordGapTerm10832_eq_value :
    recordGapCenter + 652566 = fullRecordGapValue10832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10832 (fullRecordGapValue10832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10832_not_prime : ¬(recordGapCenter + 652566).Prime := by
  rw [fullRecordGapTerm10832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10832_fast_pow_mod_ne_one

def fullRecordGapValue10833 : Nat := fullRecordGapCenterValue + 652836

theorem fullRecordGapTerm10833_eq_value :
    recordGapCenter + 652836 = fullRecordGapValue10833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10833 (fullRecordGapValue10833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10833_not_prime : ¬(recordGapCenter + 652836).Prime := by
  rw [fullRecordGapTerm10833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10833_fast_pow_mod_ne_one

def fullRecordGapValue10834 : Nat := fullRecordGapCenterValue + 652892

theorem fullRecordGapTerm10834_eq_value :
    recordGapCenter + 652892 = fullRecordGapValue10834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10834 (fullRecordGapValue10834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10834_not_prime : ¬(recordGapCenter + 652892).Prime := by
  rw [fullRecordGapTerm10834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10834_fast_pow_mod_ne_one

def fullRecordGapValue10835 : Nat := fullRecordGapCenterValue + 652926

theorem fullRecordGapTerm10835_eq_value :
    recordGapCenter + 652926 = fullRecordGapValue10835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10835 (fullRecordGapValue10835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10835_not_prime : ¬(recordGapCenter + 652926).Prime := by
  rw [fullRecordGapTerm10835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10835_fast_pow_mod_ne_one

def fullRecordGapValue10836 : Nat := fullRecordGapCenterValue + 652958

theorem fullRecordGapTerm10836_eq_value :
    recordGapCenter + 652958 = fullRecordGapValue10836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10836 (fullRecordGapValue10836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10836_not_prime : ¬(recordGapCenter + 652958).Prime := by
  rw [fullRecordGapTerm10836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10836_fast_pow_mod_ne_one

def fullRecordGapValue10837 : Nat := fullRecordGapCenterValue + 653006

theorem fullRecordGapTerm10837_eq_value :
    recordGapCenter + 653006 = fullRecordGapValue10837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10837 (fullRecordGapValue10837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10837_not_prime : ¬(recordGapCenter + 653006).Prime := by
  rw [fullRecordGapTerm10837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10837_fast_pow_mod_ne_one

def fullRecordGapValue10838 : Nat := fullRecordGapCenterValue + 653096

theorem fullRecordGapTerm10838_eq_value :
    recordGapCenter + 653096 = fullRecordGapValue10838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10838 (fullRecordGapValue10838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10838_not_prime : ¬(recordGapCenter + 653096).Prime := by
  rw [fullRecordGapTerm10838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10838_fast_pow_mod_ne_one

def fullRecordGapValue10839 : Nat := fullRecordGapCenterValue + 653222

theorem fullRecordGapTerm10839_eq_value :
    recordGapCenter + 653222 = fullRecordGapValue10839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10839 (fullRecordGapValue10839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10839_not_prime : ¬(recordGapCenter + 653222).Prime := by
  rw [fullRecordGapTerm10839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10839_fast_pow_mod_ne_one

def fullRecordGapValue10840 : Nat := fullRecordGapCenterValue + 653270

theorem fullRecordGapTerm10840_eq_value :
    recordGapCenter + 653270 = fullRecordGapValue10840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10840 (fullRecordGapValue10840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10840_not_prime : ¬(recordGapCenter + 653270).Prime := by
  rw [fullRecordGapTerm10840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10840_fast_pow_mod_ne_one

def fullRecordGapValue10841 : Nat := fullRecordGapCenterValue + 653282

theorem fullRecordGapTerm10841_eq_value :
    recordGapCenter + 653282 = fullRecordGapValue10841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10841 (fullRecordGapValue10841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10841_not_prime : ¬(recordGapCenter + 653282).Prime := by
  rw [fullRecordGapTerm10841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10841_fast_pow_mod_ne_one

def fullRecordGapValue10842 : Nat := fullRecordGapCenterValue + 653298

theorem fullRecordGapTerm10842_eq_value :
    recordGapCenter + 653298 = fullRecordGapValue10842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10842 (fullRecordGapValue10842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10842_not_prime : ¬(recordGapCenter + 653298).Prime := by
  rw [fullRecordGapTerm10842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10842_fast_pow_mod_ne_one

def fullRecordGapValue10843 : Nat := fullRecordGapCenterValue + 653336

theorem fullRecordGapTerm10843_eq_value :
    recordGapCenter + 653336 = fullRecordGapValue10843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10843 (fullRecordGapValue10843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10843_not_prime : ¬(recordGapCenter + 653336).Prime := by
  rw [fullRecordGapTerm10843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10843_fast_pow_mod_ne_one

def fullRecordGapValue10844 : Nat := fullRecordGapCenterValue + 653388

theorem fullRecordGapTerm10844_eq_value :
    recordGapCenter + 653388 = fullRecordGapValue10844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10844 (fullRecordGapValue10844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10844_not_prime : ¬(recordGapCenter + 653388).Prime := by
  rw [fullRecordGapTerm10844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10844_fast_pow_mod_ne_one

def fullRecordGapValue10845 : Nat := fullRecordGapCenterValue + 653402

theorem fullRecordGapTerm10845_eq_value :
    recordGapCenter + 653402 = fullRecordGapValue10845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10845 (fullRecordGapValue10845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10845_not_prime : ¬(recordGapCenter + 653402).Prime := by
  rw [fullRecordGapTerm10845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10845_fast_pow_mod_ne_one

def fullRecordGapValue10846 : Nat := fullRecordGapCenterValue + 653468

theorem fullRecordGapTerm10846_eq_value :
    recordGapCenter + 653468 = fullRecordGapValue10846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10846 (fullRecordGapValue10846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10846_not_prime : ¬(recordGapCenter + 653468).Prime := by
  rw [fullRecordGapTerm10846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10846_fast_pow_mod_ne_one

def fullRecordGapValue10847 : Nat := fullRecordGapCenterValue + 653502

theorem fullRecordGapTerm10847_eq_value :
    recordGapCenter + 653502 = fullRecordGapValue10847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10847 (fullRecordGapValue10847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10847_not_prime : ¬(recordGapCenter + 653502).Prime := by
  rw [fullRecordGapTerm10847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10847_fast_pow_mod_ne_one

def fullRecordGapValue10848 : Nat := fullRecordGapCenterValue + 653558

theorem fullRecordGapTerm10848_eq_value :
    recordGapCenter + 653558 = fullRecordGapValue10848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10848 (fullRecordGapValue10848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10848_not_prime : ¬(recordGapCenter + 653558).Prime := by
  rw [fullRecordGapTerm10848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10848_fast_pow_mod_ne_one

def fullRecordGapValue10849 : Nat := fullRecordGapCenterValue + 653628

theorem fullRecordGapTerm10849_eq_value :
    recordGapCenter + 653628 = fullRecordGapValue10849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10849 (fullRecordGapValue10849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10849_not_prime : ¬(recordGapCenter + 653628).Prime := by
  rw [fullRecordGapTerm10849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10849_fast_pow_mod_ne_one

def fullRecordGapValue10850 : Nat := fullRecordGapCenterValue + 653658

theorem fullRecordGapTerm10850_eq_value :
    recordGapCenter + 653658 = fullRecordGapValue10850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10850 (fullRecordGapValue10850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10850_not_prime : ¬(recordGapCenter + 653658).Prime := by
  rw [fullRecordGapTerm10850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10850_fast_pow_mod_ne_one

def fullRecordGapValue10851 : Nat := fullRecordGapCenterValue + 653738

theorem fullRecordGapTerm10851_eq_value :
    recordGapCenter + 653738 = fullRecordGapValue10851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10851 (fullRecordGapValue10851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10851_not_prime : ¬(recordGapCenter + 653738).Prime := by
  rw [fullRecordGapTerm10851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10851_fast_pow_mod_ne_one

def fullRecordGapValue10852 : Nat := fullRecordGapCenterValue + 653762

theorem fullRecordGapTerm10852_eq_value :
    recordGapCenter + 653762 = fullRecordGapValue10852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10852 (fullRecordGapValue10852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10852_not_prime : ¬(recordGapCenter + 653762).Prime := by
  rw [fullRecordGapTerm10852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10852_fast_pow_mod_ne_one

def fullRecordGapValue10853 : Nat := fullRecordGapCenterValue + 653816

theorem fullRecordGapTerm10853_eq_value :
    recordGapCenter + 653816 = fullRecordGapValue10853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10853 (fullRecordGapValue10853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10853_not_prime : ¬(recordGapCenter + 653816).Prime := by
  rw [fullRecordGapTerm10853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10853_fast_pow_mod_ne_one

def fullRecordGapValue10854 : Nat := fullRecordGapCenterValue + 653826

theorem fullRecordGapTerm10854_eq_value :
    recordGapCenter + 653826 = fullRecordGapValue10854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10854 (fullRecordGapValue10854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10854_not_prime : ¬(recordGapCenter + 653826).Prime := by
  rw [fullRecordGapTerm10854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10854_fast_pow_mod_ne_one

def fullRecordGapValue10855 : Nat := fullRecordGapCenterValue + 653846

theorem fullRecordGapTerm10855_eq_value :
    recordGapCenter + 653846 = fullRecordGapValue10855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10855 (fullRecordGapValue10855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10855_not_prime : ¬(recordGapCenter + 653846).Prime := by
  rw [fullRecordGapTerm10855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10855_fast_pow_mod_ne_one

def fullRecordGapValue10856 : Nat := fullRecordGapCenterValue + 653882

theorem fullRecordGapTerm10856_eq_value :
    recordGapCenter + 653882 = fullRecordGapValue10856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10856 (fullRecordGapValue10856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10856_not_prime : ¬(recordGapCenter + 653882).Prime := by
  rw [fullRecordGapTerm10856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10856_fast_pow_mod_ne_one

def fullRecordGapValue10857 : Nat := fullRecordGapCenterValue + 654006

theorem fullRecordGapTerm10857_eq_value :
    recordGapCenter + 654006 = fullRecordGapValue10857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10857 (fullRecordGapValue10857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10857_not_prime : ¬(recordGapCenter + 654006).Prime := by
  rw [fullRecordGapTerm10857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10857_fast_pow_mod_ne_one

def fullRecordGapValue10858 : Nat := fullRecordGapCenterValue + 654068

theorem fullRecordGapTerm10858_eq_value :
    recordGapCenter + 654068 = fullRecordGapValue10858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10858 (fullRecordGapValue10858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10858_not_prime : ¬(recordGapCenter + 654068).Prime := by
  rw [fullRecordGapTerm10858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10858_fast_pow_mod_ne_one

def fullRecordGapValue10859 : Nat := fullRecordGapCenterValue + 654230

theorem fullRecordGapTerm10859_eq_value :
    recordGapCenter + 654230 = fullRecordGapValue10859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10859 (fullRecordGapValue10859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10859_not_prime : ¬(recordGapCenter + 654230).Prime := by
  rw [fullRecordGapTerm10859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10859_fast_pow_mod_ne_one

def fullRecordGapValue10860 : Nat := fullRecordGapCenterValue + 654252

theorem fullRecordGapTerm10860_eq_value :
    recordGapCenter + 654252 = fullRecordGapValue10860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10860 (fullRecordGapValue10860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10860_not_prime : ¬(recordGapCenter + 654252).Prime := by
  rw [fullRecordGapTerm10860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10860_fast_pow_mod_ne_one

def fullRecordGapValue10861 : Nat := fullRecordGapCenterValue + 654266

theorem fullRecordGapTerm10861_eq_value :
    recordGapCenter + 654266 = fullRecordGapValue10861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10861 (fullRecordGapValue10861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10861_not_prime : ¬(recordGapCenter + 654266).Prime := by
  rw [fullRecordGapTerm10861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10861_fast_pow_mod_ne_one

def fullRecordGapValue10862 : Nat := fullRecordGapCenterValue + 654392

theorem fullRecordGapTerm10862_eq_value :
    recordGapCenter + 654392 = fullRecordGapValue10862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10862 (fullRecordGapValue10862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10862_not_prime : ¬(recordGapCenter + 654392).Prime := by
  rw [fullRecordGapTerm10862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10862_fast_pow_mod_ne_one

def fullRecordGapValue10863 : Nat := fullRecordGapCenterValue + 654438

theorem fullRecordGapTerm10863_eq_value :
    recordGapCenter + 654438 = fullRecordGapValue10863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10863 (fullRecordGapValue10863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10863_not_prime : ¬(recordGapCenter + 654438).Prime := by
  rw [fullRecordGapTerm10863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10863_fast_pow_mod_ne_one

def fullRecordGapValue10864 : Nat := fullRecordGapCenterValue + 654458

theorem fullRecordGapTerm10864_eq_value :
    recordGapCenter + 654458 = fullRecordGapValue10864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10864 (fullRecordGapValue10864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10864_not_prime : ¬(recordGapCenter + 654458).Prime := by
  rw [fullRecordGapTerm10864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10864_fast_pow_mod_ne_one

def fullRecordGapValue10865 : Nat := fullRecordGapCenterValue + 654582

theorem fullRecordGapTerm10865_eq_value :
    recordGapCenter + 654582 = fullRecordGapValue10865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10865 (fullRecordGapValue10865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10865_not_prime : ¬(recordGapCenter + 654582).Prime := by
  rw [fullRecordGapTerm10865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10865_fast_pow_mod_ne_one

def fullRecordGapValue10866 : Nat := fullRecordGapCenterValue + 654638

theorem fullRecordGapTerm10866_eq_value :
    recordGapCenter + 654638 = fullRecordGapValue10866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10866 (fullRecordGapValue10866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10866_not_prime : ¬(recordGapCenter + 654638).Prime := by
  rw [fullRecordGapTerm10866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10866_fast_pow_mod_ne_one

def fullRecordGapValue10867 : Nat := fullRecordGapCenterValue + 654686

theorem fullRecordGapTerm10867_eq_value :
    recordGapCenter + 654686 = fullRecordGapValue10867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10867 (fullRecordGapValue10867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10867_not_prime : ¬(recordGapCenter + 654686).Prime := by
  rw [fullRecordGapTerm10867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10867_fast_pow_mod_ne_one

def fullRecordGapValue10868 : Nat := fullRecordGapCenterValue + 654692

theorem fullRecordGapTerm10868_eq_value :
    recordGapCenter + 654692 = fullRecordGapValue10868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10868 (fullRecordGapValue10868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10868_not_prime : ¬(recordGapCenter + 654692).Prime := by
  rw [fullRecordGapTerm10868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10868_fast_pow_mod_ne_one

def fullRecordGapValue10869 : Nat := fullRecordGapCenterValue + 654708

theorem fullRecordGapTerm10869_eq_value :
    recordGapCenter + 654708 = fullRecordGapValue10869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10869 (fullRecordGapValue10869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10869_not_prime : ¬(recordGapCenter + 654708).Prime := by
  rw [fullRecordGapTerm10869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10869_fast_pow_mod_ne_one

def fullRecordGapValue10870 : Nat := fullRecordGapCenterValue + 654788

theorem fullRecordGapTerm10870_eq_value :
    recordGapCenter + 654788 = fullRecordGapValue10870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10870 (fullRecordGapValue10870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10870_not_prime : ¬(recordGapCenter + 654788).Prime := by
  rw [fullRecordGapTerm10870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10870_fast_pow_mod_ne_one

def fullRecordGapValue10871 : Nat := fullRecordGapCenterValue + 654866

theorem fullRecordGapTerm10871_eq_value :
    recordGapCenter + 654866 = fullRecordGapValue10871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10871 (fullRecordGapValue10871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10871_not_prime : ¬(recordGapCenter + 654866).Prime := by
  rw [fullRecordGapTerm10871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10871_fast_pow_mod_ne_one

def fullRecordGapValue10872 : Nat := fullRecordGapCenterValue + 654932

theorem fullRecordGapTerm10872_eq_value :
    recordGapCenter + 654932 = fullRecordGapValue10872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10872 (fullRecordGapValue10872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10872_not_prime : ¬(recordGapCenter + 654932).Prime := by
  rw [fullRecordGapTerm10872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10872_fast_pow_mod_ne_one

def fullRecordGapValue10873 : Nat := fullRecordGapCenterValue + 655022

theorem fullRecordGapTerm10873_eq_value :
    recordGapCenter + 655022 = fullRecordGapValue10873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10873 (fullRecordGapValue10873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10873_not_prime : ¬(recordGapCenter + 655022).Prime := by
  rw [fullRecordGapTerm10873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10873_fast_pow_mod_ne_one

def fullRecordGapValue10874 : Nat := fullRecordGapCenterValue + 655026

theorem fullRecordGapTerm10874_eq_value :
    recordGapCenter + 655026 = fullRecordGapValue10874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10874 (fullRecordGapValue10874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10874_not_prime : ¬(recordGapCenter + 655026).Prime := by
  rw [fullRecordGapTerm10874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10874_fast_pow_mod_ne_one

def fullRecordGapValue10875 : Nat := fullRecordGapCenterValue + 655058

theorem fullRecordGapTerm10875_eq_value :
    recordGapCenter + 655058 = fullRecordGapValue10875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10875 (fullRecordGapValue10875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10875_not_prime : ¬(recordGapCenter + 655058).Prime := by
  rw [fullRecordGapTerm10875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10875_fast_pow_mod_ne_one

def fullRecordGapValue10876 : Nat := fullRecordGapCenterValue + 655106

theorem fullRecordGapTerm10876_eq_value :
    recordGapCenter + 655106 = fullRecordGapValue10876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10876 (fullRecordGapValue10876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10876_not_prime : ¬(recordGapCenter + 655106).Prime := by
  rw [fullRecordGapTerm10876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10876_fast_pow_mod_ne_one

def fullRecordGapValue10877 : Nat := fullRecordGapCenterValue + 655208

theorem fullRecordGapTerm10877_eq_value :
    recordGapCenter + 655208 = fullRecordGapValue10877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10877 (fullRecordGapValue10877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10877_not_prime : ¬(recordGapCenter + 655208).Prime := by
  rw [fullRecordGapTerm10877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10877_fast_pow_mod_ne_one

def fullRecordGapValue10878 : Nat := fullRecordGapCenterValue + 655298

theorem fullRecordGapTerm10878_eq_value :
    recordGapCenter + 655298 = fullRecordGapValue10878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10878 (fullRecordGapValue10878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10878_not_prime : ¬(recordGapCenter + 655298).Prime := by
  rw [fullRecordGapTerm10878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10878_fast_pow_mod_ne_one

def fullRecordGapValue10879 : Nat := fullRecordGapCenterValue + 655370

theorem fullRecordGapTerm10879_eq_value :
    recordGapCenter + 655370 = fullRecordGapValue10879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10879 (fullRecordGapValue10879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10879_not_prime : ¬(recordGapCenter + 655370).Prime := by
  rw [fullRecordGapTerm10879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10879_fast_pow_mod_ne_one

def fullRecordGapValue10880 : Nat := fullRecordGapCenterValue + 655412

theorem fullRecordGapTerm10880_eq_value :
    recordGapCenter + 655412 = fullRecordGapValue10880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10880 (fullRecordGapValue10880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10880_not_prime : ¬(recordGapCenter + 655412).Prime := by
  rw [fullRecordGapTerm10880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10880_fast_pow_mod_ne_one

def fullRecordGapValue10881 : Nat := fullRecordGapCenterValue + 655436

theorem fullRecordGapTerm10881_eq_value :
    recordGapCenter + 655436 = fullRecordGapValue10881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10881 (fullRecordGapValue10881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10881_not_prime : ¬(recordGapCenter + 655436).Prime := by
  rw [fullRecordGapTerm10881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10881_fast_pow_mod_ne_one

def fullRecordGapValue10882 : Nat := fullRecordGapCenterValue + 655466

theorem fullRecordGapTerm10882_eq_value :
    recordGapCenter + 655466 = fullRecordGapValue10882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10882 (fullRecordGapValue10882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10882_not_prime : ¬(recordGapCenter + 655466).Prime := by
  rw [fullRecordGapTerm10882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10882_fast_pow_mod_ne_one

def fullRecordGapValue10883 : Nat := fullRecordGapCenterValue + 655476

theorem fullRecordGapTerm10883_eq_value :
    recordGapCenter + 655476 = fullRecordGapValue10883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10883 (fullRecordGapValue10883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10883_not_prime : ¬(recordGapCenter + 655476).Prime := by
  rw [fullRecordGapTerm10883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10883_fast_pow_mod_ne_one

def fullRecordGapValue10884 : Nat := fullRecordGapCenterValue + 655478

theorem fullRecordGapTerm10884_eq_value :
    recordGapCenter + 655478 = fullRecordGapValue10884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10884 (fullRecordGapValue10884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10884_not_prime : ¬(recordGapCenter + 655478).Prime := by
  rw [fullRecordGapTerm10884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10884_fast_pow_mod_ne_one

def fullRecordGapValue10885 : Nat := fullRecordGapCenterValue + 655496

theorem fullRecordGapTerm10885_eq_value :
    recordGapCenter + 655496 = fullRecordGapValue10885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10885 (fullRecordGapValue10885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10885_not_prime : ¬(recordGapCenter + 655496).Prime := by
  rw [fullRecordGapTerm10885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10885_fast_pow_mod_ne_one

def fullRecordGapValue10886 : Nat := fullRecordGapCenterValue + 655548

theorem fullRecordGapTerm10886_eq_value :
    recordGapCenter + 655548 = fullRecordGapValue10886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10886 (fullRecordGapValue10886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10886_not_prime : ¬(recordGapCenter + 655548).Prime := by
  rw [fullRecordGapTerm10886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10886_fast_pow_mod_ne_one

def fullRecordGapValue10887 : Nat := fullRecordGapCenterValue + 655572

theorem fullRecordGapTerm10887_eq_value :
    recordGapCenter + 655572 = fullRecordGapValue10887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10887 (fullRecordGapValue10887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10887_not_prime : ¬(recordGapCenter + 655572).Prime := by
  rw [fullRecordGapTerm10887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10887_fast_pow_mod_ne_one

def fullRecordGapValue10888 : Nat := fullRecordGapCenterValue + 655602

theorem fullRecordGapTerm10888_eq_value :
    recordGapCenter + 655602 = fullRecordGapValue10888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10888 (fullRecordGapValue10888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10888_not_prime : ¬(recordGapCenter + 655602).Prime := by
  rw [fullRecordGapTerm10888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10888_fast_pow_mod_ne_one

def fullRecordGapValue10889 : Nat := fullRecordGapCenterValue + 655736

theorem fullRecordGapTerm10889_eq_value :
    recordGapCenter + 655736 = fullRecordGapValue10889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10889 (fullRecordGapValue10889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10889_not_prime : ¬(recordGapCenter + 655736).Prime := by
  rw [fullRecordGapTerm10889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10889_fast_pow_mod_ne_one

def fullRecordGapValue10890 : Nat := fullRecordGapCenterValue + 655778

theorem fullRecordGapTerm10890_eq_value :
    recordGapCenter + 655778 = fullRecordGapValue10890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10890 (fullRecordGapValue10890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10890_not_prime : ¬(recordGapCenter + 655778).Prime := by
  rw [fullRecordGapTerm10890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10890_fast_pow_mod_ne_one

def fullRecordGapValue10891 : Nat := fullRecordGapCenterValue + 655782

theorem fullRecordGapTerm10891_eq_value :
    recordGapCenter + 655782 = fullRecordGapValue10891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10891 (fullRecordGapValue10891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10891_not_prime : ¬(recordGapCenter + 655782).Prime := by
  rw [fullRecordGapTerm10891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10891_fast_pow_mod_ne_one

def fullRecordGapValue10892 : Nat := fullRecordGapCenterValue + 655958

theorem fullRecordGapTerm10892_eq_value :
    recordGapCenter + 655958 = fullRecordGapValue10892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10892 (fullRecordGapValue10892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10892_not_prime : ¬(recordGapCenter + 655958).Prime := by
  rw [fullRecordGapTerm10892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10892_fast_pow_mod_ne_one

def fullRecordGapValue10893 : Nat := fullRecordGapCenterValue + 655986

theorem fullRecordGapTerm10893_eq_value :
    recordGapCenter + 655986 = fullRecordGapValue10893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10893 (fullRecordGapValue10893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10893_not_prime : ¬(recordGapCenter + 655986).Prime := by
  rw [fullRecordGapTerm10893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10893_fast_pow_mod_ne_one

def fullRecordGapValue10894 : Nat := fullRecordGapCenterValue + 655988

theorem fullRecordGapTerm10894_eq_value :
    recordGapCenter + 655988 = fullRecordGapValue10894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10894 (fullRecordGapValue10894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10894_not_prime : ¬(recordGapCenter + 655988).Prime := by
  rw [fullRecordGapTerm10894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10894_fast_pow_mod_ne_one

def fullRecordGapValue10895 : Nat := fullRecordGapCenterValue + 656072

theorem fullRecordGapTerm10895_eq_value :
    recordGapCenter + 656072 = fullRecordGapValue10895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10895 (fullRecordGapValue10895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10895_not_prime : ¬(recordGapCenter + 656072).Prime := by
  rw [fullRecordGapTerm10895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10895_fast_pow_mod_ne_one

def fullRecordGapValue10896 : Nat := fullRecordGapCenterValue + 656142

theorem fullRecordGapTerm10896_eq_value :
    recordGapCenter + 656142 = fullRecordGapValue10896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10896 (fullRecordGapValue10896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10896_not_prime : ¬(recordGapCenter + 656142).Prime := by
  rw [fullRecordGapTerm10896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10896_fast_pow_mod_ne_one

def fullRecordGapValue10897 : Nat := fullRecordGapCenterValue + 656148

theorem fullRecordGapTerm10897_eq_value :
    recordGapCenter + 656148 = fullRecordGapValue10897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10897 (fullRecordGapValue10897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10897_not_prime : ¬(recordGapCenter + 656148).Prime := by
  rw [fullRecordGapTerm10897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10897_fast_pow_mod_ne_one

def fullRecordGapValue10898 : Nat := fullRecordGapCenterValue + 656202

theorem fullRecordGapTerm10898_eq_value :
    recordGapCenter + 656202 = fullRecordGapValue10898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10898 (fullRecordGapValue10898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10898_not_prime : ¬(recordGapCenter + 656202).Prime := by
  rw [fullRecordGapTerm10898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10898_fast_pow_mod_ne_one

def fullRecordGapValue10899 : Nat := fullRecordGapCenterValue + 656342

theorem fullRecordGapTerm10899_eq_value :
    recordGapCenter + 656342 = fullRecordGapValue10899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10899 (fullRecordGapValue10899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10899_not_prime : ¬(recordGapCenter + 656342).Prime := by
  rw [fullRecordGapTerm10899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10899_fast_pow_mod_ne_one

def fullRecordGapValue10900 : Nat := fullRecordGapCenterValue + 656346

theorem fullRecordGapTerm10900_eq_value :
    recordGapCenter + 656346 = fullRecordGapValue10900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10900 (fullRecordGapValue10900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10900_not_prime : ¬(recordGapCenter + 656346).Prime := by
  rw [fullRecordGapTerm10900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10900_fast_pow_mod_ne_one

def fullRecordGapValue10901 : Nat := fullRecordGapCenterValue + 656372

theorem fullRecordGapTerm10901_eq_value :
    recordGapCenter + 656372 = fullRecordGapValue10901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10901 (fullRecordGapValue10901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10901_not_prime : ¬(recordGapCenter + 656372).Prime := by
  rw [fullRecordGapTerm10901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10901_fast_pow_mod_ne_one

def fullRecordGapValue10902 : Nat := fullRecordGapCenterValue + 656510

theorem fullRecordGapTerm10902_eq_value :
    recordGapCenter + 656510 = fullRecordGapValue10902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10902 (fullRecordGapValue10902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10902_not_prime : ¬(recordGapCenter + 656510).Prime := by
  rw [fullRecordGapTerm10902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10902_fast_pow_mod_ne_one

def fullRecordGapValue10903 : Nat := fullRecordGapCenterValue + 656556

theorem fullRecordGapTerm10903_eq_value :
    recordGapCenter + 656556 = fullRecordGapValue10903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10903 (fullRecordGapValue10903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10903_not_prime : ¬(recordGapCenter + 656556).Prime := by
  rw [fullRecordGapTerm10903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10903_fast_pow_mod_ne_one

def fullRecordGapValue10904 : Nat := fullRecordGapCenterValue + 656570

theorem fullRecordGapTerm10904_eq_value :
    recordGapCenter + 656570 = fullRecordGapValue10904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10904 (fullRecordGapValue10904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10904_not_prime : ¬(recordGapCenter + 656570).Prime := by
  rw [fullRecordGapTerm10904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10904_fast_pow_mod_ne_one

def fullRecordGapValue10905 : Nat := fullRecordGapCenterValue + 656598

theorem fullRecordGapTerm10905_eq_value :
    recordGapCenter + 656598 = fullRecordGapValue10905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10905 (fullRecordGapValue10905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10905_not_prime : ¬(recordGapCenter + 656598).Prime := by
  rw [fullRecordGapTerm10905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10905_fast_pow_mod_ne_one

def fullRecordGapValue10906 : Nat := fullRecordGapCenterValue + 656666

theorem fullRecordGapTerm10906_eq_value :
    recordGapCenter + 656666 = fullRecordGapValue10906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10906 (fullRecordGapValue10906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10906_not_prime : ¬(recordGapCenter + 656666).Prime := by
  rw [fullRecordGapTerm10906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10906_fast_pow_mod_ne_one

def fullRecordGapValue10907 : Nat := fullRecordGapCenterValue + 656706

theorem fullRecordGapTerm10907_eq_value :
    recordGapCenter + 656706 = fullRecordGapValue10907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10907 (fullRecordGapValue10907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10907_not_prime : ¬(recordGapCenter + 656706).Prime := by
  rw [fullRecordGapTerm10907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10907_fast_pow_mod_ne_one

def fullRecordGapValue10908 : Nat := fullRecordGapCenterValue + 656870

theorem fullRecordGapTerm10908_eq_value :
    recordGapCenter + 656870 = fullRecordGapValue10908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10908 (fullRecordGapValue10908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10908_not_prime : ¬(recordGapCenter + 656870).Prime := by
  rw [fullRecordGapTerm10908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10908_fast_pow_mod_ne_one

def fullRecordGapValue10909 : Nat := fullRecordGapCenterValue + 656990

theorem fullRecordGapTerm10909_eq_value :
    recordGapCenter + 656990 = fullRecordGapValue10909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10909 (fullRecordGapValue10909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10909_not_prime : ¬(recordGapCenter + 656990).Prime := by
  rw [fullRecordGapTerm10909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10909_fast_pow_mod_ne_one

def fullRecordGapValue10910 : Nat := fullRecordGapCenterValue + 657062

theorem fullRecordGapTerm10910_eq_value :
    recordGapCenter + 657062 = fullRecordGapValue10910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10910 (fullRecordGapValue10910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10910_not_prime : ¬(recordGapCenter + 657062).Prime := by
  rw [fullRecordGapTerm10910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10910_fast_pow_mod_ne_one

def fullRecordGapValue10911 : Nat := fullRecordGapCenterValue + 657086

theorem fullRecordGapTerm10911_eq_value :
    recordGapCenter + 657086 = fullRecordGapValue10911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10911 (fullRecordGapValue10911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10911_not_prime : ¬(recordGapCenter + 657086).Prime := by
  rw [fullRecordGapTerm10911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10911_fast_pow_mod_ne_one

def fullRecordGapValue10912 : Nat := fullRecordGapCenterValue + 657102

theorem fullRecordGapTerm10912_eq_value :
    recordGapCenter + 657102 = fullRecordGapValue10912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10912 (fullRecordGapValue10912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10912_not_prime : ¬(recordGapCenter + 657102).Prime := by
  rw [fullRecordGapTerm10912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10912_fast_pow_mod_ne_one

def fullRecordGapValue10913 : Nat := fullRecordGapCenterValue + 657116

theorem fullRecordGapTerm10913_eq_value :
    recordGapCenter + 657116 = fullRecordGapValue10913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10913 (fullRecordGapValue10913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10913_not_prime : ¬(recordGapCenter + 657116).Prime := by
  rw [fullRecordGapTerm10913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10913_fast_pow_mod_ne_one

def fullRecordGapValue10914 : Nat := fullRecordGapCenterValue + 657170

theorem fullRecordGapTerm10914_eq_value :
    recordGapCenter + 657170 = fullRecordGapValue10914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10914 (fullRecordGapValue10914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10914_not_prime : ¬(recordGapCenter + 657170).Prime := by
  rw [fullRecordGapTerm10914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10914_fast_pow_mod_ne_one

def fullRecordGapValue10915 : Nat := fullRecordGapCenterValue + 657242

theorem fullRecordGapTerm10915_eq_value :
    recordGapCenter + 657242 = fullRecordGapValue10915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10915 (fullRecordGapValue10915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10915_not_prime : ¬(recordGapCenter + 657242).Prime := by
  rw [fullRecordGapTerm10915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10915_fast_pow_mod_ne_one

def fullRecordGapValue10916 : Nat := fullRecordGapCenterValue + 657276

theorem fullRecordGapTerm10916_eq_value :
    recordGapCenter + 657276 = fullRecordGapValue10916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10916 (fullRecordGapValue10916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10916_not_prime : ¬(recordGapCenter + 657276).Prime := by
  rw [fullRecordGapTerm10916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10916_fast_pow_mod_ne_one

def fullRecordGapValue10917 : Nat := fullRecordGapCenterValue + 657282

theorem fullRecordGapTerm10917_eq_value :
    recordGapCenter + 657282 = fullRecordGapValue10917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10917 (fullRecordGapValue10917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10917_not_prime : ¬(recordGapCenter + 657282).Prime := by
  rw [fullRecordGapTerm10917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10917_fast_pow_mod_ne_one

def fullRecordGapValue10918 : Nat := fullRecordGapCenterValue + 657398

theorem fullRecordGapTerm10918_eq_value :
    recordGapCenter + 657398 = fullRecordGapValue10918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10918 (fullRecordGapValue10918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10918_not_prime : ¬(recordGapCenter + 657398).Prime := by
  rw [fullRecordGapTerm10918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10918_fast_pow_mod_ne_one

end PrimeFactorUnimodality
