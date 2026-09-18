import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue00769 : Nat := fullRecordGapCenterValue - 393868

theorem fullRecordGapTerm00769_eq_value :
    recordGapCenter - 393868 = fullRecordGapValue00769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00769 (fullRecordGapValue00769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00769_not_prime : ¬(recordGapCenter - 393868).Prime := by
  rw [fullRecordGapTerm00769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00769_fast_pow_mod_ne_one

def fullRecordGapValue00770 : Nat := fullRecordGapCenterValue - 393774

theorem fullRecordGapTerm00770_eq_value :
    recordGapCenter - 393774 = fullRecordGapValue00770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00770 (fullRecordGapValue00770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00770_not_prime : ¬(recordGapCenter - 393774).Prime := by
  rw [fullRecordGapTerm00770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00770_fast_pow_mod_ne_one

def fullRecordGapValue00771 : Nat := fullRecordGapCenterValue - 393634

theorem fullRecordGapTerm00771_eq_value :
    recordGapCenter - 393634 = fullRecordGapValue00771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00771 (fullRecordGapValue00771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00771_not_prime : ¬(recordGapCenter - 393634).Prime := by
  rw [fullRecordGapTerm00771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00771_fast_pow_mod_ne_one

def fullRecordGapValue00772 : Nat := fullRecordGapCenterValue - 393594

theorem fullRecordGapTerm00772_eq_value :
    recordGapCenter - 393594 = fullRecordGapValue00772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00772 (fullRecordGapValue00772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00772_not_prime : ¬(recordGapCenter - 393594).Prime := by
  rw [fullRecordGapTerm00772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00772_fast_pow_mod_ne_one

def fullRecordGapValue00773 : Nat := fullRecordGapCenterValue - 393592

theorem fullRecordGapTerm00773_eq_value :
    recordGapCenter - 393592 = fullRecordGapValue00773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00773 (fullRecordGapValue00773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00773_not_prime : ¬(recordGapCenter - 393592).Prime := by
  rw [fullRecordGapTerm00773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00773_fast_pow_mod_ne_one

def fullRecordGapValue00774 : Nat := fullRecordGapCenterValue - 393544

theorem fullRecordGapTerm00774_eq_value :
    recordGapCenter - 393544 = fullRecordGapValue00774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00774 (fullRecordGapValue00774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00774_not_prime : ¬(recordGapCenter - 393544).Prime := by
  rw [fullRecordGapTerm00774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00774_fast_pow_mod_ne_one

def fullRecordGapValue00775 : Nat := fullRecordGapCenterValue - 393508

theorem fullRecordGapTerm00775_eq_value :
    recordGapCenter - 393508 = fullRecordGapValue00775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00775 (fullRecordGapValue00775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00775_not_prime : ¬(recordGapCenter - 393508).Prime := by
  rw [fullRecordGapTerm00775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00775_fast_pow_mod_ne_one

def fullRecordGapValue00776 : Nat := fullRecordGapCenterValue - 393454

theorem fullRecordGapTerm00776_eq_value :
    recordGapCenter - 393454 = fullRecordGapValue00776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00776 (fullRecordGapValue00776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00776_not_prime : ¬(recordGapCenter - 393454).Prime := by
  rw [fullRecordGapTerm00776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00776_fast_pow_mod_ne_one

def fullRecordGapValue00777 : Nat := fullRecordGapCenterValue - 393378

theorem fullRecordGapTerm00777_eq_value :
    recordGapCenter - 393378 = fullRecordGapValue00777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00777 (fullRecordGapValue00777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00777_not_prime : ¬(recordGapCenter - 393378).Prime := by
  rw [fullRecordGapTerm00777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00777_fast_pow_mod_ne_one

def fullRecordGapValue00778 : Nat := fullRecordGapCenterValue - 393322

theorem fullRecordGapTerm00778_eq_value :
    recordGapCenter - 393322 = fullRecordGapValue00778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00778 (fullRecordGapValue00778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00778_not_prime : ¬(recordGapCenter - 393322).Prime := by
  rw [fullRecordGapTerm00778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00778_fast_pow_mod_ne_one

def fullRecordGapValue00779 : Nat := fullRecordGapCenterValue - 393292

theorem fullRecordGapTerm00779_eq_value :
    recordGapCenter - 393292 = fullRecordGapValue00779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00779 (fullRecordGapValue00779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00779_not_prime : ¬(recordGapCenter - 393292).Prime := by
  rw [fullRecordGapTerm00779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00779_fast_pow_mod_ne_one

def fullRecordGapValue00780 : Nat := fullRecordGapCenterValue - 393258

theorem fullRecordGapTerm00780_eq_value :
    recordGapCenter - 393258 = fullRecordGapValue00780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00780 (fullRecordGapValue00780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00780_not_prime : ¬(recordGapCenter - 393258).Prime := by
  rw [fullRecordGapTerm00780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00780_fast_pow_mod_ne_one

def fullRecordGapValue00781 : Nat := fullRecordGapCenterValue - 393222

theorem fullRecordGapTerm00781_eq_value :
    recordGapCenter - 393222 = fullRecordGapValue00781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00781 (fullRecordGapValue00781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00781_not_prime : ¬(recordGapCenter - 393222).Prime := by
  rw [fullRecordGapTerm00781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00781_fast_pow_mod_ne_one

def fullRecordGapValue00782 : Nat := fullRecordGapCenterValue - 393004

theorem fullRecordGapTerm00782_eq_value :
    recordGapCenter - 393004 = fullRecordGapValue00782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00782 (fullRecordGapValue00782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00782_not_prime : ¬(recordGapCenter - 393004).Prime := by
  rw [fullRecordGapTerm00782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00782_fast_pow_mod_ne_one

def fullRecordGapValue00783 : Nat := fullRecordGapCenterValue - 392998

theorem fullRecordGapTerm00783_eq_value :
    recordGapCenter - 392998 = fullRecordGapValue00783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00783 (fullRecordGapValue00783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00783_not_prime : ¬(recordGapCenter - 392998).Prime := by
  rw [fullRecordGapTerm00783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00783_fast_pow_mod_ne_one

def fullRecordGapValue00784 : Nat := fullRecordGapCenterValue - 392908

theorem fullRecordGapTerm00784_eq_value :
    recordGapCenter - 392908 = fullRecordGapValue00784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00784 (fullRecordGapValue00784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00784_not_prime : ¬(recordGapCenter - 392908).Prime := by
  rw [fullRecordGapTerm00784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00784_fast_pow_mod_ne_one

def fullRecordGapValue00785 : Nat := fullRecordGapCenterValue - 392878

theorem fullRecordGapTerm00785_eq_value :
    recordGapCenter - 392878 = fullRecordGapValue00785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00785 (fullRecordGapValue00785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00785_not_prime : ¬(recordGapCenter - 392878).Prime := by
  rw [fullRecordGapTerm00785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00785_fast_pow_mod_ne_one

def fullRecordGapValue00786 : Nat := fullRecordGapCenterValue - 392872

theorem fullRecordGapTerm00786_eq_value :
    recordGapCenter - 392872 = fullRecordGapValue00786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00786 (fullRecordGapValue00786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00786_not_prime : ¬(recordGapCenter - 392872).Prime := by
  rw [fullRecordGapTerm00786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00786_fast_pow_mod_ne_one

def fullRecordGapValue00787 : Nat := fullRecordGapCenterValue - 392662

theorem fullRecordGapTerm00787_eq_value :
    recordGapCenter - 392662 = fullRecordGapValue00787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00787 (fullRecordGapValue00787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00787_not_prime : ¬(recordGapCenter - 392662).Prime := by
  rw [fullRecordGapTerm00787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00787_fast_pow_mod_ne_one

def fullRecordGapValue00788 : Nat := fullRecordGapCenterValue - 392622

theorem fullRecordGapTerm00788_eq_value :
    recordGapCenter - 392622 = fullRecordGapValue00788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00788 (fullRecordGapValue00788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00788_not_prime : ¬(recordGapCenter - 392622).Prime := by
  rw [fullRecordGapTerm00788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00788_fast_pow_mod_ne_one

def fullRecordGapValue00789 : Nat := fullRecordGapCenterValue - 392542

theorem fullRecordGapTerm00789_eq_value :
    recordGapCenter - 392542 = fullRecordGapValue00789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00789 (fullRecordGapValue00789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00789_not_prime : ¬(recordGapCenter - 392542).Prime := by
  rw [fullRecordGapTerm00789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00789_fast_pow_mod_ne_one

def fullRecordGapValue00790 : Nat := fullRecordGapCenterValue - 392362

theorem fullRecordGapTerm00790_eq_value :
    recordGapCenter - 392362 = fullRecordGapValue00790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00790 (fullRecordGapValue00790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00790_not_prime : ¬(recordGapCenter - 392362).Prime := by
  rw [fullRecordGapTerm00790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00790_fast_pow_mod_ne_one

def fullRecordGapValue00791 : Nat := fullRecordGapCenterValue - 392278

theorem fullRecordGapTerm00791_eq_value :
    recordGapCenter - 392278 = fullRecordGapValue00791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00791 (fullRecordGapValue00791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00791_not_prime : ¬(recordGapCenter - 392278).Prime := by
  rw [fullRecordGapTerm00791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00791_fast_pow_mod_ne_one

def fullRecordGapValue00792 : Nat := fullRecordGapCenterValue - 392188

theorem fullRecordGapTerm00792_eq_value :
    recordGapCenter - 392188 = fullRecordGapValue00792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00792 (fullRecordGapValue00792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00792_not_prime : ¬(recordGapCenter - 392188).Prime := by
  rw [fullRecordGapTerm00792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00792_fast_pow_mod_ne_one

def fullRecordGapValue00793 : Nat := fullRecordGapCenterValue - 392164

theorem fullRecordGapTerm00793_eq_value :
    recordGapCenter - 392164 = fullRecordGapValue00793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00793 (fullRecordGapValue00793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00793_not_prime : ¬(recordGapCenter - 392164).Prime := by
  rw [fullRecordGapTerm00793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00793_fast_pow_mod_ne_one

def fullRecordGapValue00794 : Nat := fullRecordGapCenterValue - 392068

theorem fullRecordGapTerm00794_eq_value :
    recordGapCenter - 392068 = fullRecordGapValue00794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00794 (fullRecordGapValue00794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00794_not_prime : ¬(recordGapCenter - 392068).Prime := by
  rw [fullRecordGapTerm00794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00794_fast_pow_mod_ne_one

def fullRecordGapValue00795 : Nat := fullRecordGapCenterValue - 391962

theorem fullRecordGapTerm00795_eq_value :
    recordGapCenter - 391962 = fullRecordGapValue00795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00795 (fullRecordGapValue00795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00795_not_prime : ¬(recordGapCenter - 391962).Prime := by
  rw [fullRecordGapTerm00795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00795_fast_pow_mod_ne_one

def fullRecordGapValue00796 : Nat := fullRecordGapCenterValue - 391954

theorem fullRecordGapTerm00796_eq_value :
    recordGapCenter - 391954 = fullRecordGapValue00796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00796 (fullRecordGapValue00796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00796_not_prime : ¬(recordGapCenter - 391954).Prime := by
  rw [fullRecordGapTerm00796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00796_fast_pow_mod_ne_one

def fullRecordGapValue00797 : Nat := fullRecordGapCenterValue - 391858

theorem fullRecordGapTerm00797_eq_value :
    recordGapCenter - 391858 = fullRecordGapValue00797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00797 (fullRecordGapValue00797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00797_not_prime : ¬(recordGapCenter - 391858).Prime := by
  rw [fullRecordGapTerm00797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00797_fast_pow_mod_ne_one

def fullRecordGapValue00798 : Nat := fullRecordGapCenterValue - 391738

theorem fullRecordGapTerm00798_eq_value :
    recordGapCenter - 391738 = fullRecordGapValue00798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00798 (fullRecordGapValue00798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00798_not_prime : ¬(recordGapCenter - 391738).Prime := by
  rw [fullRecordGapTerm00798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00798_fast_pow_mod_ne_one

def fullRecordGapValue00799 : Nat := fullRecordGapCenterValue - 391542

theorem fullRecordGapTerm00799_eq_value :
    recordGapCenter - 391542 = fullRecordGapValue00799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00799 (fullRecordGapValue00799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00799_not_prime : ¬(recordGapCenter - 391542).Prime := by
  rw [fullRecordGapTerm00799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00799_fast_pow_mod_ne_one

def fullRecordGapValue00800 : Nat := fullRecordGapCenterValue - 391444

theorem fullRecordGapTerm00800_eq_value :
    recordGapCenter - 391444 = fullRecordGapValue00800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00800 (fullRecordGapValue00800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00800_not_prime : ¬(recordGapCenter - 391444).Prime := by
  rw [fullRecordGapTerm00800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00800_fast_pow_mod_ne_one

def fullRecordGapValue00801 : Nat := fullRecordGapCenterValue - 391314

theorem fullRecordGapTerm00801_eq_value :
    recordGapCenter - 391314 = fullRecordGapValue00801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00801 (fullRecordGapValue00801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00801_not_prime : ¬(recordGapCenter - 391314).Prime := by
  rw [fullRecordGapTerm00801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00801_fast_pow_mod_ne_one

def fullRecordGapValue00802 : Nat := fullRecordGapCenterValue - 391278

theorem fullRecordGapTerm00802_eq_value :
    recordGapCenter - 391278 = fullRecordGapValue00802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00802 (fullRecordGapValue00802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00802_not_prime : ¬(recordGapCenter - 391278).Prime := by
  rw [fullRecordGapTerm00802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00802_fast_pow_mod_ne_one

def fullRecordGapValue00803 : Nat := fullRecordGapCenterValue - 391218

theorem fullRecordGapTerm00803_eq_value :
    recordGapCenter - 391218 = fullRecordGapValue00803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00803 (fullRecordGapValue00803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00803_not_prime : ¬(recordGapCenter - 391218).Prime := by
  rw [fullRecordGapTerm00803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00803_fast_pow_mod_ne_one

def fullRecordGapValue00804 : Nat := fullRecordGapCenterValue - 391198

theorem fullRecordGapTerm00804_eq_value :
    recordGapCenter - 391198 = fullRecordGapValue00804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00804 (fullRecordGapValue00804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00804_not_prime : ¬(recordGapCenter - 391198).Prime := by
  rw [fullRecordGapTerm00804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00804_fast_pow_mod_ne_one

def fullRecordGapValue00805 : Nat := fullRecordGapCenterValue - 391078

theorem fullRecordGapTerm00805_eq_value :
    recordGapCenter - 391078 = fullRecordGapValue00805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00805 (fullRecordGapValue00805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00805_not_prime : ¬(recordGapCenter - 391078).Prime := by
  rw [fullRecordGapTerm00805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00805_fast_pow_mod_ne_one

def fullRecordGapValue00806 : Nat := fullRecordGapCenterValue - 391038

theorem fullRecordGapTerm00806_eq_value :
    recordGapCenter - 391038 = fullRecordGapValue00806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00806 (fullRecordGapValue00806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00806_not_prime : ¬(recordGapCenter - 391038).Prime := by
  rw [fullRecordGapTerm00806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00806_fast_pow_mod_ne_one

def fullRecordGapValue00807 : Nat := fullRecordGapCenterValue - 391002

theorem fullRecordGapTerm00807_eq_value :
    recordGapCenter - 391002 = fullRecordGapValue00807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00807 (fullRecordGapValue00807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00807_not_prime : ¬(recordGapCenter - 391002).Prime := by
  rw [fullRecordGapTerm00807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00807_fast_pow_mod_ne_one

def fullRecordGapValue00808 : Nat := fullRecordGapCenterValue - 390882

theorem fullRecordGapTerm00808_eq_value :
    recordGapCenter - 390882 = fullRecordGapValue00808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00808 (fullRecordGapValue00808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00808_not_prime : ¬(recordGapCenter - 390882).Prime := by
  rw [fullRecordGapTerm00808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00808_fast_pow_mod_ne_one

def fullRecordGapValue00809 : Nat := fullRecordGapCenterValue - 390844

theorem fullRecordGapTerm00809_eq_value :
    recordGapCenter - 390844 = fullRecordGapValue00809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00809 (fullRecordGapValue00809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00809_not_prime : ¬(recordGapCenter - 390844).Prime := by
  rw [fullRecordGapTerm00809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00809_fast_pow_mod_ne_one

def fullRecordGapValue00810 : Nat := fullRecordGapCenterValue - 390802

theorem fullRecordGapTerm00810_eq_value :
    recordGapCenter - 390802 = fullRecordGapValue00810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00810 (fullRecordGapValue00810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00810_not_prime : ¬(recordGapCenter - 390802).Prime := by
  rw [fullRecordGapTerm00810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00810_fast_pow_mod_ne_one

def fullRecordGapValue00811 : Nat := fullRecordGapCenterValue - 390778

theorem fullRecordGapTerm00811_eq_value :
    recordGapCenter - 390778 = fullRecordGapValue00811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00811 (fullRecordGapValue00811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00811_not_prime : ¬(recordGapCenter - 390778).Prime := by
  rw [fullRecordGapTerm00811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00811_fast_pow_mod_ne_one

def fullRecordGapValue00812 : Nat := fullRecordGapCenterValue - 390774

theorem fullRecordGapTerm00812_eq_value :
    recordGapCenter - 390774 = fullRecordGapValue00812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00812 (fullRecordGapValue00812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00812_not_prime : ¬(recordGapCenter - 390774).Prime := by
  rw [fullRecordGapTerm00812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00812_fast_pow_mod_ne_one

def fullRecordGapValue00813 : Nat := fullRecordGapCenterValue - 390738

theorem fullRecordGapTerm00813_eq_value :
    recordGapCenter - 390738 = fullRecordGapValue00813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00813 (fullRecordGapValue00813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00813_not_prime : ¬(recordGapCenter - 390738).Prime := by
  rw [fullRecordGapTerm00813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00813_fast_pow_mod_ne_one

def fullRecordGapValue00814 : Nat := fullRecordGapCenterValue - 390682

theorem fullRecordGapTerm00814_eq_value :
    recordGapCenter - 390682 = fullRecordGapValue00814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00814 (fullRecordGapValue00814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00814_not_prime : ¬(recordGapCenter - 390682).Prime := by
  rw [fullRecordGapTerm00814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00814_fast_pow_mod_ne_one

def fullRecordGapValue00815 : Nat := fullRecordGapCenterValue - 390568

theorem fullRecordGapTerm00815_eq_value :
    recordGapCenter - 390568 = fullRecordGapValue00815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00815 (fullRecordGapValue00815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00815_not_prime : ¬(recordGapCenter - 390568).Prime := by
  rw [fullRecordGapTerm00815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00815_fast_pow_mod_ne_one

def fullRecordGapValue00816 : Nat := fullRecordGapCenterValue - 390378

theorem fullRecordGapTerm00816_eq_value :
    recordGapCenter - 390378 = fullRecordGapValue00816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00816 (fullRecordGapValue00816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00816_not_prime : ¬(recordGapCenter - 390378).Prime := by
  rw [fullRecordGapTerm00816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00816_fast_pow_mod_ne_one

def fullRecordGapValue00817 : Nat := fullRecordGapCenterValue - 390322

theorem fullRecordGapTerm00817_eq_value :
    recordGapCenter - 390322 = fullRecordGapValue00817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00817 (fullRecordGapValue00817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00817_not_prime : ¬(recordGapCenter - 390322).Prime := by
  rw [fullRecordGapTerm00817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00817_fast_pow_mod_ne_one

def fullRecordGapValue00818 : Nat := fullRecordGapCenterValue - 390154

theorem fullRecordGapTerm00818_eq_value :
    recordGapCenter - 390154 = fullRecordGapValue00818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00818 (fullRecordGapValue00818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00818_not_prime : ¬(recordGapCenter - 390154).Prime := by
  rw [fullRecordGapTerm00818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00818_fast_pow_mod_ne_one

def fullRecordGapValue00819 : Nat := fullRecordGapCenterValue - 390094

theorem fullRecordGapTerm00819_eq_value :
    recordGapCenter - 390094 = fullRecordGapValue00819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00819 (fullRecordGapValue00819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00819_not_prime : ¬(recordGapCenter - 390094).Prime := by
  rw [fullRecordGapTerm00819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00819_fast_pow_mod_ne_one

def fullRecordGapValue00820 : Nat := fullRecordGapCenterValue - 390088

theorem fullRecordGapTerm00820_eq_value :
    recordGapCenter - 390088 = fullRecordGapValue00820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00820 (fullRecordGapValue00820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00820_not_prime : ¬(recordGapCenter - 390088).Prime := by
  rw [fullRecordGapTerm00820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00820_fast_pow_mod_ne_one

def fullRecordGapValue00821 : Nat := fullRecordGapCenterValue - 389982

theorem fullRecordGapTerm00821_eq_value :
    recordGapCenter - 389982 = fullRecordGapValue00821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00821 (fullRecordGapValue00821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00821_not_prime : ¬(recordGapCenter - 389982).Prime := by
  rw [fullRecordGapTerm00821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00821_fast_pow_mod_ne_one

def fullRecordGapValue00822 : Nat := fullRecordGapCenterValue - 389814

theorem fullRecordGapTerm00822_eq_value :
    recordGapCenter - 389814 = fullRecordGapValue00822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00822 (fullRecordGapValue00822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00822_not_prime : ¬(recordGapCenter - 389814).Prime := by
  rw [fullRecordGapTerm00822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00822_fast_pow_mod_ne_one

def fullRecordGapValue00823 : Nat := fullRecordGapCenterValue - 389812

theorem fullRecordGapTerm00823_eq_value :
    recordGapCenter - 389812 = fullRecordGapValue00823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00823 (fullRecordGapValue00823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00823_not_prime : ¬(recordGapCenter - 389812).Prime := by
  rw [fullRecordGapTerm00823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00823_fast_pow_mod_ne_one

def fullRecordGapValue00824 : Nat := fullRecordGapCenterValue - 389622

theorem fullRecordGapTerm00824_eq_value :
    recordGapCenter - 389622 = fullRecordGapValue00824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00824 (fullRecordGapValue00824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00824_not_prime : ¬(recordGapCenter - 389622).Prime := by
  rw [fullRecordGapTerm00824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00824_fast_pow_mod_ne_one

def fullRecordGapValue00825 : Nat := fullRecordGapCenterValue - 389542

theorem fullRecordGapTerm00825_eq_value :
    recordGapCenter - 389542 = fullRecordGapValue00825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00825 (fullRecordGapValue00825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00825_not_prime : ¬(recordGapCenter - 389542).Prime := by
  rw [fullRecordGapTerm00825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00825_fast_pow_mod_ne_one

def fullRecordGapValue00826 : Nat := fullRecordGapCenterValue - 389434

theorem fullRecordGapTerm00826_eq_value :
    recordGapCenter - 389434 = fullRecordGapValue00826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00826 (fullRecordGapValue00826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00826_not_prime : ¬(recordGapCenter - 389434).Prime := by
  rw [fullRecordGapTerm00826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00826_fast_pow_mod_ne_one

def fullRecordGapValue00827 : Nat := fullRecordGapCenterValue - 389308

theorem fullRecordGapTerm00827_eq_value :
    recordGapCenter - 389308 = fullRecordGapValue00827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00827 (fullRecordGapValue00827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00827_not_prime : ¬(recordGapCenter - 389308).Prime := by
  rw [fullRecordGapTerm00827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00827_fast_pow_mod_ne_one

def fullRecordGapValue00828 : Nat := fullRecordGapCenterValue - 389274

theorem fullRecordGapTerm00828_eq_value :
    recordGapCenter - 389274 = fullRecordGapValue00828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00828 (fullRecordGapValue00828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00828_not_prime : ¬(recordGapCenter - 389274).Prime := by
  rw [fullRecordGapTerm00828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00828_fast_pow_mod_ne_one

def fullRecordGapValue00829 : Nat := fullRecordGapCenterValue - 389262

theorem fullRecordGapTerm00829_eq_value :
    recordGapCenter - 389262 = fullRecordGapValue00829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00829 (fullRecordGapValue00829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00829_not_prime : ¬(recordGapCenter - 389262).Prime := by
  rw [fullRecordGapTerm00829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00829_fast_pow_mod_ne_one

def fullRecordGapValue00830 : Nat := fullRecordGapCenterValue - 389218

theorem fullRecordGapTerm00830_eq_value :
    recordGapCenter - 389218 = fullRecordGapValue00830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00830 (fullRecordGapValue00830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00830_not_prime : ¬(recordGapCenter - 389218).Prime := by
  rw [fullRecordGapTerm00830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00830_fast_pow_mod_ne_one

def fullRecordGapValue00831 : Nat := fullRecordGapCenterValue - 389212

theorem fullRecordGapTerm00831_eq_value :
    recordGapCenter - 389212 = fullRecordGapValue00831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00831 (fullRecordGapValue00831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00831_not_prime : ¬(recordGapCenter - 389212).Prime := by
  rw [fullRecordGapTerm00831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00831_fast_pow_mod_ne_one

def fullRecordGapValue00832 : Nat := fullRecordGapCenterValue - 389182

theorem fullRecordGapTerm00832_eq_value :
    recordGapCenter - 389182 = fullRecordGapValue00832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00832 (fullRecordGapValue00832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00832_not_prime : ¬(recordGapCenter - 389182).Prime := by
  rw [fullRecordGapTerm00832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00832_fast_pow_mod_ne_one

def fullRecordGapValue00833 : Nat := fullRecordGapCenterValue - 389014

theorem fullRecordGapTerm00833_eq_value :
    recordGapCenter - 389014 = fullRecordGapValue00833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00833 (fullRecordGapValue00833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00833_not_prime : ¬(recordGapCenter - 389014).Prime := by
  rw [fullRecordGapTerm00833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00833_fast_pow_mod_ne_one

def fullRecordGapValue00834 : Nat := fullRecordGapCenterValue - 388924

theorem fullRecordGapTerm00834_eq_value :
    recordGapCenter - 388924 = fullRecordGapValue00834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00834 (fullRecordGapValue00834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00834_not_prime : ¬(recordGapCenter - 388924).Prime := by
  rw [fullRecordGapTerm00834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00834_fast_pow_mod_ne_one

def fullRecordGapValue00835 : Nat := fullRecordGapCenterValue - 388902

theorem fullRecordGapTerm00835_eq_value :
    recordGapCenter - 388902 = fullRecordGapValue00835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00835 (fullRecordGapValue00835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00835_not_prime : ¬(recordGapCenter - 388902).Prime := by
  rw [fullRecordGapTerm00835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00835_fast_pow_mod_ne_one

def fullRecordGapValue00836 : Nat := fullRecordGapCenterValue - 388758

theorem fullRecordGapTerm00836_eq_value :
    recordGapCenter - 388758 = fullRecordGapValue00836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00836 (fullRecordGapValue00836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00836_not_prime : ¬(recordGapCenter - 388758).Prime := by
  rw [fullRecordGapTerm00836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00836_fast_pow_mod_ne_one

def fullRecordGapValue00837 : Nat := fullRecordGapCenterValue - 388684

theorem fullRecordGapTerm00837_eq_value :
    recordGapCenter - 388684 = fullRecordGapValue00837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00837 (fullRecordGapValue00837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00837_not_prime : ¬(recordGapCenter - 388684).Prime := by
  rw [fullRecordGapTerm00837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00837_fast_pow_mod_ne_one

def fullRecordGapValue00838 : Nat := fullRecordGapCenterValue - 388618

theorem fullRecordGapTerm00838_eq_value :
    recordGapCenter - 388618 = fullRecordGapValue00838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00838 (fullRecordGapValue00838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00838_not_prime : ¬(recordGapCenter - 388618).Prime := by
  rw [fullRecordGapTerm00838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00838_fast_pow_mod_ne_one

def fullRecordGapValue00839 : Nat := fullRecordGapCenterValue - 388468

theorem fullRecordGapTerm00839_eq_value :
    recordGapCenter - 388468 = fullRecordGapValue00839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00839 (fullRecordGapValue00839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00839_not_prime : ¬(recordGapCenter - 388468).Prime := by
  rw [fullRecordGapTerm00839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00839_fast_pow_mod_ne_one

def fullRecordGapValue00840 : Nat := fullRecordGapCenterValue - 388302

theorem fullRecordGapTerm00840_eq_value :
    recordGapCenter - 388302 = fullRecordGapValue00840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00840 (fullRecordGapValue00840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00840_not_prime : ¬(recordGapCenter - 388302).Prime := by
  rw [fullRecordGapTerm00840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00840_fast_pow_mod_ne_one

def fullRecordGapValue00841 : Nat := fullRecordGapCenterValue - 388080

theorem fullRecordGapTerm00841_eq_value :
    recordGapCenter - 388080 = fullRecordGapValue00841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00841 (fullRecordGapValue00841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00841_not_prime : ¬(recordGapCenter - 388080).Prime := by
  rw [fullRecordGapTerm00841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00841_fast_pow_mod_ne_one

def fullRecordGapValue00842 : Nat := fullRecordGapCenterValue - 388012

theorem fullRecordGapTerm00842_eq_value :
    recordGapCenter - 388012 = fullRecordGapValue00842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00842 (fullRecordGapValue00842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00842_not_prime : ¬(recordGapCenter - 388012).Prime := by
  rw [fullRecordGapTerm00842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00842_fast_pow_mod_ne_one

def fullRecordGapValue00843 : Nat := fullRecordGapCenterValue - 388002

theorem fullRecordGapTerm00843_eq_value :
    recordGapCenter - 388002 = fullRecordGapValue00843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00843 (fullRecordGapValue00843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00843_not_prime : ¬(recordGapCenter - 388002).Prime := by
  rw [fullRecordGapTerm00843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00843_fast_pow_mod_ne_one

def fullRecordGapValue00844 : Nat := fullRecordGapCenterValue - 387988

theorem fullRecordGapTerm00844_eq_value :
    recordGapCenter - 387988 = fullRecordGapValue00844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00844 (fullRecordGapValue00844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00844_not_prime : ¬(recordGapCenter - 387988).Prime := by
  rw [fullRecordGapTerm00844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00844_fast_pow_mod_ne_one

def fullRecordGapValue00845 : Nat := fullRecordGapCenterValue - 387978

theorem fullRecordGapTerm00845_eq_value :
    recordGapCenter - 387978 = fullRecordGapValue00845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00845 (fullRecordGapValue00845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00845_not_prime : ¬(recordGapCenter - 387978).Prime := by
  rw [fullRecordGapTerm00845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00845_fast_pow_mod_ne_one

def fullRecordGapValue00846 : Nat := fullRecordGapCenterValue - 387874

theorem fullRecordGapTerm00846_eq_value :
    recordGapCenter - 387874 = fullRecordGapValue00846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00846 (fullRecordGapValue00846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00846_not_prime : ¬(recordGapCenter - 387874).Prime := by
  rw [fullRecordGapTerm00846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00846_fast_pow_mod_ne_one

def fullRecordGapValue00847 : Nat := fullRecordGapCenterValue - 387832

theorem fullRecordGapTerm00847_eq_value :
    recordGapCenter - 387832 = fullRecordGapValue00847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00847 (fullRecordGapValue00847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00847_not_prime : ¬(recordGapCenter - 387832).Prime := by
  rw [fullRecordGapTerm00847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00847_fast_pow_mod_ne_one

def fullRecordGapValue00848 : Nat := fullRecordGapCenterValue - 387784

theorem fullRecordGapTerm00848_eq_value :
    recordGapCenter - 387784 = fullRecordGapValue00848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00848 (fullRecordGapValue00848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00848_not_prime : ¬(recordGapCenter - 387784).Prime := by
  rw [fullRecordGapTerm00848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00848_fast_pow_mod_ne_one

def fullRecordGapValue00849 : Nat := fullRecordGapCenterValue - 387762

theorem fullRecordGapTerm00849_eq_value :
    recordGapCenter - 387762 = fullRecordGapValue00849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00849 (fullRecordGapValue00849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00849_not_prime : ¬(recordGapCenter - 387762).Prime := by
  rw [fullRecordGapTerm00849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00849_fast_pow_mod_ne_one

def fullRecordGapValue00850 : Nat := fullRecordGapCenterValue - 387742

theorem fullRecordGapTerm00850_eq_value :
    recordGapCenter - 387742 = fullRecordGapValue00850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00850 (fullRecordGapValue00850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00850_not_prime : ¬(recordGapCenter - 387742).Prime := by
  rw [fullRecordGapTerm00850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00850_fast_pow_mod_ne_one

def fullRecordGapValue00851 : Nat := fullRecordGapCenterValue - 387694

theorem fullRecordGapTerm00851_eq_value :
    recordGapCenter - 387694 = fullRecordGapValue00851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00851 (fullRecordGapValue00851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00851_not_prime : ¬(recordGapCenter - 387694).Prime := by
  rw [fullRecordGapTerm00851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00851_fast_pow_mod_ne_one

def fullRecordGapValue00852 : Nat := fullRecordGapCenterValue - 387592

theorem fullRecordGapTerm00852_eq_value :
    recordGapCenter - 387592 = fullRecordGapValue00852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00852 (fullRecordGapValue00852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00852_not_prime : ¬(recordGapCenter - 387592).Prime := by
  rw [fullRecordGapTerm00852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00852_fast_pow_mod_ne_one

def fullRecordGapValue00853 : Nat := fullRecordGapCenterValue - 387298

theorem fullRecordGapTerm00853_eq_value :
    recordGapCenter - 387298 = fullRecordGapValue00853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00853 (fullRecordGapValue00853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00853_not_prime : ¬(recordGapCenter - 387298).Prime := by
  rw [fullRecordGapTerm00853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00853_fast_pow_mod_ne_one

def fullRecordGapValue00854 : Nat := fullRecordGapCenterValue - 387238

theorem fullRecordGapTerm00854_eq_value :
    recordGapCenter - 387238 = fullRecordGapValue00854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00854 (fullRecordGapValue00854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00854_not_prime : ¬(recordGapCenter - 387238).Prime := by
  rw [fullRecordGapTerm00854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00854_fast_pow_mod_ne_one

def fullRecordGapValue00855 : Nat := fullRecordGapCenterValue - 387154

theorem fullRecordGapTerm00855_eq_value :
    recordGapCenter - 387154 = fullRecordGapValue00855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00855 (fullRecordGapValue00855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00855_not_prime : ¬(recordGapCenter - 387154).Prime := by
  rw [fullRecordGapTerm00855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00855_fast_pow_mod_ne_one

def fullRecordGapValue00856 : Nat := fullRecordGapCenterValue - 387118

theorem fullRecordGapTerm00856_eq_value :
    recordGapCenter - 387118 = fullRecordGapValue00856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00856 (fullRecordGapValue00856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00856_not_prime : ¬(recordGapCenter - 387118).Prime := by
  rw [fullRecordGapTerm00856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00856_fast_pow_mod_ne_one

def fullRecordGapValue00857 : Nat := fullRecordGapCenterValue - 387082

theorem fullRecordGapTerm00857_eq_value :
    recordGapCenter - 387082 = fullRecordGapValue00857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00857 (fullRecordGapValue00857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00857_not_prime : ¬(recordGapCenter - 387082).Prime := by
  rw [fullRecordGapTerm00857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00857_fast_pow_mod_ne_one

def fullRecordGapValue00858 : Nat := fullRecordGapCenterValue - 386994

theorem fullRecordGapTerm00858_eq_value :
    recordGapCenter - 386994 = fullRecordGapValue00858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00858 (fullRecordGapValue00858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00858_not_prime : ¬(recordGapCenter - 386994).Prime := by
  rw [fullRecordGapTerm00858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00858_fast_pow_mod_ne_one

def fullRecordGapValue00859 : Nat := fullRecordGapCenterValue - 386938

theorem fullRecordGapTerm00859_eq_value :
    recordGapCenter - 386938 = fullRecordGapValue00859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00859 (fullRecordGapValue00859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00859_not_prime : ¬(recordGapCenter - 386938).Prime := by
  rw [fullRecordGapTerm00859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00859_fast_pow_mod_ne_one

def fullRecordGapValue00860 : Nat := fullRecordGapCenterValue - 386934

theorem fullRecordGapTerm00860_eq_value :
    recordGapCenter - 386934 = fullRecordGapValue00860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00860 (fullRecordGapValue00860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00860_not_prime : ¬(recordGapCenter - 386934).Prime := by
  rw [fullRecordGapTerm00860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00860_fast_pow_mod_ne_one

def fullRecordGapValue00861 : Nat := fullRecordGapCenterValue - 386788

theorem fullRecordGapTerm00861_eq_value :
    recordGapCenter - 386788 = fullRecordGapValue00861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00861 (fullRecordGapValue00861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00861_not_prime : ¬(recordGapCenter - 386788).Prime := by
  rw [fullRecordGapTerm00861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00861_fast_pow_mod_ne_one

def fullRecordGapValue00862 : Nat := fullRecordGapCenterValue - 386734

theorem fullRecordGapTerm00862_eq_value :
    recordGapCenter - 386734 = fullRecordGapValue00862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00862 (fullRecordGapValue00862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00862_not_prime : ¬(recordGapCenter - 386734).Prime := by
  rw [fullRecordGapTerm00862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00862_fast_pow_mod_ne_one

def fullRecordGapValue00863 : Nat := fullRecordGapCenterValue - 386728

theorem fullRecordGapTerm00863_eq_value :
    recordGapCenter - 386728 = fullRecordGapValue00863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00863 (fullRecordGapValue00863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00863_not_prime : ¬(recordGapCenter - 386728).Prime := by
  rw [fullRecordGapTerm00863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00863_fast_pow_mod_ne_one

def fullRecordGapValue00864 : Nat := fullRecordGapCenterValue - 386668

theorem fullRecordGapTerm00864_eq_value :
    recordGapCenter - 386668 = fullRecordGapValue00864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00864 (fullRecordGapValue00864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00864_not_prime : ¬(recordGapCenter - 386668).Prime := by
  rw [fullRecordGapTerm00864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00864_fast_pow_mod_ne_one

def fullRecordGapValue00865 : Nat := fullRecordGapCenterValue - 386572

theorem fullRecordGapTerm00865_eq_value :
    recordGapCenter - 386572 = fullRecordGapValue00865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00865 (fullRecordGapValue00865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00865_not_prime : ¬(recordGapCenter - 386572).Prime := by
  rw [fullRecordGapTerm00865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00865_fast_pow_mod_ne_one

def fullRecordGapValue00866 : Nat := fullRecordGapCenterValue - 386494

theorem fullRecordGapTerm00866_eq_value :
    recordGapCenter - 386494 = fullRecordGapValue00866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00866 (fullRecordGapValue00866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00866_not_prime : ¬(recordGapCenter - 386494).Prime := by
  rw [fullRecordGapTerm00866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00866_fast_pow_mod_ne_one

def fullRecordGapValue00867 : Nat := fullRecordGapCenterValue - 386488

theorem fullRecordGapTerm00867_eq_value :
    recordGapCenter - 386488 = fullRecordGapValue00867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00867 (fullRecordGapValue00867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00867_not_prime : ¬(recordGapCenter - 386488).Prime := by
  rw [fullRecordGapTerm00867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00867_fast_pow_mod_ne_one

def fullRecordGapValue00868 : Nat := fullRecordGapCenterValue - 386418

theorem fullRecordGapTerm00868_eq_value :
    recordGapCenter - 386418 = fullRecordGapValue00868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00868 (fullRecordGapValue00868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00868_not_prime : ¬(recordGapCenter - 386418).Prime := by
  rw [fullRecordGapTerm00868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00868_fast_pow_mod_ne_one

def fullRecordGapValue00869 : Nat := fullRecordGapCenterValue - 386392

theorem fullRecordGapTerm00869_eq_value :
    recordGapCenter - 386392 = fullRecordGapValue00869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00869 (fullRecordGapValue00869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00869_not_prime : ¬(recordGapCenter - 386392).Prime := by
  rw [fullRecordGapTerm00869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00869_fast_pow_mod_ne_one

def fullRecordGapValue00870 : Nat := fullRecordGapCenterValue - 386362

theorem fullRecordGapTerm00870_eq_value :
    recordGapCenter - 386362 = fullRecordGapValue00870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00870 (fullRecordGapValue00870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00870_not_prime : ¬(recordGapCenter - 386362).Prime := by
  rw [fullRecordGapTerm00870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00870_fast_pow_mod_ne_one

def fullRecordGapValue00871 : Nat := fullRecordGapCenterValue - 386278

theorem fullRecordGapTerm00871_eq_value :
    recordGapCenter - 386278 = fullRecordGapValue00871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00871 (fullRecordGapValue00871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00871_not_prime : ¬(recordGapCenter - 386278).Prime := by
  rw [fullRecordGapTerm00871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00871_fast_pow_mod_ne_one

def fullRecordGapValue00872 : Nat := fullRecordGapCenterValue - 386248

theorem fullRecordGapTerm00872_eq_value :
    recordGapCenter - 386248 = fullRecordGapValue00872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00872 (fullRecordGapValue00872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00872_not_prime : ¬(recordGapCenter - 386248).Prime := by
  rw [fullRecordGapTerm00872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00872_fast_pow_mod_ne_one

def fullRecordGapValue00873 : Nat := fullRecordGapCenterValue - 386238

theorem fullRecordGapTerm00873_eq_value :
    recordGapCenter - 386238 = fullRecordGapValue00873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00873 (fullRecordGapValue00873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00873_not_prime : ¬(recordGapCenter - 386238).Prime := by
  rw [fullRecordGapTerm00873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00873_fast_pow_mod_ne_one

def fullRecordGapValue00874 : Nat := fullRecordGapCenterValue - 386068

theorem fullRecordGapTerm00874_eq_value :
    recordGapCenter - 386068 = fullRecordGapValue00874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00874 (fullRecordGapValue00874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00874_not_prime : ¬(recordGapCenter - 386068).Prime := by
  rw [fullRecordGapTerm00874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00874_fast_pow_mod_ne_one

def fullRecordGapValue00875 : Nat := fullRecordGapCenterValue - 385998

theorem fullRecordGapTerm00875_eq_value :
    recordGapCenter - 385998 = fullRecordGapValue00875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00875 (fullRecordGapValue00875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00875_not_prime : ¬(recordGapCenter - 385998).Prime := by
  rw [fullRecordGapTerm00875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00875_fast_pow_mod_ne_one

def fullRecordGapValue00876 : Nat := fullRecordGapCenterValue - 385948

theorem fullRecordGapTerm00876_eq_value :
    recordGapCenter - 385948 = fullRecordGapValue00876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00876 (fullRecordGapValue00876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00876_not_prime : ¬(recordGapCenter - 385948).Prime := by
  rw [fullRecordGapTerm00876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00876_fast_pow_mod_ne_one

def fullRecordGapValue00877 : Nat := fullRecordGapCenterValue - 385942

theorem fullRecordGapTerm00877_eq_value :
    recordGapCenter - 385942 = fullRecordGapValue00877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00877 (fullRecordGapValue00877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00877_not_prime : ¬(recordGapCenter - 385942).Prime := by
  rw [fullRecordGapTerm00877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00877_fast_pow_mod_ne_one

def fullRecordGapValue00878 : Nat := fullRecordGapCenterValue - 385912

theorem fullRecordGapTerm00878_eq_value :
    recordGapCenter - 385912 = fullRecordGapValue00878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00878 (fullRecordGapValue00878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00878_not_prime : ¬(recordGapCenter - 385912).Prime := by
  rw [fullRecordGapTerm00878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00878_fast_pow_mod_ne_one

def fullRecordGapValue00879 : Nat := fullRecordGapCenterValue - 385698

theorem fullRecordGapTerm00879_eq_value :
    recordGapCenter - 385698 = fullRecordGapValue00879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00879 (fullRecordGapValue00879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00879_not_prime : ¬(recordGapCenter - 385698).Prime := by
  rw [fullRecordGapTerm00879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00879_fast_pow_mod_ne_one

def fullRecordGapValue00880 : Nat := fullRecordGapCenterValue - 385674

theorem fullRecordGapTerm00880_eq_value :
    recordGapCenter - 385674 = fullRecordGapValue00880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00880 (fullRecordGapValue00880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00880_not_prime : ¬(recordGapCenter - 385674).Prime := by
  rw [fullRecordGapTerm00880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00880_fast_pow_mod_ne_one

def fullRecordGapValue00881 : Nat := fullRecordGapCenterValue - 385432

theorem fullRecordGapTerm00881_eq_value :
    recordGapCenter - 385432 = fullRecordGapValue00881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00881 (fullRecordGapValue00881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00881_not_prime : ¬(recordGapCenter - 385432).Prime := by
  rw [fullRecordGapTerm00881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00881_fast_pow_mod_ne_one

def fullRecordGapValue00882 : Nat := fullRecordGapCenterValue - 385348

theorem fullRecordGapTerm00882_eq_value :
    recordGapCenter - 385348 = fullRecordGapValue00882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00882 (fullRecordGapValue00882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00882_not_prime : ¬(recordGapCenter - 385348).Prime := by
  rw [fullRecordGapTerm00882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00882_fast_pow_mod_ne_one

def fullRecordGapValue00883 : Nat := fullRecordGapCenterValue - 385338

theorem fullRecordGapTerm00883_eq_value :
    recordGapCenter - 385338 = fullRecordGapValue00883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00883 (fullRecordGapValue00883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00883_not_prime : ¬(recordGapCenter - 385338).Prime := by
  rw [fullRecordGapTerm00883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00883_fast_pow_mod_ne_one

def fullRecordGapValue00884 : Nat := fullRecordGapCenterValue - 385324

theorem fullRecordGapTerm00884_eq_value :
    recordGapCenter - 385324 = fullRecordGapValue00884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00884 (fullRecordGapValue00884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00884_not_prime : ¬(recordGapCenter - 385324).Prime := by
  rw [fullRecordGapTerm00884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00884_fast_pow_mod_ne_one

def fullRecordGapValue00885 : Nat := fullRecordGapCenterValue - 385222

theorem fullRecordGapTerm00885_eq_value :
    recordGapCenter - 385222 = fullRecordGapValue00885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00885 (fullRecordGapValue00885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00885_not_prime : ¬(recordGapCenter - 385222).Prime := by
  rw [fullRecordGapTerm00885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00885_fast_pow_mod_ne_one

def fullRecordGapValue00886 : Nat := fullRecordGapCenterValue - 384918

theorem fullRecordGapTerm00886_eq_value :
    recordGapCenter - 384918 = fullRecordGapValue00886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00886 (fullRecordGapValue00886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00886_not_prime : ¬(recordGapCenter - 384918).Prime := by
  rw [fullRecordGapTerm00886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00886_fast_pow_mod_ne_one

def fullRecordGapValue00887 : Nat := fullRecordGapCenterValue - 384912

theorem fullRecordGapTerm00887_eq_value :
    recordGapCenter - 384912 = fullRecordGapValue00887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00887 (fullRecordGapValue00887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00887_not_prime : ¬(recordGapCenter - 384912).Prime := by
  rw [fullRecordGapTerm00887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00887_fast_pow_mod_ne_one

def fullRecordGapValue00888 : Nat := fullRecordGapCenterValue - 384862

theorem fullRecordGapTerm00888_eq_value :
    recordGapCenter - 384862 = fullRecordGapValue00888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00888 (fullRecordGapValue00888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00888_not_prime : ¬(recordGapCenter - 384862).Prime := by
  rw [fullRecordGapTerm00888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00888_fast_pow_mod_ne_one

def fullRecordGapValue00889 : Nat := fullRecordGapCenterValue - 384814

theorem fullRecordGapTerm00889_eq_value :
    recordGapCenter - 384814 = fullRecordGapValue00889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00889 (fullRecordGapValue00889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00889_not_prime : ¬(recordGapCenter - 384814).Prime := by
  rw [fullRecordGapTerm00889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00889_fast_pow_mod_ne_one

def fullRecordGapValue00890 : Nat := fullRecordGapCenterValue - 384694

theorem fullRecordGapTerm00890_eq_value :
    recordGapCenter - 384694 = fullRecordGapValue00890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00890 (fullRecordGapValue00890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00890_not_prime : ¬(recordGapCenter - 384694).Prime := by
  rw [fullRecordGapTerm00890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00890_fast_pow_mod_ne_one

def fullRecordGapValue00891 : Nat := fullRecordGapCenterValue - 384634

theorem fullRecordGapTerm00891_eq_value :
    recordGapCenter - 384634 = fullRecordGapValue00891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00891 (fullRecordGapValue00891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00891_not_prime : ¬(recordGapCenter - 384634).Prime := by
  rw [fullRecordGapTerm00891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00891_fast_pow_mod_ne_one

def fullRecordGapValue00892 : Nat := fullRecordGapCenterValue - 384628

theorem fullRecordGapTerm00892_eq_value :
    recordGapCenter - 384628 = fullRecordGapValue00892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00892 (fullRecordGapValue00892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00892_not_prime : ¬(recordGapCenter - 384628).Prime := by
  rw [fullRecordGapTerm00892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00892_fast_pow_mod_ne_one

def fullRecordGapValue00893 : Nat := fullRecordGapCenterValue - 384502

theorem fullRecordGapTerm00893_eq_value :
    recordGapCenter - 384502 = fullRecordGapValue00893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00893 (fullRecordGapValue00893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00893_not_prime : ¬(recordGapCenter - 384502).Prime := by
  rw [fullRecordGapTerm00893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00893_fast_pow_mod_ne_one

def fullRecordGapValue00894 : Nat := fullRecordGapCenterValue - 384478

theorem fullRecordGapTerm00894_eq_value :
    recordGapCenter - 384478 = fullRecordGapValue00894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00894 (fullRecordGapValue00894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00894_not_prime : ¬(recordGapCenter - 384478).Prime := by
  rw [fullRecordGapTerm00894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00894_fast_pow_mod_ne_one

def fullRecordGapValue00895 : Nat := fullRecordGapCenterValue - 384382

theorem fullRecordGapTerm00895_eq_value :
    recordGapCenter - 384382 = fullRecordGapValue00895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00895 (fullRecordGapValue00895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00895_not_prime : ¬(recordGapCenter - 384382).Prime := by
  rw [fullRecordGapTerm00895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00895_fast_pow_mod_ne_one

def fullRecordGapValue00896 : Nat := fullRecordGapCenterValue - 384232

theorem fullRecordGapTerm00896_eq_value :
    recordGapCenter - 384232 = fullRecordGapValue00896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00896 (fullRecordGapValue00896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00896_not_prime : ¬(recordGapCenter - 384232).Prime := by
  rw [fullRecordGapTerm00896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00896_fast_pow_mod_ne_one

def fullRecordGapValue00897 : Nat := fullRecordGapCenterValue - 384160

theorem fullRecordGapTerm00897_eq_value :
    recordGapCenter - 384160 = fullRecordGapValue00897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00897 (fullRecordGapValue00897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00897_not_prime : ¬(recordGapCenter - 384160).Prime := by
  rw [fullRecordGapTerm00897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00897_fast_pow_mod_ne_one

def fullRecordGapValue00898 : Nat := fullRecordGapCenterValue - 384094

theorem fullRecordGapTerm00898_eq_value :
    recordGapCenter - 384094 = fullRecordGapValue00898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00898 (fullRecordGapValue00898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00898_not_prime : ¬(recordGapCenter - 384094).Prime := by
  rw [fullRecordGapTerm00898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00898_fast_pow_mod_ne_one

def fullRecordGapValue00899 : Nat := fullRecordGapCenterValue - 384004

theorem fullRecordGapTerm00899_eq_value :
    recordGapCenter - 384004 = fullRecordGapValue00899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00899 (fullRecordGapValue00899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00899_not_prime : ¬(recordGapCenter - 384004).Prime := by
  rw [fullRecordGapTerm00899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00899_fast_pow_mod_ne_one

def fullRecordGapValue00900 : Nat := fullRecordGapCenterValue - 383998

theorem fullRecordGapTerm00900_eq_value :
    recordGapCenter - 383998 = fullRecordGapValue00900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00900 (fullRecordGapValue00900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00900_not_prime : ¬(recordGapCenter - 383998).Prime := by
  rw [fullRecordGapTerm00900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00900_fast_pow_mod_ne_one

def fullRecordGapValue00901 : Nat := fullRecordGapCenterValue - 383938

theorem fullRecordGapTerm00901_eq_value :
    recordGapCenter - 383938 = fullRecordGapValue00901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00901 (fullRecordGapValue00901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00901_not_prime : ¬(recordGapCenter - 383938).Prime := by
  rw [fullRecordGapTerm00901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00901_fast_pow_mod_ne_one

def fullRecordGapValue00902 : Nat := fullRecordGapCenterValue - 383862

theorem fullRecordGapTerm00902_eq_value :
    recordGapCenter - 383862 = fullRecordGapValue00902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00902 (fullRecordGapValue00902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00902_not_prime : ¬(recordGapCenter - 383862).Prime := by
  rw [fullRecordGapTerm00902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00902_fast_pow_mod_ne_one

def fullRecordGapValue00903 : Nat := fullRecordGapCenterValue - 383788

theorem fullRecordGapTerm00903_eq_value :
    recordGapCenter - 383788 = fullRecordGapValue00903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00903 (fullRecordGapValue00903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00903_not_prime : ¬(recordGapCenter - 383788).Prime := by
  rw [fullRecordGapTerm00903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00903_fast_pow_mod_ne_one

def fullRecordGapValue00904 : Nat := fullRecordGapCenterValue - 383752

theorem fullRecordGapTerm00904_eq_value :
    recordGapCenter - 383752 = fullRecordGapValue00904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00904 (fullRecordGapValue00904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00904_not_prime : ¬(recordGapCenter - 383752).Prime := by
  rw [fullRecordGapTerm00904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00904_fast_pow_mod_ne_one

def fullRecordGapValue00905 : Nat := fullRecordGapCenterValue - 383722

theorem fullRecordGapTerm00905_eq_value :
    recordGapCenter - 383722 = fullRecordGapValue00905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00905 (fullRecordGapValue00905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00905_not_prime : ¬(recordGapCenter - 383722).Prime := by
  rw [fullRecordGapTerm00905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00905_fast_pow_mod_ne_one

def fullRecordGapValue00906 : Nat := fullRecordGapCenterValue - 383694

theorem fullRecordGapTerm00906_eq_value :
    recordGapCenter - 383694 = fullRecordGapValue00906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00906 (fullRecordGapValue00906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00906_not_prime : ¬(recordGapCenter - 383694).Prime := by
  rw [fullRecordGapTerm00906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00906_fast_pow_mod_ne_one

def fullRecordGapValue00907 : Nat := fullRecordGapCenterValue - 383668

theorem fullRecordGapTerm00907_eq_value :
    recordGapCenter - 383668 = fullRecordGapValue00907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00907 (fullRecordGapValue00907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00907_not_prime : ¬(recordGapCenter - 383668).Prime := by
  rw [fullRecordGapTerm00907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00907_fast_pow_mod_ne_one

def fullRecordGapValue00908 : Nat := fullRecordGapCenterValue - 383512

theorem fullRecordGapTerm00908_eq_value :
    recordGapCenter - 383512 = fullRecordGapValue00908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00908 (fullRecordGapValue00908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00908_not_prime : ¬(recordGapCenter - 383512).Prime := by
  rw [fullRecordGapTerm00908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00908_fast_pow_mod_ne_one

def fullRecordGapValue00909 : Nat := fullRecordGapCenterValue - 383494

theorem fullRecordGapTerm00909_eq_value :
    recordGapCenter - 383494 = fullRecordGapValue00909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00909 (fullRecordGapValue00909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00909_not_prime : ¬(recordGapCenter - 383494).Prime := by
  rw [fullRecordGapTerm00909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00909_fast_pow_mod_ne_one

def fullRecordGapValue00910 : Nat := fullRecordGapCenterValue - 383434

theorem fullRecordGapTerm00910_eq_value :
    recordGapCenter - 383434 = fullRecordGapValue00910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00910 (fullRecordGapValue00910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00910_not_prime : ¬(recordGapCenter - 383434).Prime := by
  rw [fullRecordGapTerm00910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00910_fast_pow_mod_ne_one

def fullRecordGapValue00911 : Nat := fullRecordGapCenterValue - 383242

theorem fullRecordGapTerm00911_eq_value :
    recordGapCenter - 383242 = fullRecordGapValue00911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00911 (fullRecordGapValue00911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00911_not_prime : ¬(recordGapCenter - 383242).Prime := by
  rw [fullRecordGapTerm00911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00911_fast_pow_mod_ne_one

def fullRecordGapValue00912 : Nat := fullRecordGapCenterValue - 383224

theorem fullRecordGapTerm00912_eq_value :
    recordGapCenter - 383224 = fullRecordGapValue00912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00912 (fullRecordGapValue00912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00912_not_prime : ¬(recordGapCenter - 383224).Prime := by
  rw [fullRecordGapTerm00912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00912_fast_pow_mod_ne_one

def fullRecordGapValue00913 : Nat := fullRecordGapCenterValue - 383164

theorem fullRecordGapTerm00913_eq_value :
    recordGapCenter - 383164 = fullRecordGapValue00913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00913 (fullRecordGapValue00913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00913_not_prime : ¬(recordGapCenter - 383164).Prime := by
  rw [fullRecordGapTerm00913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00913_fast_pow_mod_ne_one

def fullRecordGapValue00914 : Nat := fullRecordGapCenterValue - 383158

theorem fullRecordGapTerm00914_eq_value :
    recordGapCenter - 383158 = fullRecordGapValue00914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00914 (fullRecordGapValue00914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00914_not_prime : ¬(recordGapCenter - 383158).Prime := by
  rw [fullRecordGapTerm00914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00914_fast_pow_mod_ne_one

def fullRecordGapValue00915 : Nat := fullRecordGapCenterValue - 383122

theorem fullRecordGapTerm00915_eq_value :
    recordGapCenter - 383122 = fullRecordGapValue00915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00915 (fullRecordGapValue00915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00915_not_prime : ¬(recordGapCenter - 383122).Prime := by
  rw [fullRecordGapTerm00915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00915_fast_pow_mod_ne_one

def fullRecordGapValue00916 : Nat := fullRecordGapCenterValue - 383074

theorem fullRecordGapTerm00916_eq_value :
    recordGapCenter - 383074 = fullRecordGapValue00916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00916 (fullRecordGapValue00916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00916_not_prime : ¬(recordGapCenter - 383074).Prime := by
  rw [fullRecordGapTerm00916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00916_fast_pow_mod_ne_one

def fullRecordGapValue00917 : Nat := fullRecordGapCenterValue - 383038

theorem fullRecordGapTerm00917_eq_value :
    recordGapCenter - 383038 = fullRecordGapValue00917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00917 (fullRecordGapValue00917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00917_not_prime : ¬(recordGapCenter - 383038).Prime := by
  rw [fullRecordGapTerm00917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00917_fast_pow_mod_ne_one

def fullRecordGapValue00918 : Nat := fullRecordGapCenterValue - 383014

theorem fullRecordGapTerm00918_eq_value :
    recordGapCenter - 383014 = fullRecordGapValue00918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00918 (fullRecordGapValue00918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00918_not_prime : ¬(recordGapCenter - 383014).Prime := by
  rw [fullRecordGapTerm00918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00918_fast_pow_mod_ne_one

def fullRecordGapValue00919 : Nat := fullRecordGapCenterValue - 382938

theorem fullRecordGapTerm00919_eq_value :
    recordGapCenter - 382938 = fullRecordGapValue00919 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00919_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00919 (fullRecordGapValue00919 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00919_not_prime : ¬(recordGapCenter - 382938).Prime := by
  rw [fullRecordGapTerm00919_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00919, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00919_fast_pow_mod_ne_one

def fullRecordGapValue00920 : Nat := fullRecordGapCenterValue - 382918

theorem fullRecordGapTerm00920_eq_value :
    recordGapCenter - 382918 = fullRecordGapValue00920 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00920_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00920 (fullRecordGapValue00920 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00920_not_prime : ¬(recordGapCenter - 382918).Prime := by
  rw [fullRecordGapTerm00920_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00920, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00920_fast_pow_mod_ne_one

def fullRecordGapValue00921 : Nat := fullRecordGapCenterValue - 382882

theorem fullRecordGapTerm00921_eq_value :
    recordGapCenter - 382882 = fullRecordGapValue00921 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00921_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00921 (fullRecordGapValue00921 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00921_not_prime : ¬(recordGapCenter - 382882).Prime := by
  rw [fullRecordGapTerm00921_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00921, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00921_fast_pow_mod_ne_one

def fullRecordGapValue00922 : Nat := fullRecordGapCenterValue - 382854

theorem fullRecordGapTerm00922_eq_value :
    recordGapCenter - 382854 = fullRecordGapValue00922 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00922_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00922 (fullRecordGapValue00922 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00922_not_prime : ¬(recordGapCenter - 382854).Prime := by
  rw [fullRecordGapTerm00922_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00922, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00922_fast_pow_mod_ne_one

def fullRecordGapValue00923 : Nat := fullRecordGapCenterValue - 382828

theorem fullRecordGapTerm00923_eq_value :
    recordGapCenter - 382828 = fullRecordGapValue00923 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00923_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00923 (fullRecordGapValue00923 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00923_not_prime : ¬(recordGapCenter - 382828).Prime := by
  rw [fullRecordGapTerm00923_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00923, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00923_fast_pow_mod_ne_one

def fullRecordGapValue00924 : Nat := fullRecordGapCenterValue - 382818

theorem fullRecordGapTerm00924_eq_value :
    recordGapCenter - 382818 = fullRecordGapValue00924 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00924_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00924 (fullRecordGapValue00924 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00924_not_prime : ¬(recordGapCenter - 382818).Prime := by
  rw [fullRecordGapTerm00924_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00924, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00924_fast_pow_mod_ne_one

def fullRecordGapValue00925 : Nat := fullRecordGapCenterValue - 382758

theorem fullRecordGapTerm00925_eq_value :
    recordGapCenter - 382758 = fullRecordGapValue00925 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00925_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00925 (fullRecordGapValue00925 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00925_not_prime : ¬(recordGapCenter - 382758).Prime := by
  rw [fullRecordGapTerm00925_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00925, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00925_fast_pow_mod_ne_one

def fullRecordGapValue00926 : Nat := fullRecordGapCenterValue - 382638

theorem fullRecordGapTerm00926_eq_value :
    recordGapCenter - 382638 = fullRecordGapValue00926 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00926_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00926 (fullRecordGapValue00926 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00926_not_prime : ¬(recordGapCenter - 382638).Prime := by
  rw [fullRecordGapTerm00926_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00926, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00926_fast_pow_mod_ne_one

def fullRecordGapValue00927 : Nat := fullRecordGapCenterValue - 382498

theorem fullRecordGapTerm00927_eq_value :
    recordGapCenter - 382498 = fullRecordGapValue00927 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00927_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00927 (fullRecordGapValue00927 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00927_not_prime : ¬(recordGapCenter - 382498).Prime := by
  rw [fullRecordGapTerm00927_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00927, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00927_fast_pow_mod_ne_one

def fullRecordGapValue00928 : Nat := fullRecordGapCenterValue - 382314

theorem fullRecordGapTerm00928_eq_value :
    recordGapCenter - 382314 = fullRecordGapValue00928 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00928_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00928 (fullRecordGapValue00928 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00928_not_prime : ¬(recordGapCenter - 382314).Prime := by
  rw [fullRecordGapTerm00928_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00928, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00928_fast_pow_mod_ne_one

def fullRecordGapValue00929 : Nat := fullRecordGapCenterValue - 382218

theorem fullRecordGapTerm00929_eq_value :
    recordGapCenter - 382218 = fullRecordGapValue00929 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00929_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00929 (fullRecordGapValue00929 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00929_not_prime : ¬(recordGapCenter - 382218).Prime := by
  rw [fullRecordGapTerm00929_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00929, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00929_fast_pow_mod_ne_one

def fullRecordGapValue00930 : Nat := fullRecordGapCenterValue - 382198

theorem fullRecordGapTerm00930_eq_value :
    recordGapCenter - 382198 = fullRecordGapValue00930 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00930_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00930 (fullRecordGapValue00930 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00930_not_prime : ¬(recordGapCenter - 382198).Prime := by
  rw [fullRecordGapTerm00930_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00930, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00930_fast_pow_mod_ne_one

def fullRecordGapValue00931 : Nat := fullRecordGapCenterValue - 382042

theorem fullRecordGapTerm00931_eq_value :
    recordGapCenter - 382042 = fullRecordGapValue00931 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00931_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00931 (fullRecordGapValue00931 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00931_not_prime : ¬(recordGapCenter - 382042).Prime := by
  rw [fullRecordGapTerm00931_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00931, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00931_fast_pow_mod_ne_one

def fullRecordGapValue00932 : Nat := fullRecordGapCenterValue - 381958

theorem fullRecordGapTerm00932_eq_value :
    recordGapCenter - 381958 = fullRecordGapValue00932 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00932_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00932 (fullRecordGapValue00932 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00932_not_prime : ¬(recordGapCenter - 381958).Prime := by
  rw [fullRecordGapTerm00932_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00932, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00932_fast_pow_mod_ne_one

def fullRecordGapValue00933 : Nat := fullRecordGapCenterValue - 381954

theorem fullRecordGapTerm00933_eq_value :
    recordGapCenter - 381954 = fullRecordGapValue00933 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00933_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00933 (fullRecordGapValue00933 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00933_not_prime : ¬(recordGapCenter - 381954).Prime := by
  rw [fullRecordGapTerm00933_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00933, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00933_fast_pow_mod_ne_one

def fullRecordGapValue00934 : Nat := fullRecordGapCenterValue - 381882

theorem fullRecordGapTerm00934_eq_value :
    recordGapCenter - 381882 = fullRecordGapValue00934 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00934_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00934 (fullRecordGapValue00934 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00934_not_prime : ¬(recordGapCenter - 381882).Prime := by
  rw [fullRecordGapTerm00934_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00934, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00934_fast_pow_mod_ne_one

def fullRecordGapValue00935 : Nat := fullRecordGapCenterValue - 381778

theorem fullRecordGapTerm00935_eq_value :
    recordGapCenter - 381778 = fullRecordGapValue00935 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00935_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00935 (fullRecordGapValue00935 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00935_not_prime : ¬(recordGapCenter - 381778).Prime := by
  rw [fullRecordGapTerm00935_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00935, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00935_fast_pow_mod_ne_one

def fullRecordGapValue00936 : Nat := fullRecordGapCenterValue - 381772

theorem fullRecordGapTerm00936_eq_value :
    recordGapCenter - 381772 = fullRecordGapValue00936 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00936_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00936 (fullRecordGapValue00936 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00936_not_prime : ¬(recordGapCenter - 381772).Prime := by
  rw [fullRecordGapTerm00936_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00936, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00936_fast_pow_mod_ne_one

def fullRecordGapValue00937 : Nat := fullRecordGapCenterValue - 381742

theorem fullRecordGapTerm00937_eq_value :
    recordGapCenter - 381742 = fullRecordGapValue00937 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00937_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00937 (fullRecordGapValue00937 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00937_not_prime : ¬(recordGapCenter - 381742).Prime := by
  rw [fullRecordGapTerm00937_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00937, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00937_fast_pow_mod_ne_one

def fullRecordGapValue00938 : Nat := fullRecordGapCenterValue - 381688

theorem fullRecordGapTerm00938_eq_value :
    recordGapCenter - 381688 = fullRecordGapValue00938 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00938_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00938 (fullRecordGapValue00938 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00938_not_prime : ¬(recordGapCenter - 381688).Prime := by
  rw [fullRecordGapTerm00938_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00938, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00938_fast_pow_mod_ne_one

def fullRecordGapValue00939 : Nat := fullRecordGapCenterValue - 381642

theorem fullRecordGapTerm00939_eq_value :
    recordGapCenter - 381642 = fullRecordGapValue00939 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00939_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00939 (fullRecordGapValue00939 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00939_not_prime : ¬(recordGapCenter - 381642).Prime := by
  rw [fullRecordGapTerm00939_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00939, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00939_fast_pow_mod_ne_one

def fullRecordGapValue00940 : Nat := fullRecordGapCenterValue - 381622

theorem fullRecordGapTerm00940_eq_value :
    recordGapCenter - 381622 = fullRecordGapValue00940 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00940_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00940 (fullRecordGapValue00940 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00940_not_prime : ¬(recordGapCenter - 381622).Prime := by
  rw [fullRecordGapTerm00940_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00940, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00940_fast_pow_mod_ne_one

def fullRecordGapValue00941 : Nat := fullRecordGapCenterValue - 381574

theorem fullRecordGapTerm00941_eq_value :
    recordGapCenter - 381574 = fullRecordGapValue00941 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00941_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00941 (fullRecordGapValue00941 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00941_not_prime : ¬(recordGapCenter - 381574).Prime := by
  rw [fullRecordGapTerm00941_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00941, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00941_fast_pow_mod_ne_one

def fullRecordGapValue00942 : Nat := fullRecordGapCenterValue - 381538

theorem fullRecordGapTerm00942_eq_value :
    recordGapCenter - 381538 = fullRecordGapValue00942 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00942_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00942 (fullRecordGapValue00942 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00942_not_prime : ¬(recordGapCenter - 381538).Prime := by
  rw [fullRecordGapTerm00942_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00942, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00942_fast_pow_mod_ne_one

def fullRecordGapValue00943 : Nat := fullRecordGapCenterValue - 381534

theorem fullRecordGapTerm00943_eq_value :
    recordGapCenter - 381534 = fullRecordGapValue00943 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00943_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00943 (fullRecordGapValue00943 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00943_not_prime : ¬(recordGapCenter - 381534).Prime := by
  rw [fullRecordGapTerm00943_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00943, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00943_fast_pow_mod_ne_one

def fullRecordGapValue00944 : Nat := fullRecordGapCenterValue - 381268

theorem fullRecordGapTerm00944_eq_value :
    recordGapCenter - 381268 = fullRecordGapValue00944 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00944_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00944 (fullRecordGapValue00944 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00944_not_prime : ¬(recordGapCenter - 381268).Prime := by
  rw [fullRecordGapTerm00944_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00944, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00944_fast_pow_mod_ne_one

def fullRecordGapValue00945 : Nat := fullRecordGapCenterValue - 381162

theorem fullRecordGapTerm00945_eq_value :
    recordGapCenter - 381162 = fullRecordGapValue00945 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00945_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00945 (fullRecordGapValue00945 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00945_not_prime : ¬(recordGapCenter - 381162).Prime := by
  rw [fullRecordGapTerm00945_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00945, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00945_fast_pow_mod_ne_one

def fullRecordGapValue00946 : Nat := fullRecordGapCenterValue - 381112

theorem fullRecordGapTerm00946_eq_value :
    recordGapCenter - 381112 = fullRecordGapValue00946 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00946_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00946 (fullRecordGapValue00946 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00946_not_prime : ¬(recordGapCenter - 381112).Prime := by
  rw [fullRecordGapTerm00946_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00946, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00946_fast_pow_mod_ne_one

def fullRecordGapValue00947 : Nat := fullRecordGapCenterValue - 381024

theorem fullRecordGapTerm00947_eq_value :
    recordGapCenter - 381024 = fullRecordGapValue00947 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00947_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00947 (fullRecordGapValue00947 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00947_not_prime : ¬(recordGapCenter - 381024).Prime := by
  rw [fullRecordGapTerm00947_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00947, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00947_fast_pow_mod_ne_one

def fullRecordGapValue00948 : Nat := fullRecordGapCenterValue - 380838

theorem fullRecordGapTerm00948_eq_value :
    recordGapCenter - 380838 = fullRecordGapValue00948 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00948_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00948 (fullRecordGapValue00948 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00948_not_prime : ¬(recordGapCenter - 380838).Prime := by
  rw [fullRecordGapTerm00948_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00948, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00948_fast_pow_mod_ne_one

def fullRecordGapValue00949 : Nat := fullRecordGapCenterValue - 380818

theorem fullRecordGapTerm00949_eq_value :
    recordGapCenter - 380818 = fullRecordGapValue00949 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00949_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00949 (fullRecordGapValue00949 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00949_not_prime : ¬(recordGapCenter - 380818).Prime := by
  rw [fullRecordGapTerm00949_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00949, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00949_fast_pow_mod_ne_one

def fullRecordGapValue00950 : Nat := fullRecordGapCenterValue - 380572

theorem fullRecordGapTerm00950_eq_value :
    recordGapCenter - 380572 = fullRecordGapValue00950 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00950_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00950 (fullRecordGapValue00950 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00950_not_prime : ¬(recordGapCenter - 380572).Prime := by
  rw [fullRecordGapTerm00950_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00950, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00950_fast_pow_mod_ne_one

def fullRecordGapValue00951 : Nat := fullRecordGapCenterValue - 380524

theorem fullRecordGapTerm00951_eq_value :
    recordGapCenter - 380524 = fullRecordGapValue00951 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00951_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00951 (fullRecordGapValue00951 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00951_not_prime : ¬(recordGapCenter - 380524).Prime := by
  rw [fullRecordGapTerm00951_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00951, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00951_fast_pow_mod_ne_one

def fullRecordGapValue00952 : Nat := fullRecordGapCenterValue - 380454

theorem fullRecordGapTerm00952_eq_value :
    recordGapCenter - 380454 = fullRecordGapValue00952 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00952_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00952 (fullRecordGapValue00952 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00952_not_prime : ¬(recordGapCenter - 380454).Prime := by
  rw [fullRecordGapTerm00952_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00952, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00952_fast_pow_mod_ne_one

def fullRecordGapValue00953 : Nat := fullRecordGapCenterValue - 380382

theorem fullRecordGapTerm00953_eq_value :
    recordGapCenter - 380382 = fullRecordGapValue00953 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00953_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00953 (fullRecordGapValue00953 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00953_not_prime : ¬(recordGapCenter - 380382).Prime := by
  rw [fullRecordGapTerm00953_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00953, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00953_fast_pow_mod_ne_one

def fullRecordGapValue00954 : Nat := fullRecordGapCenterValue - 380344

theorem fullRecordGapTerm00954_eq_value :
    recordGapCenter - 380344 = fullRecordGapValue00954 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00954_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00954 (fullRecordGapValue00954 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00954_not_prime : ¬(recordGapCenter - 380344).Prime := by
  rw [fullRecordGapTerm00954_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00954, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00954_fast_pow_mod_ne_one

def fullRecordGapValue00955 : Nat := fullRecordGapCenterValue - 380334

theorem fullRecordGapTerm00955_eq_value :
    recordGapCenter - 380334 = fullRecordGapValue00955 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00955_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00955 (fullRecordGapValue00955 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00955_not_prime : ¬(recordGapCenter - 380334).Prime := by
  rw [fullRecordGapTerm00955_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00955, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00955_fast_pow_mod_ne_one

def fullRecordGapValue00956 : Nat := fullRecordGapCenterValue - 380284

theorem fullRecordGapTerm00956_eq_value :
    recordGapCenter - 380284 = fullRecordGapValue00956 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00956_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00956 (fullRecordGapValue00956 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00956_not_prime : ¬(recordGapCenter - 380284).Prime := by
  rw [fullRecordGapTerm00956_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00956, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00956_fast_pow_mod_ne_one

def fullRecordGapValue00957 : Nat := fullRecordGapCenterValue - 380242

theorem fullRecordGapTerm00957_eq_value :
    recordGapCenter - 380242 = fullRecordGapValue00957 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00957_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00957 (fullRecordGapValue00957 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00957_not_prime : ¬(recordGapCenter - 380242).Prime := by
  rw [fullRecordGapTerm00957_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00957, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00957_fast_pow_mod_ne_one

def fullRecordGapValue00958 : Nat := fullRecordGapCenterValue - 380118

theorem fullRecordGapTerm00958_eq_value :
    recordGapCenter - 380118 = fullRecordGapValue00958 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00958_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00958 (fullRecordGapValue00958 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00958_not_prime : ¬(recordGapCenter - 380118).Prime := by
  rw [fullRecordGapTerm00958_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00958, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00958_fast_pow_mod_ne_one

def fullRecordGapValue00959 : Nat := fullRecordGapCenterValue - 380022

theorem fullRecordGapTerm00959_eq_value :
    recordGapCenter - 380022 = fullRecordGapValue00959 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00959_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00959 (fullRecordGapValue00959 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00959_not_prime : ¬(recordGapCenter - 380022).Prime := by
  rw [fullRecordGapTerm00959_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00959, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00959_fast_pow_mod_ne_one

def fullRecordGapValue00960 : Nat := fullRecordGapCenterValue - 379978

theorem fullRecordGapTerm00960_eq_value :
    recordGapCenter - 379978 = fullRecordGapValue00960 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00960_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00960 (fullRecordGapValue00960 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00960_not_prime : ¬(recordGapCenter - 379978).Prime := by
  rw [fullRecordGapTerm00960_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00960, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00960_fast_pow_mod_ne_one

def fullRecordGapValue00961 : Nat := fullRecordGapCenterValue - 379972

theorem fullRecordGapTerm00961_eq_value :
    recordGapCenter - 379972 = fullRecordGapValue00961 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00961_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00961 (fullRecordGapValue00961 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00961_not_prime : ¬(recordGapCenter - 379972).Prime := by
  rw [fullRecordGapTerm00961_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00961, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00961_fast_pow_mod_ne_one

def fullRecordGapValue00962 : Nat := fullRecordGapCenterValue - 379902

theorem fullRecordGapTerm00962_eq_value :
    recordGapCenter - 379902 = fullRecordGapValue00962 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00962_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00962 (fullRecordGapValue00962 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00962_not_prime : ¬(recordGapCenter - 379902).Prime := by
  rw [fullRecordGapTerm00962_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00962, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00962_fast_pow_mod_ne_one

def fullRecordGapValue00963 : Nat := fullRecordGapCenterValue - 379804

theorem fullRecordGapTerm00963_eq_value :
    recordGapCenter - 379804 = fullRecordGapValue00963 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00963_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00963 (fullRecordGapValue00963 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00963_not_prime : ¬(recordGapCenter - 379804).Prime := by
  rw [fullRecordGapTerm00963_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00963, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00963_fast_pow_mod_ne_one

def fullRecordGapValue00964 : Nat := fullRecordGapCenterValue - 379774

theorem fullRecordGapTerm00964_eq_value :
    recordGapCenter - 379774 = fullRecordGapValue00964 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00964_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00964 (fullRecordGapValue00964 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00964_not_prime : ¬(recordGapCenter - 379774).Prime := by
  rw [fullRecordGapTerm00964_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00964, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00964_fast_pow_mod_ne_one

def fullRecordGapValue00965 : Nat := fullRecordGapCenterValue - 379672

theorem fullRecordGapTerm00965_eq_value :
    recordGapCenter - 379672 = fullRecordGapValue00965 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00965_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00965 (fullRecordGapValue00965 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00965_not_prime : ¬(recordGapCenter - 379672).Prime := by
  rw [fullRecordGapTerm00965_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00965, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00965_fast_pow_mod_ne_one

def fullRecordGapValue00966 : Nat := fullRecordGapCenterValue - 379594

theorem fullRecordGapTerm00966_eq_value :
    recordGapCenter - 379594 = fullRecordGapValue00966 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00966_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00966 (fullRecordGapValue00966 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00966_not_prime : ¬(recordGapCenter - 379594).Prime := by
  rw [fullRecordGapTerm00966_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00966, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00966_fast_pow_mod_ne_one

def fullRecordGapValue00967 : Nat := fullRecordGapCenterValue - 379528

theorem fullRecordGapTerm00967_eq_value :
    recordGapCenter - 379528 = fullRecordGapValue00967 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00967_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00967 (fullRecordGapValue00967 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00967_not_prime : ¬(recordGapCenter - 379528).Prime := by
  rw [fullRecordGapTerm00967_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00967, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00967_fast_pow_mod_ne_one

def fullRecordGapValue00968 : Nat := fullRecordGapCenterValue - 379402

theorem fullRecordGapTerm00968_eq_value :
    recordGapCenter - 379402 = fullRecordGapValue00968 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00968_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00968 (fullRecordGapValue00968 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00968_not_prime : ¬(recordGapCenter - 379402).Prime := by
  rw [fullRecordGapTerm00968_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00968, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00968_fast_pow_mod_ne_one

def fullRecordGapValue00969 : Nat := fullRecordGapCenterValue - 379348

theorem fullRecordGapTerm00969_eq_value :
    recordGapCenter - 379348 = fullRecordGapValue00969 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00969_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00969 (fullRecordGapValue00969 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00969_not_prime : ¬(recordGapCenter - 379348).Prime := by
  rw [fullRecordGapTerm00969_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00969, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00969_fast_pow_mod_ne_one

def fullRecordGapValue00970 : Nat := fullRecordGapCenterValue - 379342

theorem fullRecordGapTerm00970_eq_value :
    recordGapCenter - 379342 = fullRecordGapValue00970 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00970_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00970 (fullRecordGapValue00970 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00970_not_prime : ¬(recordGapCenter - 379342).Prime := by
  rw [fullRecordGapTerm00970_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00970, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00970_fast_pow_mod_ne_one

def fullRecordGapValue00971 : Nat := fullRecordGapCenterValue - 379234

theorem fullRecordGapTerm00971_eq_value :
    recordGapCenter - 379234 = fullRecordGapValue00971 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00971_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00971 (fullRecordGapValue00971 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00971_not_prime : ¬(recordGapCenter - 379234).Prime := by
  rw [fullRecordGapTerm00971_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00971, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00971_fast_pow_mod_ne_one

def fullRecordGapValue00972 : Nat := fullRecordGapCenterValue - 379194

theorem fullRecordGapTerm00972_eq_value :
    recordGapCenter - 379194 = fullRecordGapValue00972 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00972_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00972 (fullRecordGapValue00972 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00972_not_prime : ¬(recordGapCenter - 379194).Prime := by
  rw [fullRecordGapTerm00972_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00972, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00972_fast_pow_mod_ne_one

def fullRecordGapValue00973 : Nat := fullRecordGapCenterValue - 379074

theorem fullRecordGapTerm00973_eq_value :
    recordGapCenter - 379074 = fullRecordGapValue00973 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00973_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00973 (fullRecordGapValue00973 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00973_not_prime : ¬(recordGapCenter - 379074).Prime := by
  rw [fullRecordGapTerm00973_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00973, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00973_fast_pow_mod_ne_one

def fullRecordGapValue00974 : Nat := fullRecordGapCenterValue - 379048

theorem fullRecordGapTerm00974_eq_value :
    recordGapCenter - 379048 = fullRecordGapValue00974 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00974_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00974 (fullRecordGapValue00974 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00974_not_prime : ¬(recordGapCenter - 379048).Prime := by
  rw [fullRecordGapTerm00974_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00974, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00974_fast_pow_mod_ne_one

def fullRecordGapValue00975 : Nat := fullRecordGapCenterValue - 378958

theorem fullRecordGapTerm00975_eq_value :
    recordGapCenter - 378958 = fullRecordGapValue00975 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00975_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00975 (fullRecordGapValue00975 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00975_not_prime : ¬(recordGapCenter - 378958).Prime := by
  rw [fullRecordGapTerm00975_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00975, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00975_fast_pow_mod_ne_one

def fullRecordGapValue00976 : Nat := fullRecordGapCenterValue - 378894

theorem fullRecordGapTerm00976_eq_value :
    recordGapCenter - 378894 = fullRecordGapValue00976 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00976_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00976 (fullRecordGapValue00976 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00976_not_prime : ¬(recordGapCenter - 378894).Prime := by
  rw [fullRecordGapTerm00976_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00976, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00976_fast_pow_mod_ne_one

def fullRecordGapValue00977 : Nat := fullRecordGapCenterValue - 378892

theorem fullRecordGapTerm00977_eq_value :
    recordGapCenter - 378892 = fullRecordGapValue00977 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00977_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00977 (fullRecordGapValue00977 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00977_not_prime : ¬(recordGapCenter - 378892).Prime := by
  rw [fullRecordGapTerm00977_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00977, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00977_fast_pow_mod_ne_one

def fullRecordGapValue00978 : Nat := fullRecordGapCenterValue - 378874

theorem fullRecordGapTerm00978_eq_value :
    recordGapCenter - 378874 = fullRecordGapValue00978 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00978_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00978 (fullRecordGapValue00978 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00978_not_prime : ¬(recordGapCenter - 378874).Prime := by
  rw [fullRecordGapTerm00978_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00978, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00978_fast_pow_mod_ne_one

def fullRecordGapValue00979 : Nat := fullRecordGapCenterValue - 378748

theorem fullRecordGapTerm00979_eq_value :
    recordGapCenter - 378748 = fullRecordGapValue00979 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00979_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00979 (fullRecordGapValue00979 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00979_not_prime : ¬(recordGapCenter - 378748).Prime := by
  rw [fullRecordGapTerm00979_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00979, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00979_fast_pow_mod_ne_one

def fullRecordGapValue00980 : Nat := fullRecordGapCenterValue - 378622

theorem fullRecordGapTerm00980_eq_value :
    recordGapCenter - 378622 = fullRecordGapValue00980 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00980_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00980 (fullRecordGapValue00980 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00980_not_prime : ¬(recordGapCenter - 378622).Prime := by
  rw [fullRecordGapTerm00980_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00980, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00980_fast_pow_mod_ne_one

def fullRecordGapValue00981 : Nat := fullRecordGapCenterValue - 378618

theorem fullRecordGapTerm00981_eq_value :
    recordGapCenter - 378618 = fullRecordGapValue00981 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00981_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00981 (fullRecordGapValue00981 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00981_not_prime : ¬(recordGapCenter - 378618).Prime := by
  rw [fullRecordGapTerm00981_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00981, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00981_fast_pow_mod_ne_one

def fullRecordGapValue00982 : Nat := fullRecordGapCenterValue - 378604

theorem fullRecordGapTerm00982_eq_value :
    recordGapCenter - 378604 = fullRecordGapValue00982 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00982_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00982 (fullRecordGapValue00982 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00982_not_prime : ¬(recordGapCenter - 378604).Prime := by
  rw [fullRecordGapTerm00982_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00982, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00982_fast_pow_mod_ne_one

def fullRecordGapValue00983 : Nat := fullRecordGapCenterValue - 378412

theorem fullRecordGapTerm00983_eq_value :
    recordGapCenter - 378412 = fullRecordGapValue00983 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00983_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00983 (fullRecordGapValue00983 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00983_not_prime : ¬(recordGapCenter - 378412).Prime := by
  rw [fullRecordGapTerm00983_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00983, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00983_fast_pow_mod_ne_one

def fullRecordGapValue00984 : Nat := fullRecordGapCenterValue - 378172

theorem fullRecordGapTerm00984_eq_value :
    recordGapCenter - 378172 = fullRecordGapValue00984 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00984_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00984 (fullRecordGapValue00984 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00984_not_prime : ¬(recordGapCenter - 378172).Prime := by
  rw [fullRecordGapTerm00984_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00984, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00984_fast_pow_mod_ne_one

def fullRecordGapValue00985 : Nat := fullRecordGapCenterValue - 378124

theorem fullRecordGapTerm00985_eq_value :
    recordGapCenter - 378124 = fullRecordGapValue00985 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00985_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00985 (fullRecordGapValue00985 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00985_not_prime : ¬(recordGapCenter - 378124).Prime := by
  rw [fullRecordGapTerm00985_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00985, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00985_fast_pow_mod_ne_one

def fullRecordGapValue00986 : Nat := fullRecordGapCenterValue - 378034

theorem fullRecordGapTerm00986_eq_value :
    recordGapCenter - 378034 = fullRecordGapValue00986 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00986_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00986 (fullRecordGapValue00986 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00986_not_prime : ¬(recordGapCenter - 378034).Prime := by
  rw [fullRecordGapTerm00986_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00986, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00986_fast_pow_mod_ne_one

def fullRecordGapValue00987 : Nat := fullRecordGapCenterValue - 377998

theorem fullRecordGapTerm00987_eq_value :
    recordGapCenter - 377998 = fullRecordGapValue00987 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00987_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00987 (fullRecordGapValue00987 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00987_not_prime : ¬(recordGapCenter - 377998).Prime := by
  rw [fullRecordGapTerm00987_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00987, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00987_fast_pow_mod_ne_one

def fullRecordGapValue00988 : Nat := fullRecordGapCenterValue - 377934

theorem fullRecordGapTerm00988_eq_value :
    recordGapCenter - 377934 = fullRecordGapValue00988 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00988_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00988 (fullRecordGapValue00988 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00988_not_prime : ¬(recordGapCenter - 377934).Prime := by
  rw [fullRecordGapTerm00988_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00988, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00988_fast_pow_mod_ne_one

def fullRecordGapValue00989 : Nat := fullRecordGapCenterValue - 377932

theorem fullRecordGapTerm00989_eq_value :
    recordGapCenter - 377932 = fullRecordGapValue00989 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00989_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00989 (fullRecordGapValue00989 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00989_not_prime : ¬(recordGapCenter - 377932).Prime := by
  rw [fullRecordGapTerm00989_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00989, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00989_fast_pow_mod_ne_one

def fullRecordGapValue00990 : Nat := fullRecordGapCenterValue - 377908

theorem fullRecordGapTerm00990_eq_value :
    recordGapCenter - 377908 = fullRecordGapValue00990 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00990_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00990 (fullRecordGapValue00990 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00990_not_prime : ¬(recordGapCenter - 377908).Prime := by
  rw [fullRecordGapTerm00990_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00990, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00990_fast_pow_mod_ne_one

def fullRecordGapValue00991 : Nat := fullRecordGapCenterValue - 377878

theorem fullRecordGapTerm00991_eq_value :
    recordGapCenter - 377878 = fullRecordGapValue00991 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00991_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00991 (fullRecordGapValue00991 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00991_not_prime : ¬(recordGapCenter - 377878).Prime := by
  rw [fullRecordGapTerm00991_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00991, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00991_fast_pow_mod_ne_one

def fullRecordGapValue00992 : Nat := fullRecordGapCenterValue - 377512

theorem fullRecordGapTerm00992_eq_value :
    recordGapCenter - 377512 = fullRecordGapValue00992 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00992_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00992 (fullRecordGapValue00992 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00992_not_prime : ¬(recordGapCenter - 377512).Prime := by
  rw [fullRecordGapTerm00992_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00992, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00992_fast_pow_mod_ne_one

def fullRecordGapValue00993 : Nat := fullRecordGapCenterValue - 377382

theorem fullRecordGapTerm00993_eq_value :
    recordGapCenter - 377382 = fullRecordGapValue00993 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00993_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00993 (fullRecordGapValue00993 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00993_not_prime : ¬(recordGapCenter - 377382).Prime := by
  rw [fullRecordGapTerm00993_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00993, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00993_fast_pow_mod_ne_one

def fullRecordGapValue00994 : Nat := fullRecordGapCenterValue - 377362

theorem fullRecordGapTerm00994_eq_value :
    recordGapCenter - 377362 = fullRecordGapValue00994 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00994_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00994 (fullRecordGapValue00994 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00994_not_prime : ¬(recordGapCenter - 377362).Prime := by
  rw [fullRecordGapTerm00994_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00994, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00994_fast_pow_mod_ne_one

def fullRecordGapValue00995 : Nat := fullRecordGapCenterValue - 377218

theorem fullRecordGapTerm00995_eq_value :
    recordGapCenter - 377218 = fullRecordGapValue00995 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00995_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00995 (fullRecordGapValue00995 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00995_not_prime : ¬(recordGapCenter - 377218).Prime := by
  rw [fullRecordGapTerm00995_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00995, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00995_fast_pow_mod_ne_one

def fullRecordGapValue00996 : Nat := fullRecordGapCenterValue - 377032

theorem fullRecordGapTerm00996_eq_value :
    recordGapCenter - 377032 = fullRecordGapValue00996 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00996_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00996 (fullRecordGapValue00996 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00996_not_prime : ¬(recordGapCenter - 377032).Prime := by
  rw [fullRecordGapTerm00996_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00996, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00996_fast_pow_mod_ne_one

def fullRecordGapValue00997 : Nat := fullRecordGapCenterValue - 376962

theorem fullRecordGapTerm00997_eq_value :
    recordGapCenter - 376962 = fullRecordGapValue00997 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00997_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00997 (fullRecordGapValue00997 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00997_not_prime : ¬(recordGapCenter - 376962).Prime := by
  rw [fullRecordGapTerm00997_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00997, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00997_fast_pow_mod_ne_one

def fullRecordGapValue00998 : Nat := fullRecordGapCenterValue - 376834

theorem fullRecordGapTerm00998_eq_value :
    recordGapCenter - 376834 = fullRecordGapValue00998 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00998_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00998 (fullRecordGapValue00998 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00998_not_prime : ¬(recordGapCenter - 376834).Prime := by
  rw [fullRecordGapTerm00998_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00998, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00998_fast_pow_mod_ne_one

def fullRecordGapValue00999 : Nat := fullRecordGapCenterValue - 376738

theorem fullRecordGapTerm00999_eq_value :
    recordGapCenter - 376738 = fullRecordGapValue00999 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00999_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00999 (fullRecordGapValue00999 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00999_not_prime : ¬(recordGapCenter - 376738).Prime := by
  rw [fullRecordGapTerm00999_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00999, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00999_fast_pow_mod_ne_one

def fullRecordGapValue01000 : Nat := fullRecordGapCenterValue - 376702

theorem fullRecordGapTerm01000_eq_value :
    recordGapCenter - 376702 = fullRecordGapValue01000 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01000_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01000 (fullRecordGapValue01000 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01000_not_prime : ¬(recordGapCenter - 376702).Prime := by
  rw [fullRecordGapTerm01000_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01000, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01000_fast_pow_mod_ne_one

def fullRecordGapValue01001 : Nat := fullRecordGapCenterValue - 376638

theorem fullRecordGapTerm01001_eq_value :
    recordGapCenter - 376638 = fullRecordGapValue01001 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01001_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01001 (fullRecordGapValue01001 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01001_not_prime : ¬(recordGapCenter - 376638).Prime := by
  rw [fullRecordGapTerm01001_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01001, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01001_fast_pow_mod_ne_one

def fullRecordGapValue01002 : Nat := fullRecordGapCenterValue - 376582

theorem fullRecordGapTerm01002_eq_value :
    recordGapCenter - 376582 = fullRecordGapValue01002 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01002_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01002 (fullRecordGapValue01002 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01002_not_prime : ¬(recordGapCenter - 376582).Prime := by
  rw [fullRecordGapTerm01002_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01002, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01002_fast_pow_mod_ne_one

def fullRecordGapValue01003 : Nat := fullRecordGapCenterValue - 376518

theorem fullRecordGapTerm01003_eq_value :
    recordGapCenter - 376518 = fullRecordGapValue01003 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01003_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01003 (fullRecordGapValue01003 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01003_not_prime : ¬(recordGapCenter - 376518).Prime := by
  rw [fullRecordGapTerm01003_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01003, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01003_fast_pow_mod_ne_one

def fullRecordGapValue01004 : Nat := fullRecordGapCenterValue - 376294

theorem fullRecordGapTerm01004_eq_value :
    recordGapCenter - 376294 = fullRecordGapValue01004 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01004_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01004 (fullRecordGapValue01004 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01004_not_prime : ¬(recordGapCenter - 376294).Prime := by
  rw [fullRecordGapTerm01004_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01004, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01004_fast_pow_mod_ne_one

def fullRecordGapValue01005 : Nat := fullRecordGapCenterValue - 376122

theorem fullRecordGapTerm01005_eq_value :
    recordGapCenter - 376122 = fullRecordGapValue01005 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01005_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01005 (fullRecordGapValue01005 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01005_not_prime : ¬(recordGapCenter - 376122).Prime := by
  rw [fullRecordGapTerm01005_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01005, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01005_fast_pow_mod_ne_one

def fullRecordGapValue01006 : Nat := fullRecordGapCenterValue - 375868

theorem fullRecordGapTerm01006_eq_value :
    recordGapCenter - 375868 = fullRecordGapValue01006 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01006_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01006 (fullRecordGapValue01006 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01006_not_prime : ¬(recordGapCenter - 375868).Prime := by
  rw [fullRecordGapTerm01006_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01006, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01006_fast_pow_mod_ne_one

def fullRecordGapValue01007 : Nat := fullRecordGapCenterValue - 375798

theorem fullRecordGapTerm01007_eq_value :
    recordGapCenter - 375798 = fullRecordGapValue01007 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01007_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01007 (fullRecordGapValue01007 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01007_not_prime : ¬(recordGapCenter - 375798).Prime := by
  rw [fullRecordGapTerm01007_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01007, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01007_fast_pow_mod_ne_one

def fullRecordGapValue01008 : Nat := fullRecordGapCenterValue - 375748

theorem fullRecordGapTerm01008_eq_value :
    recordGapCenter - 375748 = fullRecordGapValue01008 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01008_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01008 (fullRecordGapValue01008 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01008_not_prime : ¬(recordGapCenter - 375748).Prime := by
  rw [fullRecordGapTerm01008_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01008, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01008_fast_pow_mod_ne_one

def fullRecordGapValue01009 : Nat := fullRecordGapCenterValue - 375652

theorem fullRecordGapTerm01009_eq_value :
    recordGapCenter - 375652 = fullRecordGapValue01009 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01009_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01009 (fullRecordGapValue01009 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01009_not_prime : ¬(recordGapCenter - 375652).Prime := by
  rw [fullRecordGapTerm01009_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01009, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01009_fast_pow_mod_ne_one

def fullRecordGapValue01010 : Nat := fullRecordGapCenterValue - 375618

theorem fullRecordGapTerm01010_eq_value :
    recordGapCenter - 375618 = fullRecordGapValue01010 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01010_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01010 (fullRecordGapValue01010 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01010_not_prime : ¬(recordGapCenter - 375618).Prime := by
  rw [fullRecordGapTerm01010_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01010, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01010_fast_pow_mod_ne_one

def fullRecordGapValue01011 : Nat := fullRecordGapCenterValue - 375604

theorem fullRecordGapTerm01011_eq_value :
    recordGapCenter - 375604 = fullRecordGapValue01011 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01011_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01011 (fullRecordGapValue01011 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01011_not_prime : ¬(recordGapCenter - 375604).Prime := by
  rw [fullRecordGapTerm01011_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01011, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01011_fast_pow_mod_ne_one

def fullRecordGapValue01012 : Nat := fullRecordGapCenterValue - 375442

theorem fullRecordGapTerm01012_eq_value :
    recordGapCenter - 375442 = fullRecordGapValue01012 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01012_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01012 (fullRecordGapValue01012 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01012_not_prime : ¬(recordGapCenter - 375442).Prime := by
  rw [fullRecordGapTerm01012_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01012, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01012_fast_pow_mod_ne_one

def fullRecordGapValue01013 : Nat := fullRecordGapCenterValue - 375378

theorem fullRecordGapTerm01013_eq_value :
    recordGapCenter - 375378 = fullRecordGapValue01013 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01013_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01013 (fullRecordGapValue01013 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01013_not_prime : ¬(recordGapCenter - 375378).Prime := by
  rw [fullRecordGapTerm01013_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01013, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01013_fast_pow_mod_ne_one

def fullRecordGapValue01014 : Nat := fullRecordGapCenterValue - 375294

theorem fullRecordGapTerm01014_eq_value :
    recordGapCenter - 375294 = fullRecordGapValue01014 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01014_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01014 (fullRecordGapValue01014 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01014_not_prime : ¬(recordGapCenter - 375294).Prime := by
  rw [fullRecordGapTerm01014_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01014, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01014_fast_pow_mod_ne_one

def fullRecordGapValue01015 : Nat := fullRecordGapCenterValue - 375262

theorem fullRecordGapTerm01015_eq_value :
    recordGapCenter - 375262 = fullRecordGapValue01015 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01015_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01015 (fullRecordGapValue01015 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01015_not_prime : ¬(recordGapCenter - 375262).Prime := by
  rw [fullRecordGapTerm01015_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01015, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01015_fast_pow_mod_ne_one

def fullRecordGapValue01016 : Nat := fullRecordGapCenterValue - 375244

theorem fullRecordGapTerm01016_eq_value :
    recordGapCenter - 375244 = fullRecordGapValue01016 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01016_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01016 (fullRecordGapValue01016 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01016_not_prime : ¬(recordGapCenter - 375244).Prime := by
  rw [fullRecordGapTerm01016_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01016, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01016_fast_pow_mod_ne_one

def fullRecordGapValue01017 : Nat := fullRecordGapCenterValue - 375118

theorem fullRecordGapTerm01017_eq_value :
    recordGapCenter - 375118 = fullRecordGapValue01017 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01017_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01017 (fullRecordGapValue01017 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01017_not_prime : ¬(recordGapCenter - 375118).Prime := by
  rw [fullRecordGapTerm01017_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01017, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01017_fast_pow_mod_ne_one

def fullRecordGapValue01018 : Nat := fullRecordGapCenterValue - 375094

theorem fullRecordGapTerm01018_eq_value :
    recordGapCenter - 375094 = fullRecordGapValue01018 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01018_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01018 (fullRecordGapValue01018 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01018_not_prime : ¬(recordGapCenter - 375094).Prime := by
  rw [fullRecordGapTerm01018_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01018, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01018_fast_pow_mod_ne_one

def fullRecordGapValue01019 : Nat := fullRecordGapCenterValue - 375000

theorem fullRecordGapTerm01019_eq_value :
    recordGapCenter - 375000 = fullRecordGapValue01019 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01019_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01019 (fullRecordGapValue01019 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01019_not_prime : ¬(recordGapCenter - 375000).Prime := by
  rw [fullRecordGapTerm01019_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01019, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01019_fast_pow_mod_ne_one

def fullRecordGapValue01020 : Nat := fullRecordGapCenterValue - 374982

theorem fullRecordGapTerm01020_eq_value :
    recordGapCenter - 374982 = fullRecordGapValue01020 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01020_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01020 (fullRecordGapValue01020 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01020_not_prime : ¬(recordGapCenter - 374982).Prime := by
  rw [fullRecordGapTerm01020_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01020, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01020_fast_pow_mod_ne_one

def fullRecordGapValue01021 : Nat := fullRecordGapCenterValue - 374898

theorem fullRecordGapTerm01021_eq_value :
    recordGapCenter - 374898 = fullRecordGapValue01021 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01021_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01021 (fullRecordGapValue01021 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01021_not_prime : ¬(recordGapCenter - 374898).Prime := by
  rw [fullRecordGapTerm01021_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01021, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01021_fast_pow_mod_ne_one

def fullRecordGapValue01022 : Nat := fullRecordGapCenterValue - 374674

theorem fullRecordGapTerm01022_eq_value :
    recordGapCenter - 374674 = fullRecordGapValue01022 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01022_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01022 (fullRecordGapValue01022 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01022_not_prime : ¬(recordGapCenter - 374674).Prime := by
  rw [fullRecordGapTerm01022_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01022, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01022_fast_pow_mod_ne_one

def fullRecordGapValue01023 : Nat := fullRecordGapCenterValue - 374548

theorem fullRecordGapTerm01023_eq_value :
    recordGapCenter - 374548 = fullRecordGapValue01023 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01023_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01023 (fullRecordGapValue01023 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01023_not_prime : ¬(recordGapCenter - 374548).Prime := by
  rw [fullRecordGapTerm01023_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01023, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01023_fast_pow_mod_ne_one

def fullRecordGapValue01024 : Nat := fullRecordGapCenterValue - 374502

theorem fullRecordGapTerm01024_eq_value :
    recordGapCenter - 374502 = fullRecordGapValue01024 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01024_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01024 (fullRecordGapValue01024 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01024_not_prime : ¬(recordGapCenter - 374502).Prime := by
  rw [fullRecordGapTerm01024_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01024, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01024_fast_pow_mod_ne_one

end PrimeFactorUnimodality
