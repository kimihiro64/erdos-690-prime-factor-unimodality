import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue03585 : Nat := fullRecordGapCenterValue - 87994

theorem fullRecordGapTerm03585_eq_value :
    recordGapCenter - 87994 = fullRecordGapValue03585 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03585_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03585 (fullRecordGapValue03585 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03585_not_prime : ¬(recordGapCenter - 87994).Prime := by
  rw [fullRecordGapTerm03585_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03585, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03585_fast_pow_mod_ne_one

def fullRecordGapValue03586 : Nat := fullRecordGapCenterValue - 87442

theorem fullRecordGapTerm03586_eq_value :
    recordGapCenter - 87442 = fullRecordGapValue03586 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03586_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03586 (fullRecordGapValue03586 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03586_not_prime : ¬(recordGapCenter - 87442).Prime := by
  rw [fullRecordGapTerm03586_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03586, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03586_fast_pow_mod_ne_one

def fullRecordGapValue03587 : Nat := fullRecordGapCenterValue - 87318

theorem fullRecordGapTerm03587_eq_value :
    recordGapCenter - 87318 = fullRecordGapValue03587 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03587_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03587 (fullRecordGapValue03587 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03587_not_prime : ¬(recordGapCenter - 87318).Prime := by
  rw [fullRecordGapTerm03587_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03587, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03587_fast_pow_mod_ne_one

def fullRecordGapValue03588 : Nat := fullRecordGapCenterValue - 87154

theorem fullRecordGapTerm03588_eq_value :
    recordGapCenter - 87154 = fullRecordGapValue03588 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03588_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03588 (fullRecordGapValue03588 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03588_not_prime : ¬(recordGapCenter - 87154).Prime := by
  rw [fullRecordGapTerm03588_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03588, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03588_fast_pow_mod_ne_one

def fullRecordGapValue03589 : Nat := fullRecordGapCenterValue - 86902

theorem fullRecordGapTerm03589_eq_value :
    recordGapCenter - 86902 = fullRecordGapValue03589 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03589_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03589 (fullRecordGapValue03589 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03589_not_prime : ¬(recordGapCenter - 86902).Prime := by
  rw [fullRecordGapTerm03589_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03589, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03589_fast_pow_mod_ne_one

def fullRecordGapValue03590 : Nat := fullRecordGapCenterValue - 86854

theorem fullRecordGapTerm03590_eq_value :
    recordGapCenter - 86854 = fullRecordGapValue03590 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03590_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03590 (fullRecordGapValue03590 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03590_not_prime : ¬(recordGapCenter - 86854).Prime := by
  rw [fullRecordGapTerm03590_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03590, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03590_fast_pow_mod_ne_one

def fullRecordGapValue03591 : Nat := fullRecordGapCenterValue - 86638

theorem fullRecordGapTerm03591_eq_value :
    recordGapCenter - 86638 = fullRecordGapValue03591 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03591_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03591 (fullRecordGapValue03591 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03591_not_prime : ¬(recordGapCenter - 86638).Prime := by
  rw [fullRecordGapTerm03591_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03591, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03591_fast_pow_mod_ne_one

def fullRecordGapValue03592 : Nat := fullRecordGapCenterValue - 86400

theorem fullRecordGapTerm03592_eq_value :
    recordGapCenter - 86400 = fullRecordGapValue03592 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03592_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03592 (fullRecordGapValue03592 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03592_not_prime : ¬(recordGapCenter - 86400).Prime := by
  rw [fullRecordGapTerm03592_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03592, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03592_fast_pow_mod_ne_one

def fullRecordGapValue03593 : Nat := fullRecordGapCenterValue - 84672

theorem fullRecordGapTerm03593_eq_value :
    recordGapCenter - 84672 = fullRecordGapValue03593 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03593_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03593 (fullRecordGapValue03593 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03593_not_prime : ¬(recordGapCenter - 84672).Prime := by
  rw [fullRecordGapTerm03593_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03593, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03593_fast_pow_mod_ne_one

def fullRecordGapValue03594 : Nat := fullRecordGapCenterValue - 81648

theorem fullRecordGapTerm03594_eq_value :
    recordGapCenter - 81648 = fullRecordGapValue03594 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03594_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03594 (fullRecordGapValue03594 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03594_not_prime : ¬(recordGapCenter - 81648).Prime := by
  rw [fullRecordGapTerm03594_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03594, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03594_fast_pow_mod_ne_one

def fullRecordGapValue03595 : Nat := fullRecordGapCenterValue - 81000

theorem fullRecordGapTerm03595_eq_value :
    recordGapCenter - 81000 = fullRecordGapValue03595 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03595_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03595 (fullRecordGapValue03595 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03595_not_prime : ¬(recordGapCenter - 81000).Prime := by
  rw [fullRecordGapTerm03595_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03595, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03595_fast_pow_mod_ne_one

def fullRecordGapValue03596 : Nat := fullRecordGapCenterValue - 80850

theorem fullRecordGapTerm03596_eq_value :
    recordGapCenter - 80850 = fullRecordGapValue03596 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03596_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03596 (fullRecordGapValue03596 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03596_not_prime : ¬(recordGapCenter - 80850).Prime := by
  rw [fullRecordGapTerm03596_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03596, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03596_fast_pow_mod_ne_one

def fullRecordGapValue03597 : Nat := fullRecordGapCenterValue - 80190

theorem fullRecordGapTerm03597_eq_value :
    recordGapCenter - 80190 = fullRecordGapValue03597 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03597_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03597 (fullRecordGapValue03597 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03597_not_prime : ¬(recordGapCenter - 80190).Prime := by
  rw [fullRecordGapTerm03597_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03597, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03597_fast_pow_mod_ne_one

def fullRecordGapValue03598 : Nat := fullRecordGapCenterValue - 78400

theorem fullRecordGapTerm03598_eq_value :
    recordGapCenter - 78400 = fullRecordGapValue03598 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03598_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03598 (fullRecordGapValue03598 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03598_not_prime : ¬(recordGapCenter - 78400).Prime := by
  rw [fullRecordGapTerm03598_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03598, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03598_fast_pow_mod_ne_one

def fullRecordGapValue03599 : Nat := fullRecordGapCenterValue - 76800

theorem fullRecordGapTerm03599_eq_value :
    recordGapCenter - 76800 = fullRecordGapValue03599 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03599_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03599 (fullRecordGapValue03599 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03599_not_prime : ¬(recordGapCenter - 76800).Prime := by
  rw [fullRecordGapTerm03599_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03599, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03599_fast_pow_mod_ne_one

def fullRecordGapValue03600 : Nat := fullRecordGapCenterValue - 76032

theorem fullRecordGapTerm03600_eq_value :
    recordGapCenter - 76032 = fullRecordGapValue03600 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03600_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03600 (fullRecordGapValue03600 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03600_not_prime : ¬(recordGapCenter - 76032).Prime := by
  rw [fullRecordGapTerm03600_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03600, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03600_fast_pow_mod_ne_one

def fullRecordGapValue03601 : Nat := fullRecordGapCenterValue - 74088

theorem fullRecordGapTerm03601_eq_value :
    recordGapCenter - 74088 = fullRecordGapValue03601 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03601_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03601 (fullRecordGapValue03601 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03601_not_prime : ¬(recordGapCenter - 74088).Prime := by
  rw [fullRecordGapTerm03601_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03601, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03601_fast_pow_mod_ne_one

def fullRecordGapValue03602 : Nat := fullRecordGapCenterValue - 73920

theorem fullRecordGapTerm03602_eq_value :
    recordGapCenter - 73920 = fullRecordGapValue03602 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03602_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03602 (fullRecordGapValue03602 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03602_not_prime : ¬(recordGapCenter - 73920).Prime := by
  rw [fullRecordGapTerm03602_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03602, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03602_fast_pow_mod_ne_one

def fullRecordGapValue03603 : Nat := fullRecordGapCenterValue - 73728

theorem fullRecordGapTerm03603_eq_value :
    recordGapCenter - 73728 = fullRecordGapValue03603 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03603_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03603 (fullRecordGapValue03603 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03603_not_prime : ¬(recordGapCenter - 73728).Prime := by
  rw [fullRecordGapTerm03603_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03603, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03603_fast_pow_mod_ne_one

def fullRecordGapValue03604 : Nat := fullRecordGapCenterValue - 72900

theorem fullRecordGapTerm03604_eq_value :
    recordGapCenter - 72900 = fullRecordGapValue03604 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03604_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03604 (fullRecordGapValue03604 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03604_not_prime : ¬(recordGapCenter - 72900).Prime := by
  rw [fullRecordGapTerm03604_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03604, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03604_fast_pow_mod_ne_one

def fullRecordGapValue03605 : Nat := fullRecordGapCenterValue - 72030

theorem fullRecordGapTerm03605_eq_value :
    recordGapCenter - 72030 = fullRecordGapValue03605 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03605_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03605 (fullRecordGapValue03605 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03605_not_prime : ¬(recordGapCenter - 72030).Prime := by
  rw [fullRecordGapTerm03605_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03605, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03605_fast_pow_mod_ne_one

def fullRecordGapValue03606 : Nat := fullRecordGapCenterValue - 71874

theorem fullRecordGapTerm03606_eq_value :
    recordGapCenter - 71874 = fullRecordGapValue03606 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03606_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03606 (fullRecordGapValue03606 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03606_not_prime : ¬(recordGapCenter - 71874).Prime := by
  rw [fullRecordGapTerm03606_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03606, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03606_fast_pow_mod_ne_one

def fullRecordGapValue03607 : Nat := fullRecordGapCenterValue - 71280

theorem fullRecordGapTerm03607_eq_value :
    recordGapCenter - 71280 = fullRecordGapValue03607 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03607_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03607 (fullRecordGapValue03607 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03607_not_prime : ¬(recordGapCenter - 71280).Prime := by
  rw [fullRecordGapTerm03607_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03607, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03607_fast_pow_mod_ne_one

def fullRecordGapValue03608 : Nat := fullRecordGapCenterValue - 70560

theorem fullRecordGapTerm03608_eq_value :
    recordGapCenter - 70560 = fullRecordGapValue03608 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03608_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03608 (fullRecordGapValue03608 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03608_not_prime : ¬(recordGapCenter - 70560).Prime := by
  rw [fullRecordGapTerm03608_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03608, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03608_fast_pow_mod_ne_one

def fullRecordGapValue03609 : Nat := fullRecordGapCenterValue - 69300

theorem fullRecordGapTerm03609_eq_value :
    recordGapCenter - 69300 = fullRecordGapValue03609 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03609_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03609 (fullRecordGapValue03609 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03609_not_prime : ¬(recordGapCenter - 69300).Prime := by
  rw [fullRecordGapTerm03609_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03609, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03609_fast_pow_mod_ne_one

def fullRecordGapValue03610 : Nat := fullRecordGapCenterValue - 68992

theorem fullRecordGapTerm03610_eq_value :
    recordGapCenter - 68992 = fullRecordGapValue03610 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03610_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03610 (fullRecordGapValue03610 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03610_not_prime : ¬(recordGapCenter - 68992).Prime := by
  rw [fullRecordGapTerm03610_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03610, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03610_fast_pow_mod_ne_one

def fullRecordGapValue03611 : Nat := fullRecordGapCenterValue - 68040

theorem fullRecordGapTerm03611_eq_value :
    recordGapCenter - 68040 = fullRecordGapValue03611 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03611_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03611 (fullRecordGapValue03611 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03611_not_prime : ¬(recordGapCenter - 68040).Prime := by
  rw [fullRecordGapTerm03611_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03611, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03611_fast_pow_mod_ne_one

def fullRecordGapValue03612 : Nat := fullRecordGapCenterValue - 67584

theorem fullRecordGapTerm03612_eq_value :
    recordGapCenter - 67584 = fullRecordGapValue03612 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03612_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03612 (fullRecordGapValue03612 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03612_not_prime : ¬(recordGapCenter - 67584).Prime := by
  rw [fullRecordGapTerm03612_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03612, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03612_fast_pow_mod_ne_one

def fullRecordGapValue03613 : Nat := fullRecordGapCenterValue - 67228

theorem fullRecordGapTerm03613_eq_value :
    recordGapCenter - 67228 = fullRecordGapValue03613 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03613_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03613 (fullRecordGapValue03613 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03613_not_prime : ¬(recordGapCenter - 67228).Prime := by
  rw [fullRecordGapTerm03613_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03613, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03613_fast_pow_mod_ne_one

def fullRecordGapValue03614 : Nat := fullRecordGapCenterValue - 67200

theorem fullRecordGapTerm03614_eq_value :
    recordGapCenter - 67200 = fullRecordGapValue03614 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03614_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03614 (fullRecordGapValue03614 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03614_not_prime : ¬(recordGapCenter - 67200).Prime := by
  rw [fullRecordGapTerm03614_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03614, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03614_fast_pow_mod_ne_one

def fullRecordGapValue03615 : Nat := fullRecordGapCenterValue - 65340

theorem fullRecordGapTerm03615_eq_value :
    recordGapCenter - 65340 = fullRecordGapValue03615 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03615_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03615 (fullRecordGapValue03615 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03615_not_prime : ¬(recordGapCenter - 65340).Prime := by
  rw [fullRecordGapTerm03615_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03615, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03615_fast_pow_mod_ne_one

def fullRecordGapValue03616 : Nat := fullRecordGapCenterValue - 63888

theorem fullRecordGapTerm03616_eq_value :
    recordGapCenter - 63888 = fullRecordGapValue03616 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03616_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03616 (fullRecordGapValue03616 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03616_not_prime : ¬(recordGapCenter - 63888).Prime := by
  rw [fullRecordGapTerm03616_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03616, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03616_fast_pow_mod_ne_one

def fullRecordGapValue03617 : Nat := fullRecordGapCenterValue - 63000

theorem fullRecordGapTerm03617_eq_value :
    recordGapCenter - 63000 = fullRecordGapValue03617 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03617_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03617 (fullRecordGapValue03617 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03617_not_prime : ¬(recordGapCenter - 63000).Prime := by
  rw [fullRecordGapTerm03617_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03617, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03617_fast_pow_mod_ne_one

def fullRecordGapValue03618 : Nat := fullRecordGapCenterValue - 62208

theorem fullRecordGapTerm03618_eq_value :
    recordGapCenter - 62208 = fullRecordGapValue03618 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03618_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03618 (fullRecordGapValue03618 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03618_not_prime : ¬(recordGapCenter - 62208).Prime := by
  rw [fullRecordGapTerm03618_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03618, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03618_fast_pow_mod_ne_one

def fullRecordGapValue03619 : Nat := fullRecordGapCenterValue - 61740

theorem fullRecordGapTerm03619_eq_value :
    recordGapCenter - 61740 = fullRecordGapValue03619 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03619_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03619 (fullRecordGapValue03619 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03619_not_prime : ¬(recordGapCenter - 61740).Prime := by
  rw [fullRecordGapTerm03619_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03619, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03619_fast_pow_mod_ne_one

def fullRecordGapValue03620 : Nat := fullRecordGapCenterValue - 60480

theorem fullRecordGapTerm03620_eq_value :
    recordGapCenter - 60480 = fullRecordGapValue03620 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03620_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03620 (fullRecordGapValue03620 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03620_not_prime : ¬(recordGapCenter - 60480).Prime := by
  rw [fullRecordGapTerm03620_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03620, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03620_fast_pow_mod_ne_one

def fullRecordGapValue03621 : Nat := fullRecordGapCenterValue - 57750

theorem fullRecordGapTerm03621_eq_value :
    recordGapCenter - 57750 = fullRecordGapValue03621 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03621_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03621 (fullRecordGapValue03621 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03621_not_prime : ¬(recordGapCenter - 57750).Prime := by
  rw [fullRecordGapTerm03621_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03621, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03621_fast_pow_mod_ne_one

def fullRecordGapValue03622 : Nat := fullRecordGapCenterValue - 57624

theorem fullRecordGapTerm03622_eq_value :
    recordGapCenter - 57624 = fullRecordGapValue03622 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03622_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03622 (fullRecordGapValue03622 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03622_not_prime : ¬(recordGapCenter - 57624).Prime := by
  rw [fullRecordGapTerm03622_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03622, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03622_fast_pow_mod_ne_one

def fullRecordGapValue03623 : Nat := fullRecordGapCenterValue - 56250

theorem fullRecordGapTerm03623_eq_value :
    recordGapCenter - 56250 = fullRecordGapValue03623 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03623_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03623 (fullRecordGapValue03623 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03623_not_prime : ¬(recordGapCenter - 56250).Prime := by
  rw [fullRecordGapTerm03623_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03623, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03623_fast_pow_mod_ne_one

def fullRecordGapValue03624 : Nat := fullRecordGapCenterValue - 55440

theorem fullRecordGapTerm03624_eq_value :
    recordGapCenter - 55440 = fullRecordGapValue03624 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03624_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03624 (fullRecordGapValue03624 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03624_not_prime : ¬(recordGapCenter - 55440).Prime := by
  rw [fullRecordGapTerm03624_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03624, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03624_fast_pow_mod_ne_one

def fullRecordGapValue03625 : Nat := fullRecordGapCenterValue - 54450

theorem fullRecordGapTerm03625_eq_value :
    recordGapCenter - 54450 = fullRecordGapValue03625 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03625_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03625 (fullRecordGapValue03625 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03625_not_prime : ¬(recordGapCenter - 54450).Prime := by
  rw [fullRecordGapTerm03625_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03625, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03625_fast_pow_mod_ne_one

def fullRecordGapValue03626 : Nat := fullRecordGapCenterValue - 54208

theorem fullRecordGapTerm03626_eq_value :
    recordGapCenter - 54208 = fullRecordGapValue03626 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03626_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03626 (fullRecordGapValue03626 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03626_not_prime : ¬(recordGapCenter - 54208).Prime := by
  rw [fullRecordGapTerm03626_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03626, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03626_fast_pow_mod_ne_one

def fullRecordGapValue03627 : Nat := fullRecordGapCenterValue - 53760

theorem fullRecordGapTerm03627_eq_value :
    recordGapCenter - 53760 = fullRecordGapValue03627 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03627_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03627 (fullRecordGapValue03627 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03627_not_prime : ¬(recordGapCenter - 53760).Prime := by
  rw [fullRecordGapTerm03627_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03627, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03627_fast_pow_mod_ne_one

def fullRecordGapValue03628 : Nat := fullRecordGapCenterValue - 52800

theorem fullRecordGapTerm03628_eq_value :
    recordGapCenter - 52800 = fullRecordGapValue03628 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03628_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03628 (fullRecordGapValue03628 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03628_not_prime : ¬(recordGapCenter - 52800).Prime := by
  rw [fullRecordGapTerm03628_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03628, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03628_fast_pow_mod_ne_one

def fullRecordGapValue03629 : Nat := fullRecordGapCenterValue - 51744

theorem fullRecordGapTerm03629_eq_value :
    recordGapCenter - 51744 = fullRecordGapValue03629 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03629_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03629 (fullRecordGapValue03629 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03629_not_prime : ¬(recordGapCenter - 51744).Prime := by
  rw [fullRecordGapTerm03629_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03629, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03629_fast_pow_mod_ne_one

def fullRecordGapValue03630 : Nat := fullRecordGapCenterValue - 49392

theorem fullRecordGapTerm03630_eq_value :
    recordGapCenter - 49392 = fullRecordGapValue03630 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03630_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03630 (fullRecordGapValue03630 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03630_not_prime : ¬(recordGapCenter - 49392).Prime := by
  rw [fullRecordGapTerm03630_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03630, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03630_fast_pow_mod_ne_one

def fullRecordGapValue03631 : Nat := fullRecordGapCenterValue - 49000

theorem fullRecordGapTerm03631_eq_value :
    recordGapCenter - 49000 = fullRecordGapValue03631 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03631_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03631 (fullRecordGapValue03631 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03631_not_prime : ¬(recordGapCenter - 49000).Prime := by
  rw [fullRecordGapTerm03631_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03631, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03631_fast_pow_mod_ne_one

def fullRecordGapValue03632 : Nat := fullRecordGapCenterValue - 48510

theorem fullRecordGapTerm03632_eq_value :
    recordGapCenter - 48510 = fullRecordGapValue03632 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03632_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03632 (fullRecordGapValue03632 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03632_not_prime : ¬(recordGapCenter - 48510).Prime := by
  rw [fullRecordGapTerm03632_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03632, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03632_fast_pow_mod_ne_one

def fullRecordGapValue03633 : Nat := fullRecordGapCenterValue - 48400

theorem fullRecordGapTerm03633_eq_value :
    recordGapCenter - 48400 = fullRecordGapValue03633 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03633_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03633 (fullRecordGapValue03633 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03633_not_prime : ¬(recordGapCenter - 48400).Prime := by
  rw [fullRecordGapTerm03633_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03633, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03633_fast_pow_mod_ne_one

def fullRecordGapValue03634 : Nat := fullRecordGapCenterValue - 48114

theorem fullRecordGapTerm03634_eq_value :
    recordGapCenter - 48114 = fullRecordGapValue03634 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03634_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03634 (fullRecordGapValue03634 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03634_not_prime : ¬(recordGapCenter - 48114).Prime := by
  rw [fullRecordGapTerm03634_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03634, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03634_fast_pow_mod_ne_one

def fullRecordGapValue03635 : Nat := fullRecordGapCenterValue - 47250

theorem fullRecordGapTerm03635_eq_value :
    recordGapCenter - 47250 = fullRecordGapValue03635 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03635_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03635 (fullRecordGapValue03635 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03635_not_prime : ¬(recordGapCenter - 47250).Prime := by
  rw [fullRecordGapTerm03635_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03635, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03635_fast_pow_mod_ne_one

def fullRecordGapValue03636 : Nat := fullRecordGapCenterValue - 46464

theorem fullRecordGapTerm03636_eq_value :
    recordGapCenter - 46464 = fullRecordGapValue03636 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03636_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03636 (fullRecordGapValue03636 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03636_not_prime : ¬(recordGapCenter - 46464).Prime := by
  rw [fullRecordGapTerm03636_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03636, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03636_fast_pow_mod_ne_one

def fullRecordGapValue03637 : Nat := fullRecordGapCenterValue - 46080

theorem fullRecordGapTerm03637_eq_value :
    recordGapCenter - 46080 = fullRecordGapValue03637 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03637_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03637 (fullRecordGapValue03637 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03637_not_prime : ¬(recordGapCenter - 46080).Prime := by
  rw [fullRecordGapTerm03637_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03637, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03637_fast_pow_mod_ne_one

def fullRecordGapValue03638 : Nat := fullRecordGapCenterValue - 45000

theorem fullRecordGapTerm03638_eq_value :
    recordGapCenter - 45000 = fullRecordGapValue03638 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03638_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03638 (fullRecordGapValue03638 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03638_not_prime : ¬(recordGapCenter - 45000).Prime := by
  rw [fullRecordGapTerm03638_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03638, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03638_fast_pow_mod_ne_one

def fullRecordGapValue03639 : Nat := fullRecordGapCenterValue - 44550

theorem fullRecordGapTerm03639_eq_value :
    recordGapCenter - 44550 = fullRecordGapValue03639 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03639_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03639 (fullRecordGapValue03639 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03639_not_prime : ¬(recordGapCenter - 44550).Prime := by
  rw [fullRecordGapTerm03639_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03639, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03639_fast_pow_mod_ne_one

def fullRecordGapValue03640 : Nat := fullRecordGapCenterValue - 43200

theorem fullRecordGapTerm03640_eq_value :
    recordGapCenter - 43200 = fullRecordGapValue03640 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03640_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03640 (fullRecordGapValue03640 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03640_not_prime : ¬(recordGapCenter - 43200).Prime := by
  rw [fullRecordGapTerm03640_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03640, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03640_fast_pow_mod_ne_one

def fullRecordGapValue03641 : Nat := fullRecordGapCenterValue - 42768

theorem fullRecordGapTerm03641_eq_value :
    recordGapCenter - 42768 = fullRecordGapValue03641 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03641_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03641 (fullRecordGapValue03641 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03641_not_prime : ¬(recordGapCenter - 42768).Prime := by
  rw [fullRecordGapTerm03641_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03641, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03641_fast_pow_mod_ne_one

def fullRecordGapValue03642 : Nat := fullRecordGapCenterValue - 42592

theorem fullRecordGapTerm03642_eq_value :
    recordGapCenter - 42592 = fullRecordGapValue03642 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03642_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03642 (fullRecordGapValue03642 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03642_not_prime : ¬(recordGapCenter - 42592).Prime := by
  rw [fullRecordGapTerm03642_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03642, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03642_fast_pow_mod_ne_one

def fullRecordGapValue03643 : Nat := fullRecordGapCenterValue - 41250

theorem fullRecordGapTerm03643_eq_value :
    recordGapCenter - 41250 = fullRecordGapValue03643 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03643_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03643 (fullRecordGapValue03643 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03643_not_prime : ¬(recordGapCenter - 41250).Prime := by
  rw [fullRecordGapTerm03643_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03643, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03643_fast_pow_mod_ne_one

def fullRecordGapValue03644 : Nat := fullRecordGapCenterValue - 41160

theorem fullRecordGapTerm03644_eq_value :
    recordGapCenter - 41160 = fullRecordGapValue03644 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03644_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03644 (fullRecordGapValue03644 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03644_not_prime : ¬(recordGapCenter - 41160).Prime := by
  rw [fullRecordGapTerm03644_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03644, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03644_fast_pow_mod_ne_one

def fullRecordGapValue03645 : Nat := fullRecordGapCenterValue - 40960

theorem fullRecordGapTerm03645_eq_value :
    recordGapCenter - 40960 = fullRecordGapValue03645 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03645_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03645 (fullRecordGapValue03645 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03645_not_prime : ¬(recordGapCenter - 40960).Prime := by
  rw [fullRecordGapTerm03645_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03645, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03645_fast_pow_mod_ne_one

def fullRecordGapValue03646 : Nat := fullRecordGapCenterValue - 40824

theorem fullRecordGapTerm03646_eq_value :
    recordGapCenter - 40824 = fullRecordGapValue03646 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03646_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03646 (fullRecordGapValue03646 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03646_not_prime : ¬(recordGapCenter - 40824).Prime := by
  rw [fullRecordGapTerm03646_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03646, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03646_fast_pow_mod_ne_one

def fullRecordGapValue03647 : Nat := fullRecordGapCenterValue - 39930

theorem fullRecordGapTerm03647_eq_value :
    recordGapCenter - 39930 = fullRecordGapValue03647 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03647_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03647 (fullRecordGapValue03647 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03647_not_prime : ¬(recordGapCenter - 39930).Prime := by
  rw [fullRecordGapTerm03647_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03647, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03647_fast_pow_mod_ne_one

def fullRecordGapValue03648 : Nat := fullRecordGapCenterValue - 39690

theorem fullRecordGapTerm03648_eq_value :
    recordGapCenter - 39690 = fullRecordGapValue03648 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03648_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03648 (fullRecordGapValue03648 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03648_not_prime : ¬(recordGapCenter - 39690).Prime := by
  rw [fullRecordGapTerm03648_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03648, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03648_fast_pow_mod_ne_one

def fullRecordGapValue03649 : Nat := fullRecordGapCenterValue - 39204

theorem fullRecordGapTerm03649_eq_value :
    recordGapCenter - 39204 = fullRecordGapValue03649 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03649_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03649 (fullRecordGapValue03649 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03649_not_prime : ¬(recordGapCenter - 39204).Prime := by
  rw [fullRecordGapTerm03649_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03649, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03649_fast_pow_mod_ne_one

def fullRecordGapValue03650 : Nat := fullRecordGapCenterValue - 38808

theorem fullRecordGapTerm03650_eq_value :
    recordGapCenter - 38808 = fullRecordGapValue03650 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03650_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03650 (fullRecordGapValue03650 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03650_not_prime : ¬(recordGapCenter - 38808).Prime := by
  rw [fullRecordGapTerm03650_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03650, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03650_fast_pow_mod_ne_one

def fullRecordGapValue03651 : Nat := fullRecordGapCenterValue - 38400

theorem fullRecordGapTerm03651_eq_value :
    recordGapCenter - 38400 = fullRecordGapValue03651 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03651_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03651 (fullRecordGapValue03651 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03651_not_prime : ¬(recordGapCenter - 38400).Prime := by
  rw [fullRecordGapTerm03651_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03651, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03651_fast_pow_mod_ne_one

def fullRecordGapValue03652 : Nat := fullRecordGapCenterValue - 37422

theorem fullRecordGapTerm03652_eq_value :
    recordGapCenter - 37422 = fullRecordGapValue03652 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03652_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03652 (fullRecordGapValue03652 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03652_not_prime : ¬(recordGapCenter - 37422).Prime := by
  rw [fullRecordGapTerm03652_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03652, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03652_fast_pow_mod_ne_one

def fullRecordGapValue03653 : Nat := fullRecordGapCenterValue - 37044

theorem fullRecordGapTerm03653_eq_value :
    recordGapCenter - 37044 = fullRecordGapValue03653 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03653_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03653 (fullRecordGapValue03653 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03653_not_prime : ¬(recordGapCenter - 37044).Prime := by
  rw [fullRecordGapTerm03653_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03653, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03653_fast_pow_mod_ne_one

def fullRecordGapValue03654 : Nat := fullRecordGapCenterValue - 35574

theorem fullRecordGapTerm03654_eq_value :
    recordGapCenter - 35574 = fullRecordGapValue03654 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03654_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03654 (fullRecordGapValue03654 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03654_not_prime : ¬(recordGapCenter - 35574).Prime := by
  rw [fullRecordGapTerm03654_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03654, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03654_fast_pow_mod_ne_one

def fullRecordGapValue03655 : Nat := fullRecordGapCenterValue - 34992

theorem fullRecordGapTerm03655_eq_value :
    recordGapCenter - 34992 = fullRecordGapValue03655 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03655_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03655 (fullRecordGapValue03655 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03655_not_prime : ¬(recordGapCenter - 34992).Prime := by
  rw [fullRecordGapTerm03655_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03655, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03655_fast_pow_mod_ne_one

def fullRecordGapValue03656 : Nat := fullRecordGapCenterValue - 34848

theorem fullRecordGapTerm03656_eq_value :
    recordGapCenter - 34848 = fullRecordGapValue03656 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03656_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03656 (fullRecordGapValue03656 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03656_not_prime : ¬(recordGapCenter - 34848).Prime := by
  rw [fullRecordGapTerm03656_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03656, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03656_fast_pow_mod_ne_one

def fullRecordGapValue03657 : Nat := fullRecordGapCenterValue - 34650

theorem fullRecordGapTerm03657_eq_value :
    recordGapCenter - 34650 = fullRecordGapValue03657 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03657_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03657 (fullRecordGapValue03657 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03657_not_prime : ¬(recordGapCenter - 34650).Prime := by
  rw [fullRecordGapTerm03657_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03657, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03657_fast_pow_mod_ne_one

def fullRecordGapValue03658 : Nat := fullRecordGapCenterValue - 33792

theorem fullRecordGapTerm03658_eq_value :
    recordGapCenter - 33792 = fullRecordGapValue03658 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03658_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03658 (fullRecordGapValue03658 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03658_not_prime : ¬(recordGapCenter - 33792).Prime := by
  rw [fullRecordGapTerm03658_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03658, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03658_fast_pow_mod_ne_one

def fullRecordGapValue03659 : Nat := fullRecordGapCenterValue - 33600

theorem fullRecordGapTerm03659_eq_value :
    recordGapCenter - 33600 = fullRecordGapValue03659 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03659_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03659 (fullRecordGapValue03659 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03659_not_prime : ¬(recordGapCenter - 33600).Prime := by
  rw [fullRecordGapTerm03659_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03659, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03659_fast_pow_mod_ne_one

def fullRecordGapValue03660 : Nat := fullRecordGapCenterValue - 33264

theorem fullRecordGapTerm03660_eq_value :
    recordGapCenter - 33264 = fullRecordGapValue03660 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03660_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03660 (fullRecordGapValue03660 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03660_not_prime : ¬(recordGapCenter - 33264).Prime := by
  rw [fullRecordGapTerm03660_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03660, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03660_fast_pow_mod_ne_one

def fullRecordGapValue03661 : Nat := fullRecordGapCenterValue - 33000

theorem fullRecordGapTerm03661_eq_value :
    recordGapCenter - 33000 = fullRecordGapValue03661 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03661_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03661 (fullRecordGapValue03661 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03661_not_prime : ¬(recordGapCenter - 33000).Prime := by
  rw [fullRecordGapTerm03661_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03661, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03661_fast_pow_mod_ne_one

def fullRecordGapValue03662 : Nat := fullRecordGapCenterValue - 32928

theorem fullRecordGapTerm03662_eq_value :
    recordGapCenter - 32928 = fullRecordGapValue03662 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03662_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03662 (fullRecordGapValue03662 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03662_not_prime : ¬(recordGapCenter - 32928).Prime := by
  rw [fullRecordGapTerm03662_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03662, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03662_fast_pow_mod_ne_one

def fullRecordGapValue03663 : Nat := fullRecordGapCenterValue - 32400

theorem fullRecordGapTerm03663_eq_value :
    recordGapCenter - 32400 = fullRecordGapValue03663 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03663_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03663 (fullRecordGapValue03663 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03663_not_prime : ¬(recordGapCenter - 32400).Prime := by
  rw [fullRecordGapTerm03663_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03663, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03663_fast_pow_mod_ne_one

def fullRecordGapValue03664 : Nat := fullRecordGapCenterValue - 31944

theorem fullRecordGapTerm03664_eq_value :
    recordGapCenter - 31944 = fullRecordGapValue03664 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03664_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03664 (fullRecordGapValue03664 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03664_not_prime : ¬(recordGapCenter - 31944).Prime := by
  rw [fullRecordGapTerm03664_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03664, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03664_fast_pow_mod_ne_one

def fullRecordGapValue03665 : Nat := fullRecordGapCenterValue - 31752

theorem fullRecordGapTerm03665_eq_value :
    recordGapCenter - 31752 = fullRecordGapValue03665 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03665_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03665 (fullRecordGapValue03665 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03665_not_prime : ¬(recordGapCenter - 31752).Prime := by
  rw [fullRecordGapTerm03665_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03665, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03665_fast_pow_mod_ne_one

def fullRecordGapValue03666 : Nat := fullRecordGapCenterValue - 31104

theorem fullRecordGapTerm03666_eq_value :
    recordGapCenter - 31104 = fullRecordGapValue03666 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03666_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03666 (fullRecordGapValue03666 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03666_not_prime : ¬(recordGapCenter - 31104).Prime := by
  rw [fullRecordGapTerm03666_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03666, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03666_fast_pow_mod_ne_one

def fullRecordGapValue03667 : Nat := fullRecordGapCenterValue - 30492

theorem fullRecordGapTerm03667_eq_value :
    recordGapCenter - 30492 = fullRecordGapValue03667 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03667_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03667 (fullRecordGapValue03667 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03667_not_prime : ¬(recordGapCenter - 30492).Prime := by
  rw [fullRecordGapTerm03667_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03667, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03667_fast_pow_mod_ne_one

def fullRecordGapValue03668 : Nat := fullRecordGapCenterValue - 30184

theorem fullRecordGapTerm03668_eq_value :
    recordGapCenter - 30184 = fullRecordGapValue03668 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03668_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03668 (fullRecordGapValue03668 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03668_not_prime : ¬(recordGapCenter - 30184).Prime := by
  rw [fullRecordGapTerm03668_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03668, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03668_fast_pow_mod_ne_one

def fullRecordGapValue03669 : Nat := fullRecordGapCenterValue - 29700

theorem fullRecordGapTerm03669_eq_value :
    recordGapCenter - 29700 = fullRecordGapValue03669 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03669_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03669 (fullRecordGapValue03669 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03669_not_prime : ¬(recordGapCenter - 29700).Prime := by
  rw [fullRecordGapTerm03669_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03669, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03669_fast_pow_mod_ne_one

def fullRecordGapValue03670 : Nat := fullRecordGapCenterValue - 29568

theorem fullRecordGapTerm03670_eq_value :
    recordGapCenter - 29568 = fullRecordGapValue03670 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03670_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03670 (fullRecordGapValue03670 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03670_not_prime : ¬(recordGapCenter - 29568).Prime := by
  rw [fullRecordGapTerm03670_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03670, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03670_fast_pow_mod_ne_one

def fullRecordGapValue03671 : Nat := fullRecordGapCenterValue - 29400

theorem fullRecordGapTerm03671_eq_value :
    recordGapCenter - 29400 = fullRecordGapValue03671 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03671_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03671 (fullRecordGapValue03671 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03671_not_prime : ¬(recordGapCenter - 29400).Prime := by
  rw [fullRecordGapTerm03671_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03671, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03671_fast_pow_mod_ne_one

def fullRecordGapValue03672 : Nat := fullRecordGapCenterValue - 29040

theorem fullRecordGapTerm03672_eq_value :
    recordGapCenter - 29040 = fullRecordGapValue03672 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03672_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03672 (fullRecordGapValue03672 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03672_not_prime : ¬(recordGapCenter - 29040).Prime := by
  rw [fullRecordGapTerm03672_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03672, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03672_fast_pow_mod_ne_one

def fullRecordGapValue03673 : Nat := fullRecordGapCenterValue - 28812

theorem fullRecordGapTerm03673_eq_value :
    recordGapCenter - 28812 = fullRecordGapValue03673 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03673_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03673 (fullRecordGapValue03673 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03673_not_prime : ¬(recordGapCenter - 28812).Prime := by
  rw [fullRecordGapTerm03673_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03673, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03673_fast_pow_mod_ne_one

def fullRecordGapValue03674 : Nat := fullRecordGapCenterValue - 28672

theorem fullRecordGapTerm03674_eq_value :
    recordGapCenter - 28672 = fullRecordGapValue03674 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03674_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03674 (fullRecordGapValue03674 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03674_not_prime : ¬(recordGapCenter - 28672).Prime := by
  rw [fullRecordGapTerm03674_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03674, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03674_fast_pow_mod_ne_one

def fullRecordGapValue03675 : Nat := fullRecordGapCenterValue - 27720

theorem fullRecordGapTerm03675_eq_value :
    recordGapCenter - 27720 = fullRecordGapValue03675 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03675_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03675 (fullRecordGapValue03675 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03675_not_prime : ¬(recordGapCenter - 27720).Prime := by
  rw [fullRecordGapTerm03675_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03675, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03675_fast_pow_mod_ne_one

def fullRecordGapValue03676 : Nat := fullRecordGapCenterValue - 26880

theorem fullRecordGapTerm03676_eq_value :
    recordGapCenter - 26880 = fullRecordGapValue03676 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03676_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03676 (fullRecordGapValue03676 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03676_not_prime : ¬(recordGapCenter - 26880).Prime := by
  rw [fullRecordGapTerm03676_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03676, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03676_fast_pow_mod_ne_one

def fullRecordGapValue03677 : Nat := fullRecordGapCenterValue - 26730

theorem fullRecordGapTerm03677_eq_value :
    recordGapCenter - 26730 = fullRecordGapValue03677 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03677_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03677 (fullRecordGapValue03677 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03677_not_prime : ¬(recordGapCenter - 26730).Prime := by
  rw [fullRecordGapTerm03677_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03677, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03677_fast_pow_mod_ne_one

def fullRecordGapValue03678 : Nat := fullRecordGapCenterValue - 26460

theorem fullRecordGapTerm03678_eq_value :
    recordGapCenter - 26460 = fullRecordGapValue03678 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03678_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03678 (fullRecordGapValue03678 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03678_not_prime : ¬(recordGapCenter - 26460).Prime := by
  rw [fullRecordGapTerm03678_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03678, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03678_fast_pow_mod_ne_one

def fullRecordGapValue03679 : Nat := fullRecordGapCenterValue - 24640

theorem fullRecordGapTerm03679_eq_value :
    recordGapCenter - 24640 = fullRecordGapValue03679 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03679_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03679 (fullRecordGapValue03679 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03679_not_prime : ¬(recordGapCenter - 24640).Prime := by
  rw [fullRecordGapTerm03679_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03679, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03679_fast_pow_mod_ne_one

def fullRecordGapValue03680 : Nat := fullRecordGapCenterValue - 24192

theorem fullRecordGapTerm03680_eq_value :
    recordGapCenter - 24192 = fullRecordGapValue03680 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03680_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03680 (fullRecordGapValue03680 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03680_not_prime : ¬(recordGapCenter - 24192).Prime := by
  rw [fullRecordGapTerm03680_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03680, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03680_fast_pow_mod_ne_one

def fullRecordGapValue03681 : Nat := fullRecordGapCenterValue - 24010

theorem fullRecordGapTerm03681_eq_value :
    recordGapCenter - 24010 = fullRecordGapValue03681 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03681_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03681 (fullRecordGapValue03681 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03681_not_prime : ¬(recordGapCenter - 24010).Prime := by
  rw [fullRecordGapTerm03681_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03681, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03681_fast_pow_mod_ne_one

def fullRecordGapValue03682 : Nat := fullRecordGapCenterValue - 24000

theorem fullRecordGapTerm03682_eq_value :
    recordGapCenter - 24000 = fullRecordGapValue03682 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03682_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03682 (fullRecordGapValue03682 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03682_not_prime : ¬(recordGapCenter - 24000).Prime := by
  rw [fullRecordGapTerm03682_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03682, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03682_fast_pow_mod_ne_one

def fullRecordGapValue03683 : Nat := fullRecordGapCenterValue - 23958

theorem fullRecordGapTerm03683_eq_value :
    recordGapCenter - 23958 = fullRecordGapValue03683 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03683_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03683 (fullRecordGapValue03683 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03683_not_prime : ¬(recordGapCenter - 23958).Prime := by
  rw [fullRecordGapTerm03683_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03683, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03683_fast_pow_mod_ne_one

def fullRecordGapValue03684 : Nat := fullRecordGapCenterValue - 23814

theorem fullRecordGapTerm03684_eq_value :
    recordGapCenter - 23814 = fullRecordGapValue03684 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03684_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03684 (fullRecordGapValue03684 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03684_not_prime : ¬(recordGapCenter - 23814).Prime := by
  rw [fullRecordGapTerm03684_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03684, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03684_fast_pow_mod_ne_one

def fullRecordGapValue03685 : Nat := fullRecordGapCenterValue - 23520

theorem fullRecordGapTerm03685_eq_value :
    recordGapCenter - 23520 = fullRecordGapValue03685 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03685_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03685 (fullRecordGapValue03685 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03685_not_prime : ¬(recordGapCenter - 23520).Prime := by
  rw [fullRecordGapTerm03685_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03685, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03685_fast_pow_mod_ne_one

def fullRecordGapValue03686 : Nat := fullRecordGapCenterValue - 21870

theorem fullRecordGapTerm03686_eq_value :
    recordGapCenter - 21870 = fullRecordGapValue03686 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03686_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03686 (fullRecordGapValue03686 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03686_not_prime : ¬(recordGapCenter - 21870).Prime := by
  rw [fullRecordGapTerm03686_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03686, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03686_fast_pow_mod_ne_one

def fullRecordGapValue03687 : Nat := fullRecordGapCenterValue - 21600

theorem fullRecordGapTerm03687_eq_value :
    recordGapCenter - 21600 = fullRecordGapValue03687 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03687_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03687 (fullRecordGapValue03687 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03687_not_prime : ¬(recordGapCenter - 21600).Prime := by
  rw [fullRecordGapTerm03687_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03687, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03687_fast_pow_mod_ne_one

def fullRecordGapValue03688 : Nat := fullRecordGapCenterValue - 21504

theorem fullRecordGapTerm03688_eq_value :
    recordGapCenter - 21504 = fullRecordGapValue03688 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03688_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03688 (fullRecordGapValue03688 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03688_not_prime : ¬(recordGapCenter - 21504).Prime := by
  rw [fullRecordGapTerm03688_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03688, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03688_fast_pow_mod_ne_one

def fullRecordGapValue03689 : Nat := fullRecordGapCenterValue - 21384

theorem fullRecordGapTerm03689_eq_value :
    recordGapCenter - 21384 = fullRecordGapValue03689 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03689_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03689 (fullRecordGapValue03689 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03689_not_prime : ¬(recordGapCenter - 21384).Prime := by
  rw [fullRecordGapTerm03689_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03689, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03689_fast_pow_mod_ne_one

def fullRecordGapValue03690 : Nat := fullRecordGapCenterValue - 21000

theorem fullRecordGapTerm03690_eq_value :
    recordGapCenter - 21000 = fullRecordGapValue03690 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03690_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03690 (fullRecordGapValue03690 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03690_not_prime : ¬(recordGapCenter - 21000).Prime := by
  rw [fullRecordGapTerm03690_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03690, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03690_fast_pow_mod_ne_one

def fullRecordGapValue03691 : Nat := fullRecordGapCenterValue - 20412

theorem fullRecordGapTerm03691_eq_value :
    recordGapCenter - 20412 = fullRecordGapValue03691 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03691_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03691 (fullRecordGapValue03691 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03691_not_prime : ¬(recordGapCenter - 20412).Prime := by
  rw [fullRecordGapTerm03691_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03691, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03691_fast_pow_mod_ne_one

def fullRecordGapValue03692 : Nat := fullRecordGapCenterValue - 20160

theorem fullRecordGapTerm03692_eq_value :
    recordGapCenter - 20160 = fullRecordGapValue03692 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03692_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03692 (fullRecordGapValue03692 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03692_not_prime : ¬(recordGapCenter - 20160).Prime := by
  rw [fullRecordGapTerm03692_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03692, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03692_fast_pow_mod_ne_one

def fullRecordGapValue03693 : Nat := fullRecordGapCenterValue - 19600

theorem fullRecordGapTerm03693_eq_value :
    recordGapCenter - 19600 = fullRecordGapValue03693 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03693_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03693 (fullRecordGapValue03693 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03693_not_prime : ¬(recordGapCenter - 19600).Prime := by
  rw [fullRecordGapTerm03693_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03693, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03693_fast_pow_mod_ne_one

def fullRecordGapValue03694 : Nat := fullRecordGapCenterValue - 18900

theorem fullRecordGapTerm03694_eq_value :
    recordGapCenter - 18900 = fullRecordGapValue03694 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03694_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03694 (fullRecordGapValue03694 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03694_not_prime : ¬(recordGapCenter - 18900).Prime := by
  rw [fullRecordGapTerm03694_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03694, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03694_fast_pow_mod_ne_one

def fullRecordGapValue03695 : Nat := fullRecordGapCenterValue - 17280

theorem fullRecordGapTerm03695_eq_value :
    recordGapCenter - 17280 = fullRecordGapValue03695 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03695_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03695 (fullRecordGapValue03695 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03695_not_prime : ¬(recordGapCenter - 17280).Prime := by
  rw [fullRecordGapTerm03695_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03695, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03695_fast_pow_mod_ne_one

def fullRecordGapValue03696 : Nat := fullRecordGapCenterValue - 16632

theorem fullRecordGapTerm03696_eq_value :
    recordGapCenter - 16632 = fullRecordGapValue03696 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03696_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03696 (fullRecordGapValue03696 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03696_not_prime : ¬(recordGapCenter - 16632).Prime := by
  rw [fullRecordGapTerm03696_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03696, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03696_fast_pow_mod_ne_one

def fullRecordGapValue03697 : Nat := fullRecordGapCenterValue - 16200

theorem fullRecordGapTerm03697_eq_value :
    recordGapCenter - 16200 = fullRecordGapValue03697 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03697_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03697 (fullRecordGapValue03697 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03697_not_prime : ¬(recordGapCenter - 16200).Prime := by
  rw [fullRecordGapTerm03697_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03697, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03697_fast_pow_mod_ne_one

def fullRecordGapValue03698 : Nat := fullRecordGapCenterValue - 16170

theorem fullRecordGapTerm03698_eq_value :
    recordGapCenter - 16170 = fullRecordGapValue03698 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03698_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03698 (fullRecordGapValue03698 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03698_not_prime : ¬(recordGapCenter - 16170).Prime := by
  rw [fullRecordGapTerm03698_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03698, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03698_fast_pow_mod_ne_one

def fullRecordGapValue03699 : Nat := fullRecordGapCenterValue - 15120

theorem fullRecordGapTerm03699_eq_value :
    recordGapCenter - 15120 = fullRecordGapValue03699 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03699_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03699 (fullRecordGapValue03699 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03699_not_prime : ¬(recordGapCenter - 15120).Prime := by
  rw [fullRecordGapTerm03699_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03699, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03699_fast_pow_mod_ne_one

def fullRecordGapValue03700 : Nat := fullRecordGapCenterValue - 14520

theorem fullRecordGapTerm03700_eq_value :
    recordGapCenter - 14520 = fullRecordGapValue03700 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03700_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03700 (fullRecordGapValue03700 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03700_not_prime : ¬(recordGapCenter - 14520).Prime := by
  rw [fullRecordGapTerm03700_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03700, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03700_fast_pow_mod_ne_one

def fullRecordGapValue03701 : Nat := fullRecordGapCenterValue - 13824

theorem fullRecordGapTerm03701_eq_value :
    recordGapCenter - 13824 = fullRecordGapValue03701 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03701_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03701 (fullRecordGapValue03701 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03701_not_prime : ¬(recordGapCenter - 13824).Prime := by
  rw [fullRecordGapTerm03701_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03701, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03701_fast_pow_mod_ne_one

def fullRecordGapValue03702 : Nat := fullRecordGapCenterValue - 13750

theorem fullRecordGapTerm03702_eq_value :
    recordGapCenter - 13750 = fullRecordGapValue03702 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03702_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03702 (fullRecordGapValue03702 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03702_not_prime : ¬(recordGapCenter - 13750).Prime := by
  rw [fullRecordGapTerm03702_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03702, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03702_fast_pow_mod_ne_one

def fullRecordGapValue03703 : Nat := fullRecordGapCenterValue - 13720

theorem fullRecordGapTerm03703_eq_value :
    recordGapCenter - 13720 = fullRecordGapValue03703 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03703_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03703 (fullRecordGapValue03703 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03703_not_prime : ¬(recordGapCenter - 13720).Prime := by
  rw [fullRecordGapTerm03703_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03703, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03703_fast_pow_mod_ne_one

def fullRecordGapValue03704 : Nat := fullRecordGapCenterValue - 13500

theorem fullRecordGapTerm03704_eq_value :
    recordGapCenter - 13500 = fullRecordGapValue03704 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03704_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03704 (fullRecordGapValue03704 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03704_not_prime : ¬(recordGapCenter - 13500).Prime := by
  rw [fullRecordGapTerm03704_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03704, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03704_fast_pow_mod_ne_one

def fullRecordGapValue03705 : Nat := fullRecordGapCenterValue - 13440

theorem fullRecordGapTerm03705_eq_value :
    recordGapCenter - 13440 = fullRecordGapValue03705 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03705_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03705 (fullRecordGapValue03705 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03705_not_prime : ¬(recordGapCenter - 13440).Prime := by
  rw [fullRecordGapTerm03705_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03705, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03705_fast_pow_mod_ne_one

def fullRecordGapValue03706 : Nat := fullRecordGapCenterValue - 13068

theorem fullRecordGapTerm03706_eq_value :
    recordGapCenter - 13068 = fullRecordGapValue03706 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03706_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03706 (fullRecordGapValue03706 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03706_not_prime : ¬(recordGapCenter - 13068).Prime := by
  rw [fullRecordGapTerm03706_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03706, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03706_fast_pow_mod_ne_one

def fullRecordGapValue03707 : Nat := fullRecordGapCenterValue - 12960

theorem fullRecordGapTerm03707_eq_value :
    recordGapCenter - 12960 = fullRecordGapValue03707 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03707_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03707 (fullRecordGapValue03707 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03707_not_prime : ¬(recordGapCenter - 12960).Prime := by
  rw [fullRecordGapTerm03707_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03707, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03707_fast_pow_mod_ne_one

def fullRecordGapValue03708 : Nat := fullRecordGapCenterValue - 12672

theorem fullRecordGapTerm03708_eq_value :
    recordGapCenter - 12672 = fullRecordGapValue03708 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03708_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03708 (fullRecordGapValue03708 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03708_not_prime : ¬(recordGapCenter - 12672).Prime := by
  rw [fullRecordGapTerm03708_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03708, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03708_fast_pow_mod_ne_one

def fullRecordGapValue03709 : Nat := fullRecordGapCenterValue - 12150

theorem fullRecordGapTerm03709_eq_value :
    recordGapCenter - 12150 = fullRecordGapValue03709 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03709_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03709 (fullRecordGapValue03709 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03709_not_prime : ¬(recordGapCenter - 12150).Prime := by
  rw [fullRecordGapTerm03709_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03709, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03709_fast_pow_mod_ne_one

def fullRecordGapValue03710 : Nat := fullRecordGapCenterValue - 12100

theorem fullRecordGapTerm03710_eq_value :
    recordGapCenter - 12100 = fullRecordGapValue03710 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03710_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03710 (fullRecordGapValue03710 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03710_not_prime : ¬(recordGapCenter - 12100).Prime := by
  rw [fullRecordGapTerm03710_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03710, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03710_fast_pow_mod_ne_one

def fullRecordGapValue03711 : Nat := fullRecordGapCenterValue - 11760

theorem fullRecordGapTerm03711_eq_value :
    recordGapCenter - 11760 = fullRecordGapValue03711 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03711_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03711 (fullRecordGapValue03711 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03711_not_prime : ¬(recordGapCenter - 11760).Prime := by
  rw [fullRecordGapTerm03711_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03711, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03711_fast_pow_mod_ne_one

def fullRecordGapValue03712 : Nat := fullRecordGapCenterValue - 11340

theorem fullRecordGapTerm03712_eq_value :
    recordGapCenter - 11340 = fullRecordGapValue03712 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03712_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03712 (fullRecordGapValue03712 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03712_not_prime : ¬(recordGapCenter - 11340).Prime := by
  rw [fullRecordGapTerm03712_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03712, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03712_fast_pow_mod_ne_one

def fullRecordGapValue03713 : Nat := fullRecordGapCenterValue - 11200

theorem fullRecordGapTerm03713_eq_value :
    recordGapCenter - 11200 = fullRecordGapValue03713 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03713_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03713 (fullRecordGapValue03713 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03713_not_prime : ¬(recordGapCenter - 11200).Prime := by
  rw [fullRecordGapTerm03713_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03713, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03713_fast_pow_mod_ne_one

def fullRecordGapValue03714 : Nat := fullRecordGapCenterValue - 11088

theorem fullRecordGapTerm03714_eq_value :
    recordGapCenter - 11088 = fullRecordGapValue03714 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03714_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03714 (fullRecordGapValue03714 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03714_not_prime : ¬(recordGapCenter - 11088).Prime := by
  rw [fullRecordGapTerm03714_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03714, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03714_fast_pow_mod_ne_one

def fullRecordGapValue03715 : Nat := fullRecordGapCenterValue - 10800

theorem fullRecordGapTerm03715_eq_value :
    recordGapCenter - 10800 = fullRecordGapValue03715 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03715_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03715 (fullRecordGapValue03715 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03715_not_prime : ¬(recordGapCenter - 10800).Prime := by
  rw [fullRecordGapTerm03715_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03715, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03715_fast_pow_mod_ne_one

def fullRecordGapValue03716 : Nat := fullRecordGapCenterValue - 10692

theorem fullRecordGapTerm03716_eq_value :
    recordGapCenter - 10692 = fullRecordGapValue03716 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03716_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03716 (fullRecordGapValue03716 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03716_not_prime : ¬(recordGapCenter - 10692).Prime := by
  rw [fullRecordGapTerm03716_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03716, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03716_fast_pow_mod_ne_one

def fullRecordGapValue03717 : Nat := fullRecordGapCenterValue - 10290

theorem fullRecordGapTerm03717_eq_value :
    recordGapCenter - 10290 = fullRecordGapValue03717 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03717_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03717 (fullRecordGapValue03717 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03717_not_prime : ¬(recordGapCenter - 10290).Prime := by
  rw [fullRecordGapTerm03717_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03717, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03717_fast_pow_mod_ne_one

def fullRecordGapValue03718 : Nat := fullRecordGapCenterValue - 10000

theorem fullRecordGapTerm03718_eq_value :
    recordGapCenter - 10000 = fullRecordGapValue03718 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03718_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03718 (fullRecordGapValue03718 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03718_not_prime : ¬(recordGapCenter - 10000).Prime := by
  rw [fullRecordGapTerm03718_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03718, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03718_fast_pow_mod_ne_one

def fullRecordGapValue03719 : Nat := fullRecordGapCenterValue - 9900

theorem fullRecordGapTerm03719_eq_value :
    recordGapCenter - 9900 = fullRecordGapValue03719 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03719_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03719 (fullRecordGapValue03719 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03719_not_prime : ¬(recordGapCenter - 9900).Prime := by
  rw [fullRecordGapTerm03719_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03719, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03719_fast_pow_mod_ne_one

def fullRecordGapValue03720 : Nat := fullRecordGapCenterValue - 9720

theorem fullRecordGapTerm03720_eq_value :
    recordGapCenter - 9720 = fullRecordGapValue03720 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03720_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03720 (fullRecordGapValue03720 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03720_not_prime : ¬(recordGapCenter - 9720).Prime := by
  rw [fullRecordGapTerm03720_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03720, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03720_fast_pow_mod_ne_one

def fullRecordGapValue03721 : Nat := fullRecordGapCenterValue - 9702

theorem fullRecordGapTerm03721_eq_value :
    recordGapCenter - 9702 = fullRecordGapValue03721 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03721_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03721 (fullRecordGapValue03721 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03721_not_prime : ¬(recordGapCenter - 9702).Prime := by
  rw [fullRecordGapTerm03721_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03721, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03721_fast_pow_mod_ne_one

def fullRecordGapValue03722 : Nat := fullRecordGapCenterValue - 9604

theorem fullRecordGapTerm03722_eq_value :
    recordGapCenter - 9604 = fullRecordGapValue03722 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03722_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03722 (fullRecordGapValue03722 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03722_not_prime : ¬(recordGapCenter - 9604).Prime := by
  rw [fullRecordGapTerm03722_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03722, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03722_fast_pow_mod_ne_one

def fullRecordGapValue03723 : Nat := fullRecordGapCenterValue - 9504

theorem fullRecordGapTerm03723_eq_value :
    recordGapCenter - 9504 = fullRecordGapValue03723 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03723_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03723 (fullRecordGapValue03723 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03723_not_prime : ¬(recordGapCenter - 9504).Prime := by
  rw [fullRecordGapTerm03723_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03723, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03723_fast_pow_mod_ne_one

def fullRecordGapValue03724 : Nat := fullRecordGapCenterValue - 9240

theorem fullRecordGapTerm03724_eq_value :
    recordGapCenter - 9240 = fullRecordGapValue03724 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03724_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03724 (fullRecordGapValue03724 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03724_not_prime : ¬(recordGapCenter - 9240).Prime := by
  rw [fullRecordGapTerm03724_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03724, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03724_fast_pow_mod_ne_one

def fullRecordGapValue03725 : Nat := fullRecordGapCenterValue - 9000

theorem fullRecordGapTerm03725_eq_value :
    recordGapCenter - 9000 = fullRecordGapValue03725 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03725_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03725 (fullRecordGapValue03725 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03725_not_prime : ¬(recordGapCenter - 9000).Prime := by
  rw [fullRecordGapTerm03725_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03725, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03725_fast_pow_mod_ne_one

def fullRecordGapValue03726 : Nat := fullRecordGapCenterValue - 8820

theorem fullRecordGapTerm03726_eq_value :
    recordGapCenter - 8820 = fullRecordGapValue03726 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03726_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03726 (fullRecordGapValue03726 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03726_not_prime : ¬(recordGapCenter - 8820).Prime := by
  rw [fullRecordGapTerm03726_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03726, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03726_fast_pow_mod_ne_one

def fullRecordGapValue03727 : Nat := fullRecordGapCenterValue - 7938

theorem fullRecordGapTerm03727_eq_value :
    recordGapCenter - 7938 = fullRecordGapValue03727 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03727_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03727 (fullRecordGapValue03727 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03727_not_prime : ¬(recordGapCenter - 7938).Prime := by
  rw [fullRecordGapTerm03727_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03727, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03727_fast_pow_mod_ne_one

def fullRecordGapValue03728 : Nat := fullRecordGapCenterValue - 7840

theorem fullRecordGapTerm03728_eq_value :
    recordGapCenter - 7840 = fullRecordGapValue03728 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03728_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03728 (fullRecordGapValue03728 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03728_not_prime : ¬(recordGapCenter - 7840).Prime := by
  rw [fullRecordGapTerm03728_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03728, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03728_fast_pow_mod_ne_one

def fullRecordGapValue03729 : Nat := fullRecordGapCenterValue - 7500

theorem fullRecordGapTerm03729_eq_value :
    recordGapCenter - 7500 = fullRecordGapValue03729 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03729_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03729 (fullRecordGapValue03729 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03729_not_prime : ¬(recordGapCenter - 7500).Prime := by
  rw [fullRecordGapTerm03729_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03729, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03729_fast_pow_mod_ne_one

def fullRecordGapValue03730 : Nat := fullRecordGapCenterValue - 6750

theorem fullRecordGapTerm03730_eq_value :
    recordGapCenter - 6750 = fullRecordGapValue03730 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03730_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03730 (fullRecordGapValue03730 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03730_not_prime : ¬(recordGapCenter - 6750).Prime := by
  rw [fullRecordGapTerm03730_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03730, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03730_fast_pow_mod_ne_one

def fullRecordGapValue03731 : Nat := fullRecordGapCenterValue - 6600

theorem fullRecordGapTerm03731_eq_value :
    recordGapCenter - 6600 = fullRecordGapValue03731 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03731_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03731 (fullRecordGapValue03731 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03731_not_prime : ¬(recordGapCenter - 6600).Prime := by
  rw [fullRecordGapTerm03731_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03731, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03731_fast_pow_mod_ne_one

def fullRecordGapValue03732 : Nat := fullRecordGapCenterValue - 6468

theorem fullRecordGapTerm03732_eq_value :
    recordGapCenter - 6468 = fullRecordGapValue03732 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03732_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03732 (fullRecordGapValue03732 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03732_not_prime : ¬(recordGapCenter - 6468).Prime := by
  rw [fullRecordGapTerm03732_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03732, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03732_fast_pow_mod_ne_one

def fullRecordGapValue03733 : Nat := fullRecordGapCenterValue - 6400

theorem fullRecordGapTerm03733_eq_value :
    recordGapCenter - 6400 = fullRecordGapValue03733 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03733_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03733 (fullRecordGapValue03733 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03733_not_prime : ¬(recordGapCenter - 6400).Prime := by
  rw [fullRecordGapTerm03733_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03733, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03733_fast_pow_mod_ne_one

def fullRecordGapValue03734 : Nat := fullRecordGapCenterValue - 6250

theorem fullRecordGapTerm03734_eq_value :
    recordGapCenter - 6250 = fullRecordGapValue03734 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03734_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03734 (fullRecordGapValue03734 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03734_not_prime : ¬(recordGapCenter - 6250).Prime := by
  rw [fullRecordGapTerm03734_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03734, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03734_fast_pow_mod_ne_one

def fullRecordGapValue03735 : Nat := fullRecordGapCenterValue - 6174

theorem fullRecordGapTerm03735_eq_value :
    recordGapCenter - 6174 = fullRecordGapValue03735 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03735_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03735 (fullRecordGapValue03735 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03735_not_prime : ¬(recordGapCenter - 6174).Prime := by
  rw [fullRecordGapTerm03735_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03735, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03735_fast_pow_mod_ne_one

def fullRecordGapValue03736 : Nat := fullRecordGapCenterValue - 6160

theorem fullRecordGapTerm03736_eq_value :
    recordGapCenter - 6160 = fullRecordGapValue03736 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03736_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03736 (fullRecordGapValue03736 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03736_not_prime : ¬(recordGapCenter - 6160).Prime := by
  rw [fullRecordGapTerm03736_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03736, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03736_fast_pow_mod_ne_one

def fullRecordGapValue03737 : Nat := fullRecordGapCenterValue - 6048

theorem fullRecordGapTerm03737_eq_value :
    recordGapCenter - 6048 = fullRecordGapValue03737 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03737_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03737 (fullRecordGapValue03737 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03737_not_prime : ¬(recordGapCenter - 6048).Prime := by
  rw [fullRecordGapTerm03737_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03737, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03737_fast_pow_mod_ne_one

def fullRecordGapValue03738 : Nat := fullRecordGapCenterValue - 5940

theorem fullRecordGapTerm03738_eq_value :
    recordGapCenter - 5940 = fullRecordGapValue03738 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03738_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03738 (fullRecordGapValue03738 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03738_not_prime : ¬(recordGapCenter - 5940).Prime := by
  rw [fullRecordGapTerm03738_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03738, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03738_fast_pow_mod_ne_one

def fullRecordGapValue03739 : Nat := fullRecordGapCenterValue - 5880

theorem fullRecordGapTerm03739_eq_value :
    recordGapCenter - 5880 = fullRecordGapValue03739 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03739_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03739 (fullRecordGapValue03739 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03739_not_prime : ¬(recordGapCenter - 5880).Prime := by
  rw [fullRecordGapTerm03739_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03739, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03739_fast_pow_mod_ne_one

def fullRecordGapValue03740 : Nat := fullRecordGapCenterValue - 5670

theorem fullRecordGapTerm03740_eq_value :
    recordGapCenter - 5670 = fullRecordGapValue03740 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03740_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03740 (fullRecordGapValue03740 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03740_not_prime : ¬(recordGapCenter - 5670).Prime := by
  rw [fullRecordGapTerm03740_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03740, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03740_fast_pow_mod_ne_one

def fullRecordGapValue03741 : Nat := fullRecordGapCenterValue - 5544

theorem fullRecordGapTerm03741_eq_value :
    recordGapCenter - 5544 = fullRecordGapValue03741 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03741_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03741 (fullRecordGapValue03741 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03741_not_prime : ¬(recordGapCenter - 5544).Prime := by
  rw [fullRecordGapTerm03741_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03741, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03741_fast_pow_mod_ne_one

def fullRecordGapValue03742 : Nat := fullRecordGapCenterValue - 5500

theorem fullRecordGapTerm03742_eq_value :
    recordGapCenter - 5500 = fullRecordGapValue03742 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03742_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03742 (fullRecordGapValue03742 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03742_not_prime : ¬(recordGapCenter - 5500).Prime := by
  rw [fullRecordGapTerm03742_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03742, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03742_fast_pow_mod_ne_one

def fullRecordGapValue03743 : Nat := fullRecordGapCenterValue - 5488

theorem fullRecordGapTerm03743_eq_value :
    recordGapCenter - 5488 = fullRecordGapValue03743 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03743_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03743 (fullRecordGapValue03743 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03743_not_prime : ¬(recordGapCenter - 5488).Prime := by
  rw [fullRecordGapTerm03743_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03743, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03743_fast_pow_mod_ne_one

def fullRecordGapValue03744 : Nat := fullRecordGapCenterValue - 5400

theorem fullRecordGapTerm03744_eq_value :
    recordGapCenter - 5400 = fullRecordGapValue03744 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03744_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03744 (fullRecordGapValue03744 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03744_not_prime : ¬(recordGapCenter - 5400).Prime := by
  rw [fullRecordGapTerm03744_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03744, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03744_fast_pow_mod_ne_one

def fullRecordGapValue03745 : Nat := fullRecordGapCenterValue - 5292

theorem fullRecordGapTerm03745_eq_value :
    recordGapCenter - 5292 = fullRecordGapValue03745 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03745_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03745 (fullRecordGapValue03745 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03745_not_prime : ¬(recordGapCenter - 5292).Prime := by
  rw [fullRecordGapTerm03745_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03745, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03745_fast_pow_mod_ne_one

def fullRecordGapValue03746 : Nat := fullRecordGapCenterValue - 5280

theorem fullRecordGapTerm03746_eq_value :
    recordGapCenter - 5280 = fullRecordGapValue03746 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03746_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03746 (fullRecordGapValue03746 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03746_not_prime : ¬(recordGapCenter - 5280).Prime := by
  rw [fullRecordGapTerm03746_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03746, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03746_fast_pow_mod_ne_one

def fullRecordGapValue03747 : Nat := fullRecordGapCenterValue - 5250

theorem fullRecordGapTerm03747_eq_value :
    recordGapCenter - 5250 = fullRecordGapValue03747 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03747_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03747 (fullRecordGapValue03747 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03747_not_prime : ¬(recordGapCenter - 5250).Prime := by
  rw [fullRecordGapTerm03747_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03747, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03747_fast_pow_mod_ne_one

def fullRecordGapValue03748 : Nat := fullRecordGapCenterValue - 4840

theorem fullRecordGapTerm03748_eq_value :
    recordGapCenter - 4840 = fullRecordGapValue03748 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03748_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03748 (fullRecordGapValue03748 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03748_not_prime : ¬(recordGapCenter - 4840).Prime := by
  rw [fullRecordGapTerm03748_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03748, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03748_fast_pow_mod_ne_one

def fullRecordGapValue03749 : Nat := fullRecordGapCenterValue - 4704

theorem fullRecordGapTerm03749_eq_value :
    recordGapCenter - 4704 = fullRecordGapValue03749 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03749_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03749 (fullRecordGapValue03749 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03749_not_prime : ¬(recordGapCenter - 4704).Prime := by
  rw [fullRecordGapTerm03749_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03749, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03749_fast_pow_mod_ne_one

def fullRecordGapValue03750 : Nat := fullRecordGapCenterValue - 4410

theorem fullRecordGapTerm03750_eq_value :
    recordGapCenter - 4410 = fullRecordGapValue03750 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03750_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03750 (fullRecordGapValue03750 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03750_not_prime : ¬(recordGapCenter - 4410).Prime := by
  rw [fullRecordGapTerm03750_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03750, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03750_fast_pow_mod_ne_one

def fullRecordGapValue03751 : Nat := fullRecordGapCenterValue - 4374

theorem fullRecordGapTerm03751_eq_value :
    recordGapCenter - 4374 = fullRecordGapValue03751 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03751_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03751 (fullRecordGapValue03751 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03751_not_prime : ¬(recordGapCenter - 4374).Prime := by
  rw [fullRecordGapTerm03751_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03751, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03751_fast_pow_mod_ne_one

def fullRecordGapValue03752 : Nat := fullRecordGapCenterValue - 4224

theorem fullRecordGapTerm03752_eq_value :
    recordGapCenter - 4224 = fullRecordGapValue03752 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03752_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03752 (fullRecordGapValue03752 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03752_not_prime : ¬(recordGapCenter - 4224).Prime := by
  rw [fullRecordGapTerm03752_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03752, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03752_fast_pow_mod_ne_one

def fullRecordGapValue03753 : Nat := fullRecordGapCenterValue - 4158

theorem fullRecordGapTerm03753_eq_value :
    recordGapCenter - 4158 = fullRecordGapValue03753 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03753_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03753 (fullRecordGapValue03753 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03753_not_prime : ¬(recordGapCenter - 4158).Prime := by
  rw [fullRecordGapTerm03753_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03753, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03753_fast_pow_mod_ne_one

def fullRecordGapValue03754 : Nat := fullRecordGapCenterValue - 4032

theorem fullRecordGapTerm03754_eq_value :
    recordGapCenter - 4032 = fullRecordGapValue03754 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03754_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03754 (fullRecordGapValue03754 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03754_not_prime : ¬(recordGapCenter - 4032).Prime := by
  rw [fullRecordGapTerm03754_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03754, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03754_fast_pow_mod_ne_one

def fullRecordGapValue03755 : Nat := fullRecordGapCenterValue - 3780

theorem fullRecordGapTerm03755_eq_value :
    recordGapCenter - 3780 = fullRecordGapValue03755 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03755_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03755 (fullRecordGapValue03755 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03755_not_prime : ¬(recordGapCenter - 3780).Prime := by
  rw [fullRecordGapTerm03755_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03755, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03755_fast_pow_mod_ne_one

def fullRecordGapValue03756 : Nat := fullRecordGapCenterValue - 3750

theorem fullRecordGapTerm03756_eq_value :
    recordGapCenter - 3750 = fullRecordGapValue03756 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03756_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03756 (fullRecordGapValue03756 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03756_not_prime : ¬(recordGapCenter - 3750).Prime := by
  rw [fullRecordGapTerm03756_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03756, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03756_fast_pow_mod_ne_one

def fullRecordGapValue03757 : Nat := fullRecordGapCenterValue - 3630

theorem fullRecordGapTerm03757_eq_value :
    recordGapCenter - 3630 = fullRecordGapValue03757 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03757_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03757 (fullRecordGapValue03757 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03757_not_prime : ¬(recordGapCenter - 3630).Prime := by
  rw [fullRecordGapTerm03757_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03757, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03757_fast_pow_mod_ne_one

def fullRecordGapValue03758 : Nat := fullRecordGapCenterValue - 3600

theorem fullRecordGapTerm03758_eq_value :
    recordGapCenter - 3600 = fullRecordGapValue03758 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03758_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03758 (fullRecordGapValue03758 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03758_not_prime : ¬(recordGapCenter - 3600).Prime := by
  rw [fullRecordGapTerm03758_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03758, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03758_fast_pow_mod_ne_one

def fullRecordGapValue03759 : Nat := fullRecordGapCenterValue - 3430

theorem fullRecordGapTerm03759_eq_value :
    recordGapCenter - 3430 = fullRecordGapValue03759 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03759_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03759 (fullRecordGapValue03759 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03759_not_prime : ¬(recordGapCenter - 3430).Prime := by
  rw [fullRecordGapTerm03759_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03759, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03759_fast_pow_mod_ne_one

def fullRecordGapValue03760 : Nat := fullRecordGapCenterValue - 3388

theorem fullRecordGapTerm03760_eq_value :
    recordGapCenter - 3388 = fullRecordGapValue03760 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03760_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03760 (fullRecordGapValue03760 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03760_not_prime : ¬(recordGapCenter - 3388).Prime := by
  rw [fullRecordGapTerm03760_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03760, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03760_fast_pow_mod_ne_one

def fullRecordGapValue03761 : Nat := fullRecordGapCenterValue - 3360

theorem fullRecordGapTerm03761_eq_value :
    recordGapCenter - 3360 = fullRecordGapValue03761 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03761_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03761 (fullRecordGapValue03761 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03761_not_prime : ¬(recordGapCenter - 3360).Prime := by
  rw [fullRecordGapTerm03761_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03761, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03761_fast_pow_mod_ne_one

def fullRecordGapValue03762 : Nat := fullRecordGapCenterValue - 3300

theorem fullRecordGapTerm03762_eq_value :
    recordGapCenter - 3300 = fullRecordGapValue03762 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03762_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03762 (fullRecordGapValue03762 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03762_not_prime : ¬(recordGapCenter - 3300).Prime := by
  rw [fullRecordGapTerm03762_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03762, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03762_fast_pow_mod_ne_one

def fullRecordGapValue03763 : Nat := fullRecordGapCenterValue - 3240

theorem fullRecordGapTerm03763_eq_value :
    recordGapCenter - 3240 = fullRecordGapValue03763 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03763_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03763 (fullRecordGapValue03763 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03763_not_prime : ¬(recordGapCenter - 3240).Prime := by
  rw [fullRecordGapTerm03763_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03763, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03763_fast_pow_mod_ne_one

def fullRecordGapValue03764 : Nat := fullRecordGapCenterValue - 2904

theorem fullRecordGapTerm03764_eq_value :
    recordGapCenter - 2904 = fullRecordGapValue03764 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03764_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03764 (fullRecordGapValue03764 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03764_not_prime : ¬(recordGapCenter - 2904).Prime := by
  rw [fullRecordGapTerm03764_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03764, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03764_fast_pow_mod_ne_one

def fullRecordGapValue03765 : Nat := fullRecordGapCenterValue - 2880

theorem fullRecordGapTerm03765_eq_value :
    recordGapCenter - 2880 = fullRecordGapValue03765 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03765_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03765 (fullRecordGapValue03765 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03765_not_prime : ¬(recordGapCenter - 2880).Prime := by
  rw [fullRecordGapTerm03765_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03765, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03765_fast_pow_mod_ne_one

def fullRecordGapValue03766 : Nat := fullRecordGapCenterValue - 2800

theorem fullRecordGapTerm03766_eq_value :
    recordGapCenter - 2800 = fullRecordGapValue03766 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03766_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03766 (fullRecordGapValue03766 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03766_not_prime : ¬(recordGapCenter - 2800).Prime := by
  rw [fullRecordGapTerm03766_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03766, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03766_fast_pow_mod_ne_one

def fullRecordGapValue03767 : Nat := fullRecordGapCenterValue - 2464

theorem fullRecordGapTerm03767_eq_value :
    recordGapCenter - 2464 = fullRecordGapValue03767 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03767_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03767 (fullRecordGapValue03767 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03767_not_prime : ¬(recordGapCenter - 2464).Prime := by
  rw [fullRecordGapTerm03767_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03767, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03767_fast_pow_mod_ne_one

def fullRecordGapValue03768 : Nat := fullRecordGapCenterValue - 2352

theorem fullRecordGapTerm03768_eq_value :
    recordGapCenter - 2352 = fullRecordGapValue03768 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03768_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03768 (fullRecordGapValue03768 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03768_not_prime : ¬(recordGapCenter - 2352).Prime := by
  rw [fullRecordGapTerm03768_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03768, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03768_fast_pow_mod_ne_one

def fullRecordGapValue03769 : Nat := fullRecordGapCenterValue - 2310

theorem fullRecordGapTerm03769_eq_value :
    recordGapCenter - 2310 = fullRecordGapValue03769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03769 (fullRecordGapValue03769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03769_not_prime : ¬(recordGapCenter - 2310).Prime := by
  rw [fullRecordGapTerm03769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03769_fast_pow_mod_ne_one

def fullRecordGapValue03770 : Nat := fullRecordGapCenterValue - 2250

theorem fullRecordGapTerm03770_eq_value :
    recordGapCenter - 2250 = fullRecordGapValue03770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03770 (fullRecordGapValue03770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03770_not_prime : ¬(recordGapCenter - 2250).Prime := by
  rw [fullRecordGapTerm03770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03770_fast_pow_mod_ne_one

def fullRecordGapValue03771 : Nat := fullRecordGapCenterValue - 2112

theorem fullRecordGapTerm03771_eq_value :
    recordGapCenter - 2112 = fullRecordGapValue03771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03771 (fullRecordGapValue03771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03771_not_prime : ¬(recordGapCenter - 2112).Prime := by
  rw [fullRecordGapTerm03771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03771_fast_pow_mod_ne_one

def fullRecordGapValue03772 : Nat := fullRecordGapCenterValue - 1980

theorem fullRecordGapTerm03772_eq_value :
    recordGapCenter - 1980 = fullRecordGapValue03772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03772 (fullRecordGapValue03772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03772_not_prime : ¬(recordGapCenter - 1980).Prime := by
  rw [fullRecordGapTerm03772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03772_fast_pow_mod_ne_one

def fullRecordGapValue03773 : Nat := fullRecordGapCenterValue - 1920

theorem fullRecordGapTerm03773_eq_value :
    recordGapCenter - 1920 = fullRecordGapValue03773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03773 (fullRecordGapValue03773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03773_not_prime : ¬(recordGapCenter - 1920).Prime := by
  rw [fullRecordGapTerm03773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03773_fast_pow_mod_ne_one

def fullRecordGapValue03774 : Nat := fullRecordGapCenterValue - 1890

theorem fullRecordGapTerm03774_eq_value :
    recordGapCenter - 1890 = fullRecordGapValue03774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03774 (fullRecordGapValue03774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03774_not_prime : ¬(recordGapCenter - 1890).Prime := by
  rw [fullRecordGapTerm03774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03774_fast_pow_mod_ne_one

def fullRecordGapValue03775 : Nat := fullRecordGapCenterValue - 1848

theorem fullRecordGapTerm03775_eq_value :
    recordGapCenter - 1848 = fullRecordGapValue03775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03775 (fullRecordGapValue03775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03775_not_prime : ¬(recordGapCenter - 1848).Prime := by
  rw [fullRecordGapTerm03775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03775_fast_pow_mod_ne_one

def fullRecordGapValue03776 : Nat := fullRecordGapCenterValue - 1750

theorem fullRecordGapTerm03776_eq_value :
    recordGapCenter - 1750 = fullRecordGapValue03776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03776 (fullRecordGapValue03776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03776_not_prime : ¬(recordGapCenter - 1750).Prime := by
  rw [fullRecordGapTerm03776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03776_fast_pow_mod_ne_one

def fullRecordGapValue03777 : Nat := fullRecordGapCenterValue - 1728

theorem fullRecordGapTerm03777_eq_value :
    recordGapCenter - 1728 = fullRecordGapValue03777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03777 (fullRecordGapValue03777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03777_not_prime : ¬(recordGapCenter - 1728).Prime := by
  rw [fullRecordGapTerm03777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03777_fast_pow_mod_ne_one

def fullRecordGapValue03778 : Nat := fullRecordGapCenterValue - 1620

theorem fullRecordGapTerm03778_eq_value :
    recordGapCenter - 1620 = fullRecordGapValue03778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03778 (fullRecordGapValue03778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03778_not_prime : ¬(recordGapCenter - 1620).Prime := by
  rw [fullRecordGapTerm03778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03778_fast_pow_mod_ne_one

def fullRecordGapValue03779 : Nat := fullRecordGapCenterValue - 1600

theorem fullRecordGapTerm03779_eq_value :
    recordGapCenter - 1600 = fullRecordGapValue03779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03779 (fullRecordGapValue03779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03779_not_prime : ¬(recordGapCenter - 1600).Prime := by
  rw [fullRecordGapTerm03779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03779_fast_pow_mod_ne_one

def fullRecordGapValue03780 : Nat := fullRecordGapCenterValue - 1584

theorem fullRecordGapTerm03780_eq_value :
    recordGapCenter - 1584 = fullRecordGapValue03780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03780 (fullRecordGapValue03780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03780_not_prime : ¬(recordGapCenter - 1584).Prime := by
  rw [fullRecordGapTerm03780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03780_fast_pow_mod_ne_one

def fullRecordGapValue03781 : Nat := fullRecordGapCenterValue - 1540

theorem fullRecordGapTerm03781_eq_value :
    recordGapCenter - 1540 = fullRecordGapValue03781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03781 (fullRecordGapValue03781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03781_not_prime : ¬(recordGapCenter - 1540).Prime := by
  rw [fullRecordGapTerm03781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03781_fast_pow_mod_ne_one

def fullRecordGapValue03782 : Nat := fullRecordGapCenterValue - 1470

theorem fullRecordGapTerm03782_eq_value :
    recordGapCenter - 1470 = fullRecordGapValue03782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03782 (fullRecordGapValue03782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03782_not_prime : ¬(recordGapCenter - 1470).Prime := by
  rw [fullRecordGapTerm03782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03782_fast_pow_mod_ne_one

def fullRecordGapValue03783 : Nat := fullRecordGapCenterValue - 1458

theorem fullRecordGapTerm03783_eq_value :
    recordGapCenter - 1458 = fullRecordGapValue03783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03783 (fullRecordGapValue03783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03783_not_prime : ¬(recordGapCenter - 1458).Prime := by
  rw [fullRecordGapTerm03783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03783_fast_pow_mod_ne_one

def fullRecordGapValue03784 : Nat := fullRecordGapCenterValue - 1372

theorem fullRecordGapTerm03784_eq_value :
    recordGapCenter - 1372 = fullRecordGapValue03784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03784 (fullRecordGapValue03784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03784_not_prime : ¬(recordGapCenter - 1372).Prime := by
  rw [fullRecordGapTerm03784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03784_fast_pow_mod_ne_one

def fullRecordGapValue03785 : Nat := fullRecordGapCenterValue - 1188

theorem fullRecordGapTerm03785_eq_value :
    recordGapCenter - 1188 = fullRecordGapValue03785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03785 (fullRecordGapValue03785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03785_not_prime : ¬(recordGapCenter - 1188).Prime := by
  rw [fullRecordGapTerm03785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03785_fast_pow_mod_ne_one

def fullRecordGapValue03786 : Nat := fullRecordGapCenterValue - 1152

theorem fullRecordGapTerm03786_eq_value :
    recordGapCenter - 1152 = fullRecordGapValue03786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03786 (fullRecordGapValue03786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03786_not_prime : ¬(recordGapCenter - 1152).Prime := by
  rw [fullRecordGapTerm03786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03786_fast_pow_mod_ne_one

def fullRecordGapValue03787 : Nat := fullRecordGapCenterValue - 1078

theorem fullRecordGapTerm03787_eq_value :
    recordGapCenter - 1078 = fullRecordGapValue03787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03787 (fullRecordGapValue03787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03787_not_prime : ¬(recordGapCenter - 1078).Prime := by
  rw [fullRecordGapTerm03787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03787_fast_pow_mod_ne_one

def fullRecordGapValue03788 : Nat := fullRecordGapCenterValue - 1000

theorem fullRecordGapTerm03788_eq_value :
    recordGapCenter - 1000 = fullRecordGapValue03788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03788 (fullRecordGapValue03788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03788_not_prime : ¬(recordGapCenter - 1000).Prime := by
  rw [fullRecordGapTerm03788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03788_fast_pow_mod_ne_one

def fullRecordGapValue03789 : Nat := fullRecordGapCenterValue - 880

theorem fullRecordGapTerm03789_eq_value :
    recordGapCenter - 880 = fullRecordGapValue03789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03789 (fullRecordGapValue03789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03789_not_prime : ¬(recordGapCenter - 880).Prime := by
  rw [fullRecordGapTerm03789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03789_fast_pow_mod_ne_one

def fullRecordGapValue03790 : Nat := fullRecordGapCenterValue - 810

theorem fullRecordGapTerm03790_eq_value :
    recordGapCenter - 810 = fullRecordGapValue03790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03790 (fullRecordGapValue03790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03790_not_prime : ¬(recordGapCenter - 810).Prime := by
  rw [fullRecordGapTerm03790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03790_fast_pow_mod_ne_one

def fullRecordGapValue03791 : Nat := fullRecordGapCenterValue - 768

theorem fullRecordGapTerm03791_eq_value :
    recordGapCenter - 768 = fullRecordGapValue03791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03791 (fullRecordGapValue03791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03791_not_prime : ¬(recordGapCenter - 768).Prime := by
  rw [fullRecordGapTerm03791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03791_fast_pow_mod_ne_one

def fullRecordGapValue03792 : Nat := fullRecordGapCenterValue - 648

theorem fullRecordGapTerm03792_eq_value :
    recordGapCenter - 648 = fullRecordGapValue03792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03792 (fullRecordGapValue03792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03792_not_prime : ¬(recordGapCenter - 648).Prime := by
  rw [fullRecordGapTerm03792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03792_fast_pow_mod_ne_one

def fullRecordGapValue03793 : Nat := fullRecordGapCenterValue - 600

theorem fullRecordGapTerm03793_eq_value :
    recordGapCenter - 600 = fullRecordGapValue03793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03793 (fullRecordGapValue03793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03793_not_prime : ¬(recordGapCenter - 600).Prime := by
  rw [fullRecordGapTerm03793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03793_fast_pow_mod_ne_one

def fullRecordGapValue03794 : Nat := fullRecordGapCenterValue - 594

theorem fullRecordGapTerm03794_eq_value :
    recordGapCenter - 594 = fullRecordGapValue03794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03794 (fullRecordGapValue03794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03794_not_prime : ¬(recordGapCenter - 594).Prime := by
  rw [fullRecordGapTerm03794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03794_fast_pow_mod_ne_one

def fullRecordGapValue03795 : Nat := fullRecordGapCenterValue - 588

theorem fullRecordGapTerm03795_eq_value :
    recordGapCenter - 588 = fullRecordGapValue03795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03795 (fullRecordGapValue03795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03795_not_prime : ¬(recordGapCenter - 588).Prime := by
  rw [fullRecordGapTerm03795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03795_fast_pow_mod_ne_one

def fullRecordGapValue03796 : Nat := fullRecordGapCenterValue - 462

theorem fullRecordGapTerm03796_eq_value :
    recordGapCenter - 462 = fullRecordGapValue03796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03796 (fullRecordGapValue03796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03796_not_prime : ¬(recordGapCenter - 462).Prime := by
  rw [fullRecordGapTerm03796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03796_fast_pow_mod_ne_one

def fullRecordGapValue03797 : Nat := fullRecordGapCenterValue - 448

theorem fullRecordGapTerm03797_eq_value :
    recordGapCenter - 448 = fullRecordGapValue03797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03797 (fullRecordGapValue03797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03797_not_prime : ¬(recordGapCenter - 448).Prime := by
  rw [fullRecordGapTerm03797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03797_fast_pow_mod_ne_one

def fullRecordGapValue03798 : Nat := fullRecordGapCenterValue - 420

theorem fullRecordGapTerm03798_eq_value :
    recordGapCenter - 420 = fullRecordGapValue03798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03798 (fullRecordGapValue03798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03798_not_prime : ¬(recordGapCenter - 420).Prime := by
  rw [fullRecordGapTerm03798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03798_fast_pow_mod_ne_one

def fullRecordGapValue03799 : Nat := fullRecordGapCenterValue - 384

theorem fullRecordGapTerm03799_eq_value :
    recordGapCenter - 384 = fullRecordGapValue03799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03799 (fullRecordGapValue03799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03799_not_prime : ¬(recordGapCenter - 384).Prime := by
  rw [fullRecordGapTerm03799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03799_fast_pow_mod_ne_one

def fullRecordGapValue03800 : Nat := fullRecordGapCenterValue - 352

theorem fullRecordGapTerm03800_eq_value :
    recordGapCenter - 352 = fullRecordGapValue03800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03800 (fullRecordGapValue03800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03800_not_prime : ¬(recordGapCenter - 352).Prime := by
  rw [fullRecordGapTerm03800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03800_fast_pow_mod_ne_one

def fullRecordGapValue03801 : Nat := fullRecordGapCenterValue - 270

theorem fullRecordGapTerm03801_eq_value :
    recordGapCenter - 270 = fullRecordGapValue03801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03801 (fullRecordGapValue03801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03801_not_prime : ¬(recordGapCenter - 270).Prime := by
  rw [fullRecordGapTerm03801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03801_fast_pow_mod_ne_one

def fullRecordGapValue03802 : Nat := fullRecordGapCenterValue - 252

theorem fullRecordGapTerm03802_eq_value :
    recordGapCenter - 252 = fullRecordGapValue03802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03802 (fullRecordGapValue03802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03802_not_prime : ¬(recordGapCenter - 252).Prime := by
  rw [fullRecordGapTerm03802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03802_fast_pow_mod_ne_one

def fullRecordGapValue03803 : Nat := fullRecordGapCenterValue - 250

theorem fullRecordGapTerm03803_eq_value :
    recordGapCenter - 250 = fullRecordGapValue03803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03803 (fullRecordGapValue03803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03803_not_prime : ¬(recordGapCenter - 250).Prime := by
  rw [fullRecordGapTerm03803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03803_fast_pow_mod_ne_one

def fullRecordGapValue03804 : Nat := fullRecordGapCenterValue - 240

theorem fullRecordGapTerm03804_eq_value :
    recordGapCenter - 240 = fullRecordGapValue03804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03804 (fullRecordGapValue03804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03804_not_prime : ¬(recordGapCenter - 240).Prime := by
  rw [fullRecordGapTerm03804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03804_fast_pow_mod_ne_one

def fullRecordGapValue03805 : Nat := fullRecordGapCenterValue - 198

theorem fullRecordGapTerm03805_eq_value :
    recordGapCenter - 198 = fullRecordGapValue03805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03805 (fullRecordGapValue03805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03805_not_prime : ¬(recordGapCenter - 198).Prime := by
  rw [fullRecordGapTerm03805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03805_fast_pow_mod_ne_one

def fullRecordGapValue03806 : Nat := fullRecordGapCenterValue - 192

theorem fullRecordGapTerm03806_eq_value :
    recordGapCenter - 192 = fullRecordGapValue03806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03806 (fullRecordGapValue03806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03806_not_prime : ¬(recordGapCenter - 192).Prime := by
  rw [fullRecordGapTerm03806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03806_fast_pow_mod_ne_one

def fullRecordGapValue03807 : Nat := fullRecordGapCenterValue - 108

theorem fullRecordGapTerm03807_eq_value :
    recordGapCenter - 108 = fullRecordGapValue03807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03807 (fullRecordGapValue03807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03807_not_prime : ¬(recordGapCenter - 108).Prime := by
  rw [fullRecordGapTerm03807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03807_fast_pow_mod_ne_one

def fullRecordGapValue03808 : Nat := fullRecordGapCenterValue - 100

theorem fullRecordGapTerm03808_eq_value :
    recordGapCenter - 100 = fullRecordGapValue03808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03808 (fullRecordGapValue03808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03808_not_prime : ¬(recordGapCenter - 100).Prime := by
  rw [fullRecordGapTerm03808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03808_fast_pow_mod_ne_one

def fullRecordGapValue03809 : Nat := fullRecordGapCenterValue - 90

theorem fullRecordGapTerm03809_eq_value :
    recordGapCenter - 90 = fullRecordGapValue03809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03809 (fullRecordGapValue03809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03809_not_prime : ¬(recordGapCenter - 90).Prime := by
  rw [fullRecordGapTerm03809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03809_fast_pow_mod_ne_one

def fullRecordGapValue03810 : Nat := fullRecordGapCenterValue - 88

theorem fullRecordGapTerm03810_eq_value :
    recordGapCenter - 88 = fullRecordGapValue03810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03810 (fullRecordGapValue03810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03810_not_prime : ¬(recordGapCenter - 88).Prime := by
  rw [fullRecordGapTerm03810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03810_fast_pow_mod_ne_one

def fullRecordGapValue03811 : Nat := fullRecordGapCenterValue - 84

theorem fullRecordGapTerm03811_eq_value :
    recordGapCenter - 84 = fullRecordGapValue03811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03811 (fullRecordGapValue03811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03811_not_prime : ¬(recordGapCenter - 84).Prime := by
  rw [fullRecordGapTerm03811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03811_fast_pow_mod_ne_one

def fullRecordGapValue03812 : Nat := fullRecordGapCenterValue - 60

theorem fullRecordGapTerm03812_eq_value :
    recordGapCenter - 60 = fullRecordGapValue03812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03812 (fullRecordGapValue03812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03812_not_prime : ¬(recordGapCenter - 60).Prime := by
  rw [fullRecordGapTerm03812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03812_fast_pow_mod_ne_one

def fullRecordGapValue03813 : Nat := fullRecordGapCenterValue - 54

theorem fullRecordGapTerm03813_eq_value :
    recordGapCenter - 54 = fullRecordGapValue03813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03813 (fullRecordGapValue03813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03813_not_prime : ¬(recordGapCenter - 54).Prime := by
  rw [fullRecordGapTerm03813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03813_fast_pow_mod_ne_one

def fullRecordGapValue03814 : Nat := fullRecordGapCenterValue - 24

theorem fullRecordGapTerm03814_eq_value :
    recordGapCenter - 24 = fullRecordGapValue03814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03814 (fullRecordGapValue03814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03814_not_prime : ¬(recordGapCenter - 24).Prime := by
  rw [fullRecordGapTerm03814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03814_fast_pow_mod_ne_one

def fullRecordGapValue03815 : Nat := fullRecordGapCenterValue - 12

theorem fullRecordGapTerm03815_eq_value :
    recordGapCenter - 12 = fullRecordGapValue03815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03815 (fullRecordGapValue03815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03815_not_prime : ¬(recordGapCenter - 12).Prime := by
  rw [fullRecordGapTerm03815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03815_fast_pow_mod_ne_one

def fullRecordGapValue03816 : Nat := fullRecordGapCenterValue + 66

theorem fullRecordGapTerm03816_eq_value :
    recordGapCenter + 66 = fullRecordGapValue03816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03816 (fullRecordGapValue03816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03816_not_prime : ¬(recordGapCenter + 66).Prime := by
  rw [fullRecordGapTerm03816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03816_fast_pow_mod_ne_one

def fullRecordGapValue03817 : Nat := fullRecordGapCenterValue + 72

theorem fullRecordGapTerm03817_eq_value :
    recordGapCenter + 72 = fullRecordGapValue03817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03817 (fullRecordGapValue03817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03817_not_prime : ¬(recordGapCenter + 72).Prime := by
  rw [fullRecordGapTerm03817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03817_fast_pow_mod_ne_one

def fullRecordGapValue03818 : Nat := fullRecordGapCenterValue + 96

theorem fullRecordGapTerm03818_eq_value :
    recordGapCenter + 96 = fullRecordGapValue03818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03818 (fullRecordGapValue03818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03818_not_prime : ¬(recordGapCenter + 96).Prime := by
  rw [fullRecordGapTerm03818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03818_fast_pow_mod_ne_one

def fullRecordGapValue03819 : Nat := fullRecordGapCenterValue + 110

theorem fullRecordGapTerm03819_eq_value :
    recordGapCenter + 110 = fullRecordGapValue03819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03819 (fullRecordGapValue03819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03819_not_prime : ¬(recordGapCenter + 110).Prime := by
  rw [fullRecordGapTerm03819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03819_fast_pow_mod_ne_one

def fullRecordGapValue03820 : Nat := fullRecordGapCenterValue + 126

theorem fullRecordGapTerm03820_eq_value :
    recordGapCenter + 126 = fullRecordGapValue03820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03820 (fullRecordGapValue03820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03820_not_prime : ¬(recordGapCenter + 126).Prime := by
  rw [fullRecordGapTerm03820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03820_fast_pow_mod_ne_one

def fullRecordGapValue03821 : Nat := fullRecordGapCenterValue + 140

theorem fullRecordGapTerm03821_eq_value :
    recordGapCenter + 140 = fullRecordGapValue03821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03821 (fullRecordGapValue03821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03821_not_prime : ¬(recordGapCenter + 140).Prime := by
  rw [fullRecordGapTerm03821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03821_fast_pow_mod_ne_one

def fullRecordGapValue03822 : Nat := fullRecordGapCenterValue + 162

theorem fullRecordGapTerm03822_eq_value :
    recordGapCenter + 162 = fullRecordGapValue03822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03822 (fullRecordGapValue03822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03822_not_prime : ¬(recordGapCenter + 162).Prime := by
  rw [fullRecordGapTerm03822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03822_fast_pow_mod_ne_one

def fullRecordGapValue03823 : Nat := fullRecordGapCenterValue + 176

theorem fullRecordGapTerm03823_eq_value :
    recordGapCenter + 176 = fullRecordGapValue03823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03823 (fullRecordGapValue03823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03823_not_prime : ¬(recordGapCenter + 176).Prime := by
  rw [fullRecordGapTerm03823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03823_fast_pow_mod_ne_one

def fullRecordGapValue03824 : Nat := fullRecordGapCenterValue + 192

theorem fullRecordGapTerm03824_eq_value :
    recordGapCenter + 192 = fullRecordGapValue03824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03824 (fullRecordGapValue03824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03824_not_prime : ¬(recordGapCenter + 192).Prime := by
  rw [fullRecordGapTerm03824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03824_fast_pow_mod_ne_one

def fullRecordGapValue03825 : Nat := fullRecordGapCenterValue + 240

theorem fullRecordGapTerm03825_eq_value :
    recordGapCenter + 240 = fullRecordGapValue03825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03825 (fullRecordGapValue03825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03825_not_prime : ¬(recordGapCenter + 240).Prime := by
  rw [fullRecordGapTerm03825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03825_fast_pow_mod_ne_one

def fullRecordGapValue03826 : Nat := fullRecordGapCenterValue + 252

theorem fullRecordGapTerm03826_eq_value :
    recordGapCenter + 252 = fullRecordGapValue03826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03826 (fullRecordGapValue03826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03826_not_prime : ¬(recordGapCenter + 252).Prime := by
  rw [fullRecordGapTerm03826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03826_fast_pow_mod_ne_one

def fullRecordGapValue03827 : Nat := fullRecordGapCenterValue + 336

theorem fullRecordGapTerm03827_eq_value :
    recordGapCenter + 336 = fullRecordGapValue03827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03827 (fullRecordGapValue03827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03827_not_prime : ¬(recordGapCenter + 336).Prime := by
  rw [fullRecordGapTerm03827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03827_fast_pow_mod_ne_one

def fullRecordGapValue03828 : Nat := fullRecordGapCenterValue + 350

theorem fullRecordGapTerm03828_eq_value :
    recordGapCenter + 350 = fullRecordGapValue03828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03828 (fullRecordGapValue03828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03828_not_prime : ¬(recordGapCenter + 350).Prime := by
  rw [fullRecordGapTerm03828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03828_fast_pow_mod_ne_one

def fullRecordGapValue03829 : Nat := fullRecordGapCenterValue + 360

theorem fullRecordGapTerm03829_eq_value :
    recordGapCenter + 360 = fullRecordGapValue03829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03829 (fullRecordGapValue03829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03829_not_prime : ¬(recordGapCenter + 360).Prime := by
  rw [fullRecordGapTerm03829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03829_fast_pow_mod_ne_one

def fullRecordGapValue03830 : Nat := fullRecordGapCenterValue + 420

theorem fullRecordGapTerm03830_eq_value :
    recordGapCenter + 420 = fullRecordGapValue03830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03830 (fullRecordGapValue03830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03830_not_prime : ¬(recordGapCenter + 420).Prime := by
  rw [fullRecordGapTerm03830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03830_fast_pow_mod_ne_one

def fullRecordGapValue03831 : Nat := fullRecordGapCenterValue + 486

theorem fullRecordGapTerm03831_eq_value :
    recordGapCenter + 486 = fullRecordGapValue03831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03831 (fullRecordGapValue03831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03831_not_prime : ¬(recordGapCenter + 486).Prime := by
  rw [fullRecordGapTerm03831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03831_fast_pow_mod_ne_one

def fullRecordGapValue03832 : Nat := fullRecordGapCenterValue + 512

theorem fullRecordGapTerm03832_eq_value :
    recordGapCenter + 512 = fullRecordGapValue03832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03832 (fullRecordGapValue03832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03832_not_prime : ¬(recordGapCenter + 512).Prime := by
  rw [fullRecordGapTerm03832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03832_fast_pow_mod_ne_one

def fullRecordGapValue03833 : Nat := fullRecordGapCenterValue + 528

theorem fullRecordGapTerm03833_eq_value :
    recordGapCenter + 528 = fullRecordGapValue03833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03833 (fullRecordGapValue03833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03833_not_prime : ¬(recordGapCenter + 528).Prime := by
  rw [fullRecordGapTerm03833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03833_fast_pow_mod_ne_one

def fullRecordGapValue03834 : Nat := fullRecordGapCenterValue + 560

theorem fullRecordGapTerm03834_eq_value :
    recordGapCenter + 560 = fullRecordGapValue03834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03834 (fullRecordGapValue03834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03834_not_prime : ¬(recordGapCenter + 560).Prime := by
  rw [fullRecordGapTerm03834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03834_fast_pow_mod_ne_one

def fullRecordGapValue03835 : Nat := fullRecordGapCenterValue + 576

theorem fullRecordGapTerm03835_eq_value :
    recordGapCenter + 576 = fullRecordGapValue03835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03835 (fullRecordGapValue03835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03835_not_prime : ¬(recordGapCenter + 576).Prime := by
  rw [fullRecordGapTerm03835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03835_fast_pow_mod_ne_one

def fullRecordGapValue03836 : Nat := fullRecordGapCenterValue + 588

theorem fullRecordGapTerm03836_eq_value :
    recordGapCenter + 588 = fullRecordGapValue03836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03836 (fullRecordGapValue03836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03836_not_prime : ¬(recordGapCenter + 588).Prime := by
  rw [fullRecordGapTerm03836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03836_fast_pow_mod_ne_one

def fullRecordGapValue03837 : Nat := fullRecordGapCenterValue + 600

theorem fullRecordGapTerm03837_eq_value :
    recordGapCenter + 600 = fullRecordGapValue03837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03837 (fullRecordGapValue03837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03837_not_prime : ¬(recordGapCenter + 600).Prime := by
  rw [fullRecordGapTerm03837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03837_fast_pow_mod_ne_one

def fullRecordGapValue03838 : Nat := fullRecordGapCenterValue + 660

theorem fullRecordGapTerm03838_eq_value :
    recordGapCenter + 660 = fullRecordGapValue03838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03838 (fullRecordGapValue03838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03838_not_prime : ¬(recordGapCenter + 660).Prime := by
  rw [fullRecordGapTerm03838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03838_fast_pow_mod_ne_one

def fullRecordGapValue03839 : Nat := fullRecordGapCenterValue + 726

theorem fullRecordGapTerm03839_eq_value :
    recordGapCenter + 726 = fullRecordGapValue03839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03839 (fullRecordGapValue03839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03839_not_prime : ¬(recordGapCenter + 726).Prime := by
  rw [fullRecordGapTerm03839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03839_fast_pow_mod_ne_one

def fullRecordGapValue03840 : Nat := fullRecordGapCenterValue + 882

theorem fullRecordGapTerm03840_eq_value :
    recordGapCenter + 882 = fullRecordGapValue03840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03840 (fullRecordGapValue03840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03840_not_prime : ¬(recordGapCenter + 882).Prime := by
  rw [fullRecordGapTerm03840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03840_fast_pow_mod_ne_one

end PrimeFactorUnimodality
