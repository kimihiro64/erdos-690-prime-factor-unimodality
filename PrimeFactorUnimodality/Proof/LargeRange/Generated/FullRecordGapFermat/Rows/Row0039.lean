import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue09729 : Nat := fullRecordGapCenterValue + 584538

theorem fullRecordGapTerm09729_eq_value :
    recordGapCenter + 584538 = fullRecordGapValue09729 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09729_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09729 (fullRecordGapValue09729 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09729_not_prime : ¬(recordGapCenter + 584538).Prime := by
  rw [fullRecordGapTerm09729_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09729, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09729_fast_pow_mod_ne_one

def fullRecordGapValue09730 : Nat := fullRecordGapCenterValue + 584718

theorem fullRecordGapTerm09730_eq_value :
    recordGapCenter + 584718 = fullRecordGapValue09730 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09730_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09730 (fullRecordGapValue09730 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09730_not_prime : ¬(recordGapCenter + 584718).Prime := by
  rw [fullRecordGapTerm09730_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09730, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09730_fast_pow_mod_ne_one

def fullRecordGapValue09731 : Nat := fullRecordGapCenterValue + 584726

theorem fullRecordGapTerm09731_eq_value :
    recordGapCenter + 584726 = fullRecordGapValue09731 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09731_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09731 (fullRecordGapValue09731 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09731_not_prime : ¬(recordGapCenter + 584726).Prime := by
  rw [fullRecordGapTerm09731_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09731, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09731_fast_pow_mod_ne_one

def fullRecordGapValue09732 : Nat := fullRecordGapCenterValue + 584762

theorem fullRecordGapTerm09732_eq_value :
    recordGapCenter + 584762 = fullRecordGapValue09732 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09732_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09732 (fullRecordGapValue09732 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09732_not_prime : ¬(recordGapCenter + 584762).Prime := by
  rw [fullRecordGapTerm09732_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09732, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09732_fast_pow_mod_ne_one

def fullRecordGapValue09733 : Nat := fullRecordGapCenterValue + 584810

theorem fullRecordGapTerm09733_eq_value :
    recordGapCenter + 584810 = fullRecordGapValue09733 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09733_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09733 (fullRecordGapValue09733 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09733_not_prime : ¬(recordGapCenter + 584810).Prime := by
  rw [fullRecordGapTerm09733_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09733, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09733_fast_pow_mod_ne_one

def fullRecordGapValue09734 : Nat := fullRecordGapCenterValue + 584882

theorem fullRecordGapTerm09734_eq_value :
    recordGapCenter + 584882 = fullRecordGapValue09734 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09734_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09734 (fullRecordGapValue09734 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09734_not_prime : ¬(recordGapCenter + 584882).Prime := by
  rw [fullRecordGapTerm09734_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09734, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09734_fast_pow_mod_ne_one

def fullRecordGapValue09735 : Nat := fullRecordGapCenterValue + 584978

theorem fullRecordGapTerm09735_eq_value :
    recordGapCenter + 584978 = fullRecordGapValue09735 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09735_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09735 (fullRecordGapValue09735 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09735_not_prime : ¬(recordGapCenter + 584978).Prime := by
  rw [fullRecordGapTerm09735_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09735, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09735_fast_pow_mod_ne_one

def fullRecordGapValue09736 : Nat := fullRecordGapCenterValue + 585006

theorem fullRecordGapTerm09736_eq_value :
    recordGapCenter + 585006 = fullRecordGapValue09736 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09736_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09736 (fullRecordGapValue09736 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09736_not_prime : ¬(recordGapCenter + 585006).Prime := by
  rw [fullRecordGapTerm09736_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09736, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09736_fast_pow_mod_ne_one

def fullRecordGapValue09737 : Nat := fullRecordGapCenterValue + 585012

theorem fullRecordGapTerm09737_eq_value :
    recordGapCenter + 585012 = fullRecordGapValue09737 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09737_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09737 (fullRecordGapValue09737 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09737_not_prime : ¬(recordGapCenter + 585012).Prime := by
  rw [fullRecordGapTerm09737_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09737, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09737_fast_pow_mod_ne_one

def fullRecordGapValue09738 : Nat := fullRecordGapCenterValue + 585062

theorem fullRecordGapTerm09738_eq_value :
    recordGapCenter + 585062 = fullRecordGapValue09738 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09738_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09738 (fullRecordGapValue09738 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09738_not_prime : ¬(recordGapCenter + 585062).Prime := by
  rw [fullRecordGapTerm09738_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09738, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09738_fast_pow_mod_ne_one

def fullRecordGapValue09739 : Nat := fullRecordGapCenterValue + 585098

theorem fullRecordGapTerm09739_eq_value :
    recordGapCenter + 585098 = fullRecordGapValue09739 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09739_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09739 (fullRecordGapValue09739 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09739_not_prime : ¬(recordGapCenter + 585098).Prime := by
  rw [fullRecordGapTerm09739_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09739, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09739_fast_pow_mod_ne_one

def fullRecordGapValue09740 : Nat := fullRecordGapCenterValue + 585138

theorem fullRecordGapTerm09740_eq_value :
    recordGapCenter + 585138 = fullRecordGapValue09740 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09740_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09740 (fullRecordGapValue09740 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09740_not_prime : ¬(recordGapCenter + 585138).Prime := by
  rw [fullRecordGapTerm09740_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09740, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09740_fast_pow_mod_ne_one

def fullRecordGapValue09741 : Nat := fullRecordGapCenterValue + 585146

theorem fullRecordGapTerm09741_eq_value :
    recordGapCenter + 585146 = fullRecordGapValue09741 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09741_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09741 (fullRecordGapValue09741 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09741_not_prime : ¬(recordGapCenter + 585146).Prime := by
  rw [fullRecordGapTerm09741_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09741, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09741_fast_pow_mod_ne_one

def fullRecordGapValue09742 : Nat := fullRecordGapCenterValue + 585188

theorem fullRecordGapTerm09742_eq_value :
    recordGapCenter + 585188 = fullRecordGapValue09742 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09742_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09742 (fullRecordGapValue09742 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09742_not_prime : ¬(recordGapCenter + 585188).Prime := by
  rw [fullRecordGapTerm09742_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09742, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09742_fast_pow_mod_ne_one

def fullRecordGapValue09743 : Nat := fullRecordGapCenterValue + 585348

theorem fullRecordGapTerm09743_eq_value :
    recordGapCenter + 585348 = fullRecordGapValue09743 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09743_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09743 (fullRecordGapValue09743 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09743_not_prime : ¬(recordGapCenter + 585348).Prime := by
  rw [fullRecordGapTerm09743_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09743, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09743_fast_pow_mod_ne_one

def fullRecordGapValue09744 : Nat := fullRecordGapCenterValue + 585426

theorem fullRecordGapTerm09744_eq_value :
    recordGapCenter + 585426 = fullRecordGapValue09744 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09744_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09744 (fullRecordGapValue09744 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09744_not_prime : ¬(recordGapCenter + 585426).Prime := by
  rw [fullRecordGapTerm09744_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09744, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09744_fast_pow_mod_ne_one

def fullRecordGapValue09745 : Nat := fullRecordGapCenterValue + 585498

theorem fullRecordGapTerm09745_eq_value :
    recordGapCenter + 585498 = fullRecordGapValue09745 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09745_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09745 (fullRecordGapValue09745 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09745_not_prime : ¬(recordGapCenter + 585498).Prime := by
  rw [fullRecordGapTerm09745_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09745, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09745_fast_pow_mod_ne_one

def fullRecordGapValue09746 : Nat := fullRecordGapCenterValue + 585506

theorem fullRecordGapTerm09746_eq_value :
    recordGapCenter + 585506 = fullRecordGapValue09746 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09746_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09746 (fullRecordGapValue09746 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09746_not_prime : ¬(recordGapCenter + 585506).Prime := by
  rw [fullRecordGapTerm09746_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09746, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09746_fast_pow_mod_ne_one

def fullRecordGapValue09747 : Nat := fullRecordGapCenterValue + 585512

theorem fullRecordGapTerm09747_eq_value :
    recordGapCenter + 585512 = fullRecordGapValue09747 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09747_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09747 (fullRecordGapValue09747 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09747_not_prime : ¬(recordGapCenter + 585512).Prime := by
  rw [fullRecordGapTerm09747_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09747, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09747_fast_pow_mod_ne_one

def fullRecordGapValue09748 : Nat := fullRecordGapCenterValue + 585588

theorem fullRecordGapTerm09748_eq_value :
    recordGapCenter + 585588 = fullRecordGapValue09748 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09748_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09748 (fullRecordGapValue09748 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09748_not_prime : ¬(recordGapCenter + 585588).Prime := by
  rw [fullRecordGapTerm09748_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09748, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09748_fast_pow_mod_ne_one

def fullRecordGapValue09749 : Nat := fullRecordGapCenterValue + 585642

theorem fullRecordGapTerm09749_eq_value :
    recordGapCenter + 585642 = fullRecordGapValue09749 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09749_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09749 (fullRecordGapValue09749 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09749_not_prime : ¬(recordGapCenter + 585642).Prime := by
  rw [fullRecordGapTerm09749_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09749, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09749_fast_pow_mod_ne_one

def fullRecordGapValue09750 : Nat := fullRecordGapCenterValue + 585692

theorem fullRecordGapTerm09750_eq_value :
    recordGapCenter + 585692 = fullRecordGapValue09750 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09750_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09750 (fullRecordGapValue09750 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09750_not_prime : ¬(recordGapCenter + 585692).Prime := by
  rw [fullRecordGapTerm09750_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09750, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09750_fast_pow_mod_ne_one

def fullRecordGapValue09751 : Nat := fullRecordGapCenterValue + 585758

theorem fullRecordGapTerm09751_eq_value :
    recordGapCenter + 585758 = fullRecordGapValue09751 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09751_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09751 (fullRecordGapValue09751 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09751_not_prime : ¬(recordGapCenter + 585758).Prime := by
  rw [fullRecordGapTerm09751_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09751, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09751_fast_pow_mod_ne_one

def fullRecordGapValue09752 : Nat := fullRecordGapCenterValue + 585818

theorem fullRecordGapTerm09752_eq_value :
    recordGapCenter + 585818 = fullRecordGapValue09752 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09752_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09752 (fullRecordGapValue09752 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09752_not_prime : ¬(recordGapCenter + 585818).Prime := by
  rw [fullRecordGapTerm09752_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09752, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09752_fast_pow_mod_ne_one

def fullRecordGapValue09753 : Nat := fullRecordGapCenterValue + 585866

theorem fullRecordGapTerm09753_eq_value :
    recordGapCenter + 585866 = fullRecordGapValue09753 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09753_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09753 (fullRecordGapValue09753 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09753_not_prime : ¬(recordGapCenter + 585866).Prime := by
  rw [fullRecordGapTerm09753_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09753, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09753_fast_pow_mod_ne_one

def fullRecordGapValue09754 : Nat := fullRecordGapCenterValue + 585876

theorem fullRecordGapTerm09754_eq_value :
    recordGapCenter + 585876 = fullRecordGapValue09754 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09754_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09754 (fullRecordGapValue09754 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09754_not_prime : ¬(recordGapCenter + 585876).Prime := by
  rw [fullRecordGapTerm09754_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09754, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09754_fast_pow_mod_ne_one

def fullRecordGapValue09755 : Nat := fullRecordGapCenterValue + 585896

theorem fullRecordGapTerm09755_eq_value :
    recordGapCenter + 585896 = fullRecordGapValue09755 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09755_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09755 (fullRecordGapValue09755 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09755_not_prime : ¬(recordGapCenter + 585896).Prime := by
  rw [fullRecordGapTerm09755_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09755, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09755_fast_pow_mod_ne_one

def fullRecordGapValue09756 : Nat := fullRecordGapCenterValue + 585938

theorem fullRecordGapTerm09756_eq_value :
    recordGapCenter + 585938 = fullRecordGapValue09756 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09756_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09756 (fullRecordGapValue09756 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09756_not_prime : ¬(recordGapCenter + 585938).Prime := by
  rw [fullRecordGapTerm09756_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09756, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09756_fast_pow_mod_ne_one

def fullRecordGapValue09757 : Nat := fullRecordGapCenterValue + 585986

theorem fullRecordGapTerm09757_eq_value :
    recordGapCenter + 585986 = fullRecordGapValue09757 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09757_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09757 (fullRecordGapValue09757 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09757_not_prime : ¬(recordGapCenter + 585986).Prime := by
  rw [fullRecordGapTerm09757_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09757, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09757_fast_pow_mod_ne_one

def fullRecordGapValue09758 : Nat := fullRecordGapCenterValue + 586052

theorem fullRecordGapTerm09758_eq_value :
    recordGapCenter + 586052 = fullRecordGapValue09758 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09758_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09758 (fullRecordGapValue09758 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09758_not_prime : ¬(recordGapCenter + 586052).Prime := by
  rw [fullRecordGapTerm09758_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09758, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09758_fast_pow_mod_ne_one

def fullRecordGapValue09759 : Nat := fullRecordGapCenterValue + 586122

theorem fullRecordGapTerm09759_eq_value :
    recordGapCenter + 586122 = fullRecordGapValue09759 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09759_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09759 (fullRecordGapValue09759 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09759_not_prime : ¬(recordGapCenter + 586122).Prime := by
  rw [fullRecordGapTerm09759_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09759, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09759_fast_pow_mod_ne_one

def fullRecordGapValue09760 : Nat := fullRecordGapCenterValue + 586266

theorem fullRecordGapTerm09760_eq_value :
    recordGapCenter + 586266 = fullRecordGapValue09760 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09760_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09760 (fullRecordGapValue09760 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09760_not_prime : ¬(recordGapCenter + 586266).Prime := by
  rw [fullRecordGapTerm09760_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09760, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09760_fast_pow_mod_ne_one

def fullRecordGapValue09761 : Nat := fullRecordGapCenterValue + 586310

theorem fullRecordGapTerm09761_eq_value :
    recordGapCenter + 586310 = fullRecordGapValue09761 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09761_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09761 (fullRecordGapValue09761 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09761_not_prime : ¬(recordGapCenter + 586310).Prime := by
  rw [fullRecordGapTerm09761_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09761, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09761_fast_pow_mod_ne_one

def fullRecordGapValue09762 : Nat := fullRecordGapCenterValue + 586328

theorem fullRecordGapTerm09762_eq_value :
    recordGapCenter + 586328 = fullRecordGapValue09762 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09762_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09762 (fullRecordGapValue09762 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09762_not_prime : ¬(recordGapCenter + 586328).Prime := by
  rw [fullRecordGapTerm09762_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09762, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09762_fast_pow_mod_ne_one

def fullRecordGapValue09763 : Nat := fullRecordGapCenterValue + 586412

theorem fullRecordGapTerm09763_eq_value :
    recordGapCenter + 586412 = fullRecordGapValue09763 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09763_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09763 (fullRecordGapValue09763 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09763_not_prime : ¬(recordGapCenter + 586412).Prime := by
  rw [fullRecordGapTerm09763_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09763, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09763_fast_pow_mod_ne_one

def fullRecordGapValue09764 : Nat := fullRecordGapCenterValue + 586436

theorem fullRecordGapTerm09764_eq_value :
    recordGapCenter + 586436 = fullRecordGapValue09764 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09764_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09764 (fullRecordGapValue09764 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09764_not_prime : ¬(recordGapCenter + 586436).Prime := by
  rw [fullRecordGapTerm09764_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09764, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09764_fast_pow_mod_ne_one

def fullRecordGapValue09765 : Nat := fullRecordGapCenterValue + 586442

theorem fullRecordGapTerm09765_eq_value :
    recordGapCenter + 586442 = fullRecordGapValue09765 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09765_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09765 (fullRecordGapValue09765 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09765_not_prime : ¬(recordGapCenter + 586442).Prime := by
  rw [fullRecordGapTerm09765_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09765, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09765_fast_pow_mod_ne_one

def fullRecordGapValue09766 : Nat := fullRecordGapCenterValue + 586526

theorem fullRecordGapTerm09766_eq_value :
    recordGapCenter + 586526 = fullRecordGapValue09766 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09766_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09766 (fullRecordGapValue09766 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09766_not_prime : ¬(recordGapCenter + 586526).Prime := by
  rw [fullRecordGapTerm09766_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09766, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09766_fast_pow_mod_ne_one

def fullRecordGapValue09767 : Nat := fullRecordGapCenterValue + 586596

theorem fullRecordGapTerm09767_eq_value :
    recordGapCenter + 586596 = fullRecordGapValue09767 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09767_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09767 (fullRecordGapValue09767 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09767_not_prime : ¬(recordGapCenter + 586596).Prime := by
  rw [fullRecordGapTerm09767_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09767, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09767_fast_pow_mod_ne_one

def fullRecordGapValue09768 : Nat := fullRecordGapCenterValue + 586616

theorem fullRecordGapTerm09768_eq_value :
    recordGapCenter + 586616 = fullRecordGapValue09768 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09768_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09768 (fullRecordGapValue09768 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09768_not_prime : ¬(recordGapCenter + 586616).Prime := by
  rw [fullRecordGapTerm09768_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09768, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09768_fast_pow_mod_ne_one

def fullRecordGapValue09769 : Nat := fullRecordGapCenterValue + 586622

theorem fullRecordGapTerm09769_eq_value :
    recordGapCenter + 586622 = fullRecordGapValue09769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09769 (fullRecordGapValue09769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09769_not_prime : ¬(recordGapCenter + 586622).Prime := by
  rw [fullRecordGapTerm09769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09769_fast_pow_mod_ne_one

def fullRecordGapValue09770 : Nat := fullRecordGapCenterValue + 586668

theorem fullRecordGapTerm09770_eq_value :
    recordGapCenter + 586668 = fullRecordGapValue09770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09770 (fullRecordGapValue09770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09770_not_prime : ¬(recordGapCenter + 586668).Prime := by
  rw [fullRecordGapTerm09770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09770_fast_pow_mod_ne_one

def fullRecordGapValue09771 : Nat := fullRecordGapCenterValue + 586722

theorem fullRecordGapTerm09771_eq_value :
    recordGapCenter + 586722 = fullRecordGapValue09771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09771 (fullRecordGapValue09771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09771_not_prime : ¬(recordGapCenter + 586722).Prime := by
  rw [fullRecordGapTerm09771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09771_fast_pow_mod_ne_one

def fullRecordGapValue09772 : Nat := fullRecordGapCenterValue + 586826

theorem fullRecordGapTerm09772_eq_value :
    recordGapCenter + 586826 = fullRecordGapValue09772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09772 (fullRecordGapValue09772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09772_not_prime : ¬(recordGapCenter + 586826).Prime := by
  rw [fullRecordGapTerm09772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09772_fast_pow_mod_ne_one

def fullRecordGapValue09773 : Nat := fullRecordGapCenterValue + 586862

theorem fullRecordGapTerm09773_eq_value :
    recordGapCenter + 586862 = fullRecordGapValue09773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09773 (fullRecordGapValue09773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09773_not_prime : ¬(recordGapCenter + 586862).Prime := by
  rw [fullRecordGapTerm09773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09773_fast_pow_mod_ne_one

def fullRecordGapValue09774 : Nat := fullRecordGapCenterValue + 587058

theorem fullRecordGapTerm09774_eq_value :
    recordGapCenter + 587058 = fullRecordGapValue09774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09774 (fullRecordGapValue09774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09774_not_prime : ¬(recordGapCenter + 587058).Prime := by
  rw [fullRecordGapTerm09774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09774_fast_pow_mod_ne_one

def fullRecordGapValue09775 : Nat := fullRecordGapCenterValue + 587228

theorem fullRecordGapTerm09775_eq_value :
    recordGapCenter + 587228 = fullRecordGapValue09775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09775 (fullRecordGapValue09775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09775_not_prime : ¬(recordGapCenter + 587228).Prime := by
  rw [fullRecordGapTerm09775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09775_fast_pow_mod_ne_one

def fullRecordGapValue09776 : Nat := fullRecordGapCenterValue + 587402

theorem fullRecordGapTerm09776_eq_value :
    recordGapCenter + 587402 = fullRecordGapValue09776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09776 (fullRecordGapValue09776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09776_not_prime : ¬(recordGapCenter + 587402).Prime := by
  rw [fullRecordGapTerm09776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09776_fast_pow_mod_ne_one

def fullRecordGapValue09777 : Nat := fullRecordGapCenterValue + 587436

theorem fullRecordGapTerm09777_eq_value :
    recordGapCenter + 587436 = fullRecordGapValue09777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09777 (fullRecordGapValue09777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09777_not_prime : ¬(recordGapCenter + 587436).Prime := by
  rw [fullRecordGapTerm09777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09777_fast_pow_mod_ne_one

def fullRecordGapValue09778 : Nat := fullRecordGapCenterValue + 587546

theorem fullRecordGapTerm09778_eq_value :
    recordGapCenter + 587546 = fullRecordGapValue09778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09778 (fullRecordGapValue09778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09778_not_prime : ¬(recordGapCenter + 587546).Prime := by
  rw [fullRecordGapTerm09778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09778_fast_pow_mod_ne_one

def fullRecordGapValue09779 : Nat := fullRecordGapCenterValue + 587658

theorem fullRecordGapTerm09779_eq_value :
    recordGapCenter + 587658 = fullRecordGapValue09779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09779 (fullRecordGapValue09779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09779_not_prime : ¬(recordGapCenter + 587658).Prime := by
  rw [fullRecordGapTerm09779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09779_fast_pow_mod_ne_one

def fullRecordGapValue09780 : Nat := fullRecordGapCenterValue + 587816

theorem fullRecordGapTerm09780_eq_value :
    recordGapCenter + 587816 = fullRecordGapValue09780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09780 (fullRecordGapValue09780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09780_not_prime : ¬(recordGapCenter + 587816).Prime := by
  rw [fullRecordGapTerm09780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09780_fast_pow_mod_ne_one

def fullRecordGapValue09781 : Nat := fullRecordGapCenterValue + 587966

theorem fullRecordGapTerm09781_eq_value :
    recordGapCenter + 587966 = fullRecordGapValue09781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09781 (fullRecordGapValue09781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09781_not_prime : ¬(recordGapCenter + 587966).Prime := by
  rw [fullRecordGapTerm09781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09781_fast_pow_mod_ne_one

def fullRecordGapValue09782 : Nat := fullRecordGapCenterValue + 588000

theorem fullRecordGapTerm09782_eq_value :
    recordGapCenter + 588000 = fullRecordGapValue09782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09782 (fullRecordGapValue09782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09782_not_prime : ¬(recordGapCenter + 588000).Prime := by
  rw [fullRecordGapTerm09782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09782_fast_pow_mod_ne_one

def fullRecordGapValue09783 : Nat := fullRecordGapCenterValue + 588036

theorem fullRecordGapTerm09783_eq_value :
    recordGapCenter + 588036 = fullRecordGapValue09783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09783 (fullRecordGapValue09783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09783_not_prime : ¬(recordGapCenter + 588036).Prime := by
  rw [fullRecordGapTerm09783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09783_fast_pow_mod_ne_one

def fullRecordGapValue09784 : Nat := fullRecordGapCenterValue + 588066

theorem fullRecordGapTerm09784_eq_value :
    recordGapCenter + 588066 = fullRecordGapValue09784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09784 (fullRecordGapValue09784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09784_not_prime : ¬(recordGapCenter + 588066).Prime := by
  rw [fullRecordGapTerm09784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09784_fast_pow_mod_ne_one

def fullRecordGapValue09785 : Nat := fullRecordGapCenterValue + 588108

theorem fullRecordGapTerm09785_eq_value :
    recordGapCenter + 588108 = fullRecordGapValue09785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09785 (fullRecordGapValue09785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09785_not_prime : ¬(recordGapCenter + 588108).Prime := by
  rw [fullRecordGapTerm09785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09785_fast_pow_mod_ne_one

def fullRecordGapValue09786 : Nat := fullRecordGapCenterValue + 588206

theorem fullRecordGapTerm09786_eq_value :
    recordGapCenter + 588206 = fullRecordGapValue09786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09786 (fullRecordGapValue09786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09786_not_prime : ¬(recordGapCenter + 588206).Prime := by
  rw [fullRecordGapTerm09786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09786_fast_pow_mod_ne_one

def fullRecordGapValue09787 : Nat := fullRecordGapCenterValue + 588282

theorem fullRecordGapTerm09787_eq_value :
    recordGapCenter + 588282 = fullRecordGapValue09787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09787 (fullRecordGapValue09787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09787_not_prime : ¬(recordGapCenter + 588282).Prime := by
  rw [fullRecordGapTerm09787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09787_fast_pow_mod_ne_one

def fullRecordGapValue09788 : Nat := fullRecordGapCenterValue + 588332

theorem fullRecordGapTerm09788_eq_value :
    recordGapCenter + 588332 = fullRecordGapValue09788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09788 (fullRecordGapValue09788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09788_not_prime : ¬(recordGapCenter + 588332).Prime := by
  rw [fullRecordGapTerm09788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09788_fast_pow_mod_ne_one

def fullRecordGapValue09789 : Nat := fullRecordGapCenterValue + 588362

theorem fullRecordGapTerm09789_eq_value :
    recordGapCenter + 588362 = fullRecordGapValue09789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09789 (fullRecordGapValue09789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09789_not_prime : ¬(recordGapCenter + 588362).Prime := by
  rw [fullRecordGapTerm09789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09789_fast_pow_mod_ne_one

def fullRecordGapValue09790 : Nat := fullRecordGapCenterValue + 588396

theorem fullRecordGapTerm09790_eq_value :
    recordGapCenter + 588396 = fullRecordGapValue09790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09790 (fullRecordGapValue09790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09790_not_prime : ¬(recordGapCenter + 588396).Prime := by
  rw [fullRecordGapTerm09790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09790_fast_pow_mod_ne_one

def fullRecordGapValue09791 : Nat := fullRecordGapCenterValue + 588422

theorem fullRecordGapTerm09791_eq_value :
    recordGapCenter + 588422 = fullRecordGapValue09791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09791 (fullRecordGapValue09791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09791_not_prime : ¬(recordGapCenter + 588422).Prime := by
  rw [fullRecordGapTerm09791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09791_fast_pow_mod_ne_one

def fullRecordGapValue09792 : Nat := fullRecordGapCenterValue + 588446

theorem fullRecordGapTerm09792_eq_value :
    recordGapCenter + 588446 = fullRecordGapValue09792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09792 (fullRecordGapValue09792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09792_not_prime : ¬(recordGapCenter + 588446).Prime := by
  rw [fullRecordGapTerm09792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09792_fast_pow_mod_ne_one

def fullRecordGapValue09793 : Nat := fullRecordGapCenterValue + 588486

theorem fullRecordGapTerm09793_eq_value :
    recordGapCenter + 588486 = fullRecordGapValue09793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09793 (fullRecordGapValue09793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09793_not_prime : ¬(recordGapCenter + 588486).Prime := by
  rw [fullRecordGapTerm09793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09793_fast_pow_mod_ne_one

def fullRecordGapValue09794 : Nat := fullRecordGapCenterValue + 588488

theorem fullRecordGapTerm09794_eq_value :
    recordGapCenter + 588488 = fullRecordGapValue09794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09794 (fullRecordGapValue09794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09794_not_prime : ¬(recordGapCenter + 588488).Prime := by
  rw [fullRecordGapTerm09794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09794_fast_pow_mod_ne_one

def fullRecordGapValue09795 : Nat := fullRecordGapCenterValue + 588788

theorem fullRecordGapTerm09795_eq_value :
    recordGapCenter + 588788 = fullRecordGapValue09795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09795 (fullRecordGapValue09795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09795_not_prime : ¬(recordGapCenter + 588788).Prime := by
  rw [fullRecordGapTerm09795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09795_fast_pow_mod_ne_one

def fullRecordGapValue09796 : Nat := fullRecordGapCenterValue + 588806

theorem fullRecordGapTerm09796_eq_value :
    recordGapCenter + 588806 = fullRecordGapValue09796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09796 (fullRecordGapValue09796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09796_not_prime : ¬(recordGapCenter + 588806).Prime := by
  rw [fullRecordGapTerm09796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09796_fast_pow_mod_ne_one

def fullRecordGapValue09797 : Nat := fullRecordGapCenterValue + 588872

theorem fullRecordGapTerm09797_eq_value :
    recordGapCenter + 588872 = fullRecordGapValue09797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09797 (fullRecordGapValue09797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09797_not_prime : ¬(recordGapCenter + 588872).Prime := by
  rw [fullRecordGapTerm09797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09797_fast_pow_mod_ne_one

def fullRecordGapValue09798 : Nat := fullRecordGapCenterValue + 588908

theorem fullRecordGapTerm09798_eq_value :
    recordGapCenter + 588908 = fullRecordGapValue09798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09798 (fullRecordGapValue09798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09798_not_prime : ¬(recordGapCenter + 588908).Prime := by
  rw [fullRecordGapTerm09798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09798_fast_pow_mod_ne_one

def fullRecordGapValue09799 : Nat := fullRecordGapCenterValue + 588998

theorem fullRecordGapTerm09799_eq_value :
    recordGapCenter + 588998 = fullRecordGapValue09799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09799 (fullRecordGapValue09799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09799_not_prime : ¬(recordGapCenter + 588998).Prime := by
  rw [fullRecordGapTerm09799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09799_fast_pow_mod_ne_one

def fullRecordGapValue09800 : Nat := fullRecordGapCenterValue + 589010

theorem fullRecordGapTerm09800_eq_value :
    recordGapCenter + 589010 = fullRecordGapValue09800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09800 (fullRecordGapValue09800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09800_not_prime : ¬(recordGapCenter + 589010).Prime := by
  rw [fullRecordGapTerm09800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09800_fast_pow_mod_ne_one

def fullRecordGapValue09801 : Nat := fullRecordGapCenterValue + 589052

theorem fullRecordGapTerm09801_eq_value :
    recordGapCenter + 589052 = fullRecordGapValue09801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09801 (fullRecordGapValue09801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09801_not_prime : ¬(recordGapCenter + 589052).Prime := by
  rw [fullRecordGapTerm09801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09801_fast_pow_mod_ne_one

def fullRecordGapValue09802 : Nat := fullRecordGapCenterValue + 589172

theorem fullRecordGapTerm09802_eq_value :
    recordGapCenter + 589172 = fullRecordGapValue09802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09802 (fullRecordGapValue09802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09802_not_prime : ¬(recordGapCenter + 589172).Prime := by
  rw [fullRecordGapTerm09802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09802_fast_pow_mod_ne_one

def fullRecordGapValue09803 : Nat := fullRecordGapCenterValue + 589208

theorem fullRecordGapTerm09803_eq_value :
    recordGapCenter + 589208 = fullRecordGapValue09803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09803 (fullRecordGapValue09803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09803_not_prime : ¬(recordGapCenter + 589208).Prime := by
  rw [fullRecordGapTerm09803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09803_fast_pow_mod_ne_one

def fullRecordGapValue09804 : Nat := fullRecordGapCenterValue + 589298

theorem fullRecordGapTerm09804_eq_value :
    recordGapCenter + 589298 = fullRecordGapValue09804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09804 (fullRecordGapValue09804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09804_not_prime : ¬(recordGapCenter + 589298).Prime := by
  rw [fullRecordGapTerm09804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09804_fast_pow_mod_ne_one

def fullRecordGapValue09805 : Nat := fullRecordGapCenterValue + 589326

theorem fullRecordGapTerm09805_eq_value :
    recordGapCenter + 589326 = fullRecordGapValue09805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09805 (fullRecordGapValue09805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09805_not_prime : ¬(recordGapCenter + 589326).Prime := by
  rw [fullRecordGapTerm09805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09805_fast_pow_mod_ne_one

def fullRecordGapValue09806 : Nat := fullRecordGapCenterValue + 589346

theorem fullRecordGapTerm09806_eq_value :
    recordGapCenter + 589346 = fullRecordGapValue09806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09806 (fullRecordGapValue09806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09806_not_prime : ¬(recordGapCenter + 589346).Prime := by
  rw [fullRecordGapTerm09806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09806_fast_pow_mod_ne_one

def fullRecordGapValue09807 : Nat := fullRecordGapCenterValue + 589370

theorem fullRecordGapTerm09807_eq_value :
    recordGapCenter + 589370 = fullRecordGapValue09807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09807 (fullRecordGapValue09807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09807_not_prime : ¬(recordGapCenter + 589370).Prime := by
  rw [fullRecordGapTerm09807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09807_fast_pow_mod_ne_one

def fullRecordGapValue09808 : Nat := fullRecordGapCenterValue + 589388

theorem fullRecordGapTerm09808_eq_value :
    recordGapCenter + 589388 = fullRecordGapValue09808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09808 (fullRecordGapValue09808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09808_not_prime : ¬(recordGapCenter + 589388).Prime := by
  rw [fullRecordGapTerm09808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09808_fast_pow_mod_ne_one

def fullRecordGapValue09809 : Nat := fullRecordGapCenterValue + 589412

theorem fullRecordGapTerm09809_eq_value :
    recordGapCenter + 589412 = fullRecordGapValue09809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09809 (fullRecordGapValue09809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09809_not_prime : ¬(recordGapCenter + 589412).Prime := by
  rw [fullRecordGapTerm09809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09809_fast_pow_mod_ne_one

def fullRecordGapValue09810 : Nat := fullRecordGapCenterValue + 589430

theorem fullRecordGapTerm09810_eq_value :
    recordGapCenter + 589430 = fullRecordGapValue09810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09810 (fullRecordGapValue09810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09810_not_prime : ¬(recordGapCenter + 589430).Prime := by
  rw [fullRecordGapTerm09810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09810_fast_pow_mod_ne_one

def fullRecordGapValue09811 : Nat := fullRecordGapCenterValue + 589502

theorem fullRecordGapTerm09811_eq_value :
    recordGapCenter + 589502 = fullRecordGapValue09811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09811 (fullRecordGapValue09811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09811_not_prime : ¬(recordGapCenter + 589502).Prime := by
  rw [fullRecordGapTerm09811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09811_fast_pow_mod_ne_one

def fullRecordGapValue09812 : Nat := fullRecordGapCenterValue + 589542

theorem fullRecordGapTerm09812_eq_value :
    recordGapCenter + 589542 = fullRecordGapValue09812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09812 (fullRecordGapValue09812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09812_not_prime : ¬(recordGapCenter + 589542).Prime := by
  rw [fullRecordGapTerm09812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09812_fast_pow_mod_ne_one

def fullRecordGapValue09813 : Nat := fullRecordGapCenterValue + 589562

theorem fullRecordGapTerm09813_eq_value :
    recordGapCenter + 589562 = fullRecordGapValue09813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09813 (fullRecordGapValue09813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09813_not_prime : ¬(recordGapCenter + 589562).Prime := by
  rw [fullRecordGapTerm09813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09813_fast_pow_mod_ne_one

def fullRecordGapValue09814 : Nat := fullRecordGapCenterValue + 589592

theorem fullRecordGapTerm09814_eq_value :
    recordGapCenter + 589592 = fullRecordGapValue09814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09814 (fullRecordGapValue09814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09814_not_prime : ¬(recordGapCenter + 589592).Prime := by
  rw [fullRecordGapTerm09814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09814_fast_pow_mod_ne_one

def fullRecordGapValue09815 : Nat := fullRecordGapCenterValue + 589718

theorem fullRecordGapTerm09815_eq_value :
    recordGapCenter + 589718 = fullRecordGapValue09815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09815 (fullRecordGapValue09815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09815_not_prime : ¬(recordGapCenter + 589718).Prime := by
  rw [fullRecordGapTerm09815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09815_fast_pow_mod_ne_one

def fullRecordGapValue09816 : Nat := fullRecordGapCenterValue + 589782

theorem fullRecordGapTerm09816_eq_value :
    recordGapCenter + 589782 = fullRecordGapValue09816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09816 (fullRecordGapValue09816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09816_not_prime : ¬(recordGapCenter + 589782).Prime := by
  rw [fullRecordGapTerm09816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09816_fast_pow_mod_ne_one

def fullRecordGapValue09817 : Nat := fullRecordGapCenterValue + 589790

theorem fullRecordGapTerm09817_eq_value :
    recordGapCenter + 589790 = fullRecordGapValue09817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09817 (fullRecordGapValue09817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09817_not_prime : ¬(recordGapCenter + 589790).Prime := by
  rw [fullRecordGapTerm09817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09817_fast_pow_mod_ne_one

def fullRecordGapValue09818 : Nat := fullRecordGapCenterValue + 589796

theorem fullRecordGapTerm09818_eq_value :
    recordGapCenter + 589796 = fullRecordGapValue09818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09818 (fullRecordGapValue09818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09818_not_prime : ¬(recordGapCenter + 589796).Prime := by
  rw [fullRecordGapTerm09818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09818_fast_pow_mod_ne_one

def fullRecordGapValue09819 : Nat := fullRecordGapCenterValue + 589962

theorem fullRecordGapTerm09819_eq_value :
    recordGapCenter + 589962 = fullRecordGapValue09819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09819 (fullRecordGapValue09819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09819_not_prime : ¬(recordGapCenter + 589962).Prime := by
  rw [fullRecordGapTerm09819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09819_fast_pow_mod_ne_one

def fullRecordGapValue09820 : Nat := fullRecordGapCenterValue + 589982

theorem fullRecordGapTerm09820_eq_value :
    recordGapCenter + 589982 = fullRecordGapValue09820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09820 (fullRecordGapValue09820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09820_not_prime : ¬(recordGapCenter + 589982).Prime := by
  rw [fullRecordGapTerm09820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09820_fast_pow_mod_ne_one

def fullRecordGapValue09821 : Nat := fullRecordGapCenterValue + 590012

theorem fullRecordGapTerm09821_eq_value :
    recordGapCenter + 590012 = fullRecordGapValue09821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09821 (fullRecordGapValue09821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09821_not_prime : ¬(recordGapCenter + 590012).Prime := by
  rw [fullRecordGapTerm09821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09821_fast_pow_mod_ne_one

def fullRecordGapValue09822 : Nat := fullRecordGapCenterValue + 590028

theorem fullRecordGapTerm09822_eq_value :
    recordGapCenter + 590028 = fullRecordGapValue09822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09822 (fullRecordGapValue09822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09822_not_prime : ¬(recordGapCenter + 590028).Prime := by
  rw [fullRecordGapTerm09822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09822_fast_pow_mod_ne_one

def fullRecordGapValue09823 : Nat := fullRecordGapCenterValue + 590052

theorem fullRecordGapTerm09823_eq_value :
    recordGapCenter + 590052 = fullRecordGapValue09823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09823 (fullRecordGapValue09823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09823_not_prime : ¬(recordGapCenter + 590052).Prime := by
  rw [fullRecordGapTerm09823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09823_fast_pow_mod_ne_one

def fullRecordGapValue09824 : Nat := fullRecordGapCenterValue + 590066

theorem fullRecordGapTerm09824_eq_value :
    recordGapCenter + 590066 = fullRecordGapValue09824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09824 (fullRecordGapValue09824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09824_not_prime : ¬(recordGapCenter + 590066).Prime := by
  rw [fullRecordGapTerm09824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09824_fast_pow_mod_ne_one

def fullRecordGapValue09825 : Nat := fullRecordGapCenterValue + 590082

theorem fullRecordGapTerm09825_eq_value :
    recordGapCenter + 590082 = fullRecordGapValue09825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09825 (fullRecordGapValue09825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09825_not_prime : ¬(recordGapCenter + 590082).Prime := by
  rw [fullRecordGapTerm09825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09825_fast_pow_mod_ne_one

def fullRecordGapValue09826 : Nat := fullRecordGapCenterValue + 590222

theorem fullRecordGapTerm09826_eq_value :
    recordGapCenter + 590222 = fullRecordGapValue09826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09826 (fullRecordGapValue09826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09826_not_prime : ¬(recordGapCenter + 590222).Prime := by
  rw [fullRecordGapTerm09826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09826_fast_pow_mod_ne_one

def fullRecordGapValue09827 : Nat := fullRecordGapCenterValue + 590228

theorem fullRecordGapTerm09827_eq_value :
    recordGapCenter + 590228 = fullRecordGapValue09827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09827 (fullRecordGapValue09827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09827_not_prime : ¬(recordGapCenter + 590228).Prime := by
  rw [fullRecordGapTerm09827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09827_fast_pow_mod_ne_one

def fullRecordGapValue09828 : Nat := fullRecordGapCenterValue + 590258

theorem fullRecordGapTerm09828_eq_value :
    recordGapCenter + 590258 = fullRecordGapValue09828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09828 (fullRecordGapValue09828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09828_not_prime : ¬(recordGapCenter + 590258).Prime := by
  rw [fullRecordGapTerm09828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09828_fast_pow_mod_ne_one

def fullRecordGapValue09829 : Nat := fullRecordGapCenterValue + 590412

theorem fullRecordGapTerm09829_eq_value :
    recordGapCenter + 590412 = fullRecordGapValue09829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09829 (fullRecordGapValue09829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09829_not_prime : ¬(recordGapCenter + 590412).Prime := by
  rw [fullRecordGapTerm09829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09829_fast_pow_mod_ne_one

def fullRecordGapValue09830 : Nat := fullRecordGapCenterValue + 590438

theorem fullRecordGapTerm09830_eq_value :
    recordGapCenter + 590438 = fullRecordGapValue09830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09830 (fullRecordGapValue09830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09830_not_prime : ¬(recordGapCenter + 590438).Prime := by
  rw [fullRecordGapTerm09830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09830_fast_pow_mod_ne_one

def fullRecordGapValue09831 : Nat := fullRecordGapCenterValue + 590552

theorem fullRecordGapTerm09831_eq_value :
    recordGapCenter + 590552 = fullRecordGapValue09831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09831 (fullRecordGapValue09831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09831_not_prime : ¬(recordGapCenter + 590552).Prime := by
  rw [fullRecordGapTerm09831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09831_fast_pow_mod_ne_one

def fullRecordGapValue09832 : Nat := fullRecordGapCenterValue + 590658

theorem fullRecordGapTerm09832_eq_value :
    recordGapCenter + 590658 = fullRecordGapValue09832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09832 (fullRecordGapValue09832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09832_not_prime : ¬(recordGapCenter + 590658).Prime := by
  rw [fullRecordGapTerm09832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09832_fast_pow_mod_ne_one

def fullRecordGapValue09833 : Nat := fullRecordGapCenterValue + 590822

theorem fullRecordGapTerm09833_eq_value :
    recordGapCenter + 590822 = fullRecordGapValue09833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09833 (fullRecordGapValue09833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09833_not_prime : ¬(recordGapCenter + 590822).Prime := by
  rw [fullRecordGapTerm09833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09833_fast_pow_mod_ne_one

def fullRecordGapValue09834 : Nat := fullRecordGapCenterValue + 590838

theorem fullRecordGapTerm09834_eq_value :
    recordGapCenter + 590838 = fullRecordGapValue09834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09834 (fullRecordGapValue09834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09834_not_prime : ¬(recordGapCenter + 590838).Prime := by
  rw [fullRecordGapTerm09834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09834_fast_pow_mod_ne_one

def fullRecordGapValue09835 : Nat := fullRecordGapCenterValue + 590858

theorem fullRecordGapTerm09835_eq_value :
    recordGapCenter + 590858 = fullRecordGapValue09835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09835 (fullRecordGapValue09835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09835_not_prime : ¬(recordGapCenter + 590858).Prime := by
  rw [fullRecordGapTerm09835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09835_fast_pow_mod_ne_one

def fullRecordGapValue09836 : Nat := fullRecordGapCenterValue + 590936

theorem fullRecordGapTerm09836_eq_value :
    recordGapCenter + 590936 = fullRecordGapValue09836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09836 (fullRecordGapValue09836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09836_not_prime : ¬(recordGapCenter + 590936).Prime := by
  rw [fullRecordGapTerm09836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09836_fast_pow_mod_ne_one

def fullRecordGapValue09837 : Nat := fullRecordGapCenterValue + 590972

theorem fullRecordGapTerm09837_eq_value :
    recordGapCenter + 590972 = fullRecordGapValue09837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09837 (fullRecordGapValue09837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09837_not_prime : ¬(recordGapCenter + 590972).Prime := by
  rw [fullRecordGapTerm09837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09837_fast_pow_mod_ne_one

def fullRecordGapValue09838 : Nat := fullRecordGapCenterValue + 591036

theorem fullRecordGapTerm09838_eq_value :
    recordGapCenter + 591036 = fullRecordGapValue09838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09838 (fullRecordGapValue09838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09838_not_prime : ¬(recordGapCenter + 591036).Prime := by
  rw [fullRecordGapTerm09838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09838_fast_pow_mod_ne_one

def fullRecordGapValue09839 : Nat := fullRecordGapCenterValue + 591116

theorem fullRecordGapTerm09839_eq_value :
    recordGapCenter + 591116 = fullRecordGapValue09839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09839 (fullRecordGapValue09839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09839_not_prime : ¬(recordGapCenter + 591116).Prime := by
  rw [fullRecordGapTerm09839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09839_fast_pow_mod_ne_one

def fullRecordGapValue09840 : Nat := fullRecordGapCenterValue + 591176

theorem fullRecordGapTerm09840_eq_value :
    recordGapCenter + 591176 = fullRecordGapValue09840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09840 (fullRecordGapValue09840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09840_not_prime : ¬(recordGapCenter + 591176).Prime := by
  rw [fullRecordGapTerm09840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09840_fast_pow_mod_ne_one

def fullRecordGapValue09841 : Nat := fullRecordGapCenterValue + 591230

theorem fullRecordGapTerm09841_eq_value :
    recordGapCenter + 591230 = fullRecordGapValue09841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09841 (fullRecordGapValue09841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09841_not_prime : ¬(recordGapCenter + 591230).Prime := by
  rw [fullRecordGapTerm09841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09841_fast_pow_mod_ne_one

def fullRecordGapValue09842 : Nat := fullRecordGapCenterValue + 591258

theorem fullRecordGapTerm09842_eq_value :
    recordGapCenter + 591258 = fullRecordGapValue09842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09842 (fullRecordGapValue09842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09842_not_prime : ¬(recordGapCenter + 591258).Prime := by
  rw [fullRecordGapTerm09842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09842_fast_pow_mod_ne_one

def fullRecordGapValue09843 : Nat := fullRecordGapCenterValue + 591348

theorem fullRecordGapTerm09843_eq_value :
    recordGapCenter + 591348 = fullRecordGapValue09843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09843 (fullRecordGapValue09843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09843_not_prime : ¬(recordGapCenter + 591348).Prime := by
  rw [fullRecordGapTerm09843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09843_fast_pow_mod_ne_one

def fullRecordGapValue09844 : Nat := fullRecordGapCenterValue + 591360

theorem fullRecordGapTerm09844_eq_value :
    recordGapCenter + 591360 = fullRecordGapValue09844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09844 (fullRecordGapValue09844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09844_not_prime : ¬(recordGapCenter + 591360).Prime := by
  rw [fullRecordGapTerm09844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09844_fast_pow_mod_ne_one

def fullRecordGapValue09845 : Nat := fullRecordGapCenterValue + 591410

theorem fullRecordGapTerm09845_eq_value :
    recordGapCenter + 591410 = fullRecordGapValue09845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09845 (fullRecordGapValue09845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09845_not_prime : ¬(recordGapCenter + 591410).Prime := by
  rw [fullRecordGapTerm09845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09845_fast_pow_mod_ne_one

def fullRecordGapValue09846 : Nat := fullRecordGapCenterValue + 591512

theorem fullRecordGapTerm09846_eq_value :
    recordGapCenter + 591512 = fullRecordGapValue09846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09846 (fullRecordGapValue09846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09846_not_prime : ¬(recordGapCenter + 591512).Prime := by
  rw [fullRecordGapTerm09846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09846_fast_pow_mod_ne_one

def fullRecordGapValue09847 : Nat := fullRecordGapCenterValue + 591518

theorem fullRecordGapTerm09847_eq_value :
    recordGapCenter + 591518 = fullRecordGapValue09847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09847 (fullRecordGapValue09847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09847_not_prime : ¬(recordGapCenter + 591518).Prime := by
  rw [fullRecordGapTerm09847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09847_fast_pow_mod_ne_one

def fullRecordGapValue09848 : Nat := fullRecordGapCenterValue + 591608

theorem fullRecordGapTerm09848_eq_value :
    recordGapCenter + 591608 = fullRecordGapValue09848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09848 (fullRecordGapValue09848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09848_not_prime : ¬(recordGapCenter + 591608).Prime := by
  rw [fullRecordGapTerm09848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09848_fast_pow_mod_ne_one

def fullRecordGapValue09849 : Nat := fullRecordGapCenterValue + 591830

theorem fullRecordGapTerm09849_eq_value :
    recordGapCenter + 591830 = fullRecordGapValue09849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09849 (fullRecordGapValue09849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09849_not_prime : ¬(recordGapCenter + 591830).Prime := by
  rw [fullRecordGapTerm09849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09849_fast_pow_mod_ne_one

def fullRecordGapValue09850 : Nat := fullRecordGapCenterValue + 591986

theorem fullRecordGapTerm09850_eq_value :
    recordGapCenter + 591986 = fullRecordGapValue09850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09850 (fullRecordGapValue09850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09850_not_prime : ¬(recordGapCenter + 591986).Prime := by
  rw [fullRecordGapTerm09850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09850_fast_pow_mod_ne_one

def fullRecordGapValue09851 : Nat := fullRecordGapCenterValue + 592068

theorem fullRecordGapTerm09851_eq_value :
    recordGapCenter + 592068 = fullRecordGapValue09851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09851 (fullRecordGapValue09851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09851_not_prime : ¬(recordGapCenter + 592068).Prime := by
  rw [fullRecordGapTerm09851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09851_fast_pow_mod_ne_one

def fullRecordGapValue09852 : Nat := fullRecordGapCenterValue + 592070

theorem fullRecordGapTerm09852_eq_value :
    recordGapCenter + 592070 = fullRecordGapValue09852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09852 (fullRecordGapValue09852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09852_not_prime : ¬(recordGapCenter + 592070).Prime := by
  rw [fullRecordGapTerm09852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09852_fast_pow_mod_ne_one

def fullRecordGapValue09853 : Nat := fullRecordGapCenterValue + 592142

theorem fullRecordGapTerm09853_eq_value :
    recordGapCenter + 592142 = fullRecordGapValue09853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09853 (fullRecordGapValue09853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09853_not_prime : ¬(recordGapCenter + 592142).Prime := by
  rw [fullRecordGapTerm09853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09853_fast_pow_mod_ne_one

def fullRecordGapValue09854 : Nat := fullRecordGapCenterValue + 592166

theorem fullRecordGapTerm09854_eq_value :
    recordGapCenter + 592166 = fullRecordGapValue09854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09854 (fullRecordGapValue09854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09854_not_prime : ¬(recordGapCenter + 592166).Prime := by
  rw [fullRecordGapTerm09854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09854_fast_pow_mod_ne_one

def fullRecordGapValue09855 : Nat := fullRecordGapCenterValue + 592292

theorem fullRecordGapTerm09855_eq_value :
    recordGapCenter + 592292 = fullRecordGapValue09855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09855 (fullRecordGapValue09855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09855_not_prime : ¬(recordGapCenter + 592292).Prime := by
  rw [fullRecordGapTerm09855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09855_fast_pow_mod_ne_one

def fullRecordGapValue09856 : Nat := fullRecordGapCenterValue + 592316

theorem fullRecordGapTerm09856_eq_value :
    recordGapCenter + 592316 = fullRecordGapValue09856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09856 (fullRecordGapValue09856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09856_not_prime : ¬(recordGapCenter + 592316).Prime := by
  rw [fullRecordGapTerm09856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09856_fast_pow_mod_ne_one

def fullRecordGapValue09857 : Nat := fullRecordGapCenterValue + 592386

theorem fullRecordGapTerm09857_eq_value :
    recordGapCenter + 592386 = fullRecordGapValue09857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09857 (fullRecordGapValue09857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09857_not_prime : ¬(recordGapCenter + 592386).Prime := by
  rw [fullRecordGapTerm09857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09857_fast_pow_mod_ne_one

def fullRecordGapValue09858 : Nat := fullRecordGapCenterValue + 592422

theorem fullRecordGapTerm09858_eq_value :
    recordGapCenter + 592422 = fullRecordGapValue09858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09858 (fullRecordGapValue09858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09858_not_prime : ¬(recordGapCenter + 592422).Prime := by
  rw [fullRecordGapTerm09858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09858_fast_pow_mod_ne_one

def fullRecordGapValue09859 : Nat := fullRecordGapCenterValue + 592442

theorem fullRecordGapTerm09859_eq_value :
    recordGapCenter + 592442 = fullRecordGapValue09859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09859 (fullRecordGapValue09859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09859_not_prime : ¬(recordGapCenter + 592442).Prime := by
  rw [fullRecordGapTerm09859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09859_fast_pow_mod_ne_one

def fullRecordGapValue09860 : Nat := fullRecordGapCenterValue + 592502

theorem fullRecordGapTerm09860_eq_value :
    recordGapCenter + 592502 = fullRecordGapValue09860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09860 (fullRecordGapValue09860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09860_not_prime : ¬(recordGapCenter + 592502).Prime := by
  rw [fullRecordGapTerm09860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09860_fast_pow_mod_ne_one

def fullRecordGapValue09861 : Nat := fullRecordGapCenterValue + 592568

theorem fullRecordGapTerm09861_eq_value :
    recordGapCenter + 592568 = fullRecordGapValue09861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09861 (fullRecordGapValue09861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09861_not_prime : ¬(recordGapCenter + 592568).Prime := by
  rw [fullRecordGapTerm09861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09861_fast_pow_mod_ne_one

def fullRecordGapValue09862 : Nat := fullRecordGapCenterValue + 592616

theorem fullRecordGapTerm09862_eq_value :
    recordGapCenter + 592616 = fullRecordGapValue09862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09862 (fullRecordGapValue09862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09862_not_prime : ¬(recordGapCenter + 592616).Prime := by
  rw [fullRecordGapTerm09862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09862_fast_pow_mod_ne_one

def fullRecordGapValue09863 : Nat := fullRecordGapCenterValue + 592638

theorem fullRecordGapTerm09863_eq_value :
    recordGapCenter + 592638 = fullRecordGapValue09863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09863 (fullRecordGapValue09863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09863_not_prime : ¬(recordGapCenter + 592638).Prime := by
  rw [fullRecordGapTerm09863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09863_fast_pow_mod_ne_one

def fullRecordGapValue09864 : Nat := fullRecordGapCenterValue + 592716

theorem fullRecordGapTerm09864_eq_value :
    recordGapCenter + 592716 = fullRecordGapValue09864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09864 (fullRecordGapValue09864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09864_not_prime : ¬(recordGapCenter + 592716).Prime := by
  rw [fullRecordGapTerm09864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09864_fast_pow_mod_ne_one

def fullRecordGapValue09865 : Nat := fullRecordGapCenterValue + 592730

theorem fullRecordGapTerm09865_eq_value :
    recordGapCenter + 592730 = fullRecordGapValue09865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09865 (fullRecordGapValue09865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09865_not_prime : ¬(recordGapCenter + 592730).Prime := by
  rw [fullRecordGapTerm09865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09865_fast_pow_mod_ne_one

def fullRecordGapValue09866 : Nat := fullRecordGapCenterValue + 592842

theorem fullRecordGapTerm09866_eq_value :
    recordGapCenter + 592842 = fullRecordGapValue09866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09866 (fullRecordGapValue09866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09866_not_prime : ¬(recordGapCenter + 592842).Prime := by
  rw [fullRecordGapTerm09866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09866_fast_pow_mod_ne_one

def fullRecordGapValue09867 : Nat := fullRecordGapCenterValue + 592916

theorem fullRecordGapTerm09867_eq_value :
    recordGapCenter + 592916 = fullRecordGapValue09867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09867 (fullRecordGapValue09867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09867_not_prime : ¬(recordGapCenter + 592916).Prime := by
  rw [fullRecordGapTerm09867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09867_fast_pow_mod_ne_one

def fullRecordGapValue09868 : Nat := fullRecordGapCenterValue + 592932

theorem fullRecordGapTerm09868_eq_value :
    recordGapCenter + 592932 = fullRecordGapValue09868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09868 (fullRecordGapValue09868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09868_not_prime : ¬(recordGapCenter + 592932).Prime := by
  rw [fullRecordGapTerm09868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09868_fast_pow_mod_ne_one

def fullRecordGapValue09869 : Nat := fullRecordGapCenterValue + 593022

theorem fullRecordGapTerm09869_eq_value :
    recordGapCenter + 593022 = fullRecordGapValue09869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09869 (fullRecordGapValue09869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09869_not_prime : ¬(recordGapCenter + 593022).Prime := by
  rw [fullRecordGapTerm09869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09869_fast_pow_mod_ne_one

def fullRecordGapValue09870 : Nat := fullRecordGapCenterValue + 593048

theorem fullRecordGapTerm09870_eq_value :
    recordGapCenter + 593048 = fullRecordGapValue09870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09870 (fullRecordGapValue09870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09870_not_prime : ¬(recordGapCenter + 593048).Prime := by
  rw [fullRecordGapTerm09870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09870_fast_pow_mod_ne_one

def fullRecordGapValue09871 : Nat := fullRecordGapCenterValue + 593192

theorem fullRecordGapTerm09871_eq_value :
    recordGapCenter + 593192 = fullRecordGapValue09871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09871 (fullRecordGapValue09871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09871_not_prime : ¬(recordGapCenter + 593192).Prime := by
  rw [fullRecordGapTerm09871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09871_fast_pow_mod_ne_one

def fullRecordGapValue09872 : Nat := fullRecordGapCenterValue + 593330

theorem fullRecordGapTerm09872_eq_value :
    recordGapCenter + 593330 = fullRecordGapValue09872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09872 (fullRecordGapValue09872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09872_not_prime : ¬(recordGapCenter + 593330).Prime := by
  rw [fullRecordGapTerm09872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09872_fast_pow_mod_ne_one

def fullRecordGapValue09873 : Nat := fullRecordGapCenterValue + 593426

theorem fullRecordGapTerm09873_eq_value :
    recordGapCenter + 593426 = fullRecordGapValue09873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09873 (fullRecordGapValue09873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09873_not_prime : ¬(recordGapCenter + 593426).Prime := by
  rw [fullRecordGapTerm09873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09873_fast_pow_mod_ne_one

def fullRecordGapValue09874 : Nat := fullRecordGapCenterValue + 593498

theorem fullRecordGapTerm09874_eq_value :
    recordGapCenter + 593498 = fullRecordGapValue09874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09874 (fullRecordGapValue09874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09874_not_prime : ¬(recordGapCenter + 593498).Prime := by
  rw [fullRecordGapTerm09874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09874_fast_pow_mod_ne_one

def fullRecordGapValue09875 : Nat := fullRecordGapCenterValue + 593546

theorem fullRecordGapTerm09875_eq_value :
    recordGapCenter + 593546 = fullRecordGapValue09875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09875 (fullRecordGapValue09875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09875_not_prime : ¬(recordGapCenter + 593546).Prime := by
  rw [fullRecordGapTerm09875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09875_fast_pow_mod_ne_one

def fullRecordGapValue09876 : Nat := fullRecordGapCenterValue + 593562

theorem fullRecordGapTerm09876_eq_value :
    recordGapCenter + 593562 = fullRecordGapValue09876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09876 (fullRecordGapValue09876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09876_not_prime : ¬(recordGapCenter + 593562).Prime := by
  rw [fullRecordGapTerm09876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09876_fast_pow_mod_ne_one

def fullRecordGapValue09877 : Nat := fullRecordGapCenterValue + 593576

theorem fullRecordGapTerm09877_eq_value :
    recordGapCenter + 593576 = fullRecordGapValue09877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09877 (fullRecordGapValue09877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09877_not_prime : ¬(recordGapCenter + 593576).Prime := by
  rw [fullRecordGapTerm09877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09877_fast_pow_mod_ne_one

def fullRecordGapValue09878 : Nat := fullRecordGapCenterValue + 593612

theorem fullRecordGapTerm09878_eq_value :
    recordGapCenter + 593612 = fullRecordGapValue09878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09878 (fullRecordGapValue09878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09878_not_prime : ¬(recordGapCenter + 593612).Prime := by
  rw [fullRecordGapTerm09878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09878_fast_pow_mod_ne_one

def fullRecordGapValue09879 : Nat := fullRecordGapCenterValue + 593672

theorem fullRecordGapTerm09879_eq_value :
    recordGapCenter + 593672 = fullRecordGapValue09879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09879 (fullRecordGapValue09879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09879_not_prime : ¬(recordGapCenter + 593672).Prime := by
  rw [fullRecordGapTerm09879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09879_fast_pow_mod_ne_one

def fullRecordGapValue09880 : Nat := fullRecordGapCenterValue + 593756

theorem fullRecordGapTerm09880_eq_value :
    recordGapCenter + 593756 = fullRecordGapValue09880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09880 (fullRecordGapValue09880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09880_not_prime : ¬(recordGapCenter + 593756).Prime := by
  rw [fullRecordGapTerm09880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09880_fast_pow_mod_ne_one

def fullRecordGapValue09881 : Nat := fullRecordGapCenterValue + 593772

theorem fullRecordGapTerm09881_eq_value :
    recordGapCenter + 593772 = fullRecordGapValue09881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09881 (fullRecordGapValue09881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09881_not_prime : ¬(recordGapCenter + 593772).Prime := by
  rw [fullRecordGapTerm09881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09881_fast_pow_mod_ne_one

def fullRecordGapValue09882 : Nat := fullRecordGapCenterValue + 593778

theorem fullRecordGapTerm09882_eq_value :
    recordGapCenter + 593778 = fullRecordGapValue09882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09882 (fullRecordGapValue09882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09882_not_prime : ¬(recordGapCenter + 593778).Prime := by
  rw [fullRecordGapTerm09882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09882_fast_pow_mod_ne_one

def fullRecordGapValue09883 : Nat := fullRecordGapCenterValue + 593828

theorem fullRecordGapTerm09883_eq_value :
    recordGapCenter + 593828 = fullRecordGapValue09883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09883 (fullRecordGapValue09883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09883_not_prime : ¬(recordGapCenter + 593828).Prime := by
  rw [fullRecordGapTerm09883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09883_fast_pow_mod_ne_one

def fullRecordGapValue09884 : Nat := fullRecordGapCenterValue + 593876

theorem fullRecordGapTerm09884_eq_value :
    recordGapCenter + 593876 = fullRecordGapValue09884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09884 (fullRecordGapValue09884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09884_not_prime : ¬(recordGapCenter + 593876).Prime := by
  rw [fullRecordGapTerm09884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09884_fast_pow_mod_ne_one

def fullRecordGapValue09885 : Nat := fullRecordGapCenterValue + 593990

theorem fullRecordGapTerm09885_eq_value :
    recordGapCenter + 593990 = fullRecordGapValue09885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09885 (fullRecordGapValue09885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09885_not_prime : ¬(recordGapCenter + 593990).Prime := by
  rw [fullRecordGapTerm09885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09885_fast_pow_mod_ne_one

def fullRecordGapValue09886 : Nat := fullRecordGapCenterValue + 594102

theorem fullRecordGapTerm09886_eq_value :
    recordGapCenter + 594102 = fullRecordGapValue09886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09886 (fullRecordGapValue09886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09886_not_prime : ¬(recordGapCenter + 594102).Prime := by
  rw [fullRecordGapTerm09886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09886_fast_pow_mod_ne_one

def fullRecordGapValue09887 : Nat := fullRecordGapCenterValue + 594276

theorem fullRecordGapTerm09887_eq_value :
    recordGapCenter + 594276 = fullRecordGapValue09887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09887 (fullRecordGapValue09887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09887_not_prime : ¬(recordGapCenter + 594276).Prime := by
  rw [fullRecordGapTerm09887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09887_fast_pow_mod_ne_one

def fullRecordGapValue09888 : Nat := fullRecordGapCenterValue + 594296

theorem fullRecordGapTerm09888_eq_value :
    recordGapCenter + 594296 = fullRecordGapValue09888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09888 (fullRecordGapValue09888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09888_not_prime : ¬(recordGapCenter + 594296).Prime := by
  rw [fullRecordGapTerm09888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09888_fast_pow_mod_ne_one

def fullRecordGapValue09889 : Nat := fullRecordGapCenterValue + 594318

theorem fullRecordGapTerm09889_eq_value :
    recordGapCenter + 594318 = fullRecordGapValue09889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09889 (fullRecordGapValue09889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09889_not_prime : ¬(recordGapCenter + 594318).Prime := by
  rw [fullRecordGapTerm09889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09889_fast_pow_mod_ne_one

def fullRecordGapValue09890 : Nat := fullRecordGapCenterValue + 594372

theorem fullRecordGapTerm09890_eq_value :
    recordGapCenter + 594372 = fullRecordGapValue09890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09890 (fullRecordGapValue09890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09890_not_prime : ¬(recordGapCenter + 594372).Prime := by
  rw [fullRecordGapTerm09890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09890_fast_pow_mod_ne_one

def fullRecordGapValue09891 : Nat := fullRecordGapCenterValue + 594470

theorem fullRecordGapTerm09891_eq_value :
    recordGapCenter + 594470 = fullRecordGapValue09891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09891 (fullRecordGapValue09891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09891_not_prime : ¬(recordGapCenter + 594470).Prime := by
  rw [fullRecordGapTerm09891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09891_fast_pow_mod_ne_one

def fullRecordGapValue09892 : Nat := fullRecordGapCenterValue + 594618

theorem fullRecordGapTerm09892_eq_value :
    recordGapCenter + 594618 = fullRecordGapValue09892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09892 (fullRecordGapValue09892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09892_not_prime : ¬(recordGapCenter + 594618).Prime := by
  rw [fullRecordGapTerm09892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09892_fast_pow_mod_ne_one

def fullRecordGapValue09893 : Nat := fullRecordGapCenterValue + 594708

theorem fullRecordGapTerm09893_eq_value :
    recordGapCenter + 594708 = fullRecordGapValue09893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09893 (fullRecordGapValue09893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09893_not_prime : ¬(recordGapCenter + 594708).Prime := by
  rw [fullRecordGapTerm09893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09893_fast_pow_mod_ne_one

def fullRecordGapValue09894 : Nat := fullRecordGapCenterValue + 594842

theorem fullRecordGapTerm09894_eq_value :
    recordGapCenter + 594842 = fullRecordGapValue09894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09894 (fullRecordGapValue09894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09894_not_prime : ¬(recordGapCenter + 594842).Prime := by
  rw [fullRecordGapTerm09894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09894_fast_pow_mod_ne_one

def fullRecordGapValue09895 : Nat := fullRecordGapCenterValue + 594938

theorem fullRecordGapTerm09895_eq_value :
    recordGapCenter + 594938 = fullRecordGapValue09895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09895 (fullRecordGapValue09895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09895_not_prime : ¬(recordGapCenter + 594938).Prime := by
  rw [fullRecordGapTerm09895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09895_fast_pow_mod_ne_one

def fullRecordGapValue09896 : Nat := fullRecordGapCenterValue + 594962

theorem fullRecordGapTerm09896_eq_value :
    recordGapCenter + 594962 = fullRecordGapValue09896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09896 (fullRecordGapValue09896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09896_not_prime : ¬(recordGapCenter + 594962).Prime := by
  rw [fullRecordGapTerm09896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09896_fast_pow_mod_ne_one

def fullRecordGapValue09897 : Nat := fullRecordGapCenterValue + 595172

theorem fullRecordGapTerm09897_eq_value :
    recordGapCenter + 595172 = fullRecordGapValue09897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09897 (fullRecordGapValue09897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09897_not_prime : ¬(recordGapCenter + 595172).Prime := by
  rw [fullRecordGapTerm09897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09897_fast_pow_mod_ne_one

def fullRecordGapValue09898 : Nat := fullRecordGapCenterValue + 595178

theorem fullRecordGapTerm09898_eq_value :
    recordGapCenter + 595178 = fullRecordGapValue09898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09898 (fullRecordGapValue09898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09898_not_prime : ¬(recordGapCenter + 595178).Prime := by
  rw [fullRecordGapTerm09898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09898_fast_pow_mod_ne_one

def fullRecordGapValue09899 : Nat := fullRecordGapCenterValue + 595226

theorem fullRecordGapTerm09899_eq_value :
    recordGapCenter + 595226 = fullRecordGapValue09899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09899 (fullRecordGapValue09899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09899_not_prime : ¬(recordGapCenter + 595226).Prime := by
  rw [fullRecordGapTerm09899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09899_fast_pow_mod_ne_one

def fullRecordGapValue09900 : Nat := fullRecordGapCenterValue + 595268

theorem fullRecordGapTerm09900_eq_value :
    recordGapCenter + 595268 = fullRecordGapValue09900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09900 (fullRecordGapValue09900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09900_not_prime : ¬(recordGapCenter + 595268).Prime := by
  rw [fullRecordGapTerm09900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09900_fast_pow_mod_ne_one

def fullRecordGapValue09901 : Nat := fullRecordGapCenterValue + 595352

theorem fullRecordGapTerm09901_eq_value :
    recordGapCenter + 595352 = fullRecordGapValue09901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09901 (fullRecordGapValue09901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09901_not_prime : ¬(recordGapCenter + 595352).Prime := by
  rw [fullRecordGapTerm09901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09901_fast_pow_mod_ne_one

def fullRecordGapValue09902 : Nat := fullRecordGapCenterValue + 595436

theorem fullRecordGapTerm09902_eq_value :
    recordGapCenter + 595436 = fullRecordGapValue09902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09902 (fullRecordGapValue09902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09902_not_prime : ¬(recordGapCenter + 595436).Prime := by
  rw [fullRecordGapTerm09902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09902_fast_pow_mod_ne_one

def fullRecordGapValue09903 : Nat := fullRecordGapCenterValue + 595446

theorem fullRecordGapTerm09903_eq_value :
    recordGapCenter + 595446 = fullRecordGapValue09903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09903 (fullRecordGapValue09903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09903_not_prime : ¬(recordGapCenter + 595446).Prime := by
  rw [fullRecordGapTerm09903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09903_fast_pow_mod_ne_one

def fullRecordGapValue09904 : Nat := fullRecordGapCenterValue + 595542

theorem fullRecordGapTerm09904_eq_value :
    recordGapCenter + 595542 = fullRecordGapValue09904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09904 (fullRecordGapValue09904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09904_not_prime : ¬(recordGapCenter + 595542).Prime := by
  rw [fullRecordGapTerm09904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09904_fast_pow_mod_ne_one

def fullRecordGapValue09905 : Nat := fullRecordGapCenterValue + 595592

theorem fullRecordGapTerm09905_eq_value :
    recordGapCenter + 595592 = fullRecordGapValue09905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09905 (fullRecordGapValue09905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09905_not_prime : ¬(recordGapCenter + 595592).Prime := by
  rw [fullRecordGapTerm09905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09905_fast_pow_mod_ne_one

def fullRecordGapValue09906 : Nat := fullRecordGapCenterValue + 595610

theorem fullRecordGapTerm09906_eq_value :
    recordGapCenter + 595610 = fullRecordGapValue09906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09906 (fullRecordGapValue09906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09906_not_prime : ¬(recordGapCenter + 595610).Prime := by
  rw [fullRecordGapTerm09906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09906_fast_pow_mod_ne_one

def fullRecordGapValue09907 : Nat := fullRecordGapCenterValue + 595652

theorem fullRecordGapTerm09907_eq_value :
    recordGapCenter + 595652 = fullRecordGapValue09907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09907 (fullRecordGapValue09907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09907_not_prime : ¬(recordGapCenter + 595652).Prime := by
  rw [fullRecordGapTerm09907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09907_fast_pow_mod_ne_one

def fullRecordGapValue09908 : Nat := fullRecordGapCenterValue + 595670

theorem fullRecordGapTerm09908_eq_value :
    recordGapCenter + 595670 = fullRecordGapValue09908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09908 (fullRecordGapValue09908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09908_not_prime : ¬(recordGapCenter + 595670).Prime := by
  rw [fullRecordGapTerm09908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09908_fast_pow_mod_ne_one

def fullRecordGapValue09909 : Nat := fullRecordGapCenterValue + 595796

theorem fullRecordGapTerm09909_eq_value :
    recordGapCenter + 595796 = fullRecordGapValue09909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09909 (fullRecordGapValue09909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09909_not_prime : ¬(recordGapCenter + 595796).Prime := by
  rw [fullRecordGapTerm09909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09909_fast_pow_mod_ne_one

def fullRecordGapValue09910 : Nat := fullRecordGapCenterValue + 595956

theorem fullRecordGapTerm09910_eq_value :
    recordGapCenter + 595956 = fullRecordGapValue09910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09910 (fullRecordGapValue09910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09910_not_prime : ¬(recordGapCenter + 595956).Prime := by
  rw [fullRecordGapTerm09910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09910_fast_pow_mod_ne_one

def fullRecordGapValue09911 : Nat := fullRecordGapCenterValue + 596072

theorem fullRecordGapTerm09911_eq_value :
    recordGapCenter + 596072 = fullRecordGapValue09911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09911 (fullRecordGapValue09911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09911_not_prime : ¬(recordGapCenter + 596072).Prime := by
  rw [fullRecordGapTerm09911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09911_fast_pow_mod_ne_one

def fullRecordGapValue09912 : Nat := fullRecordGapCenterValue + 596186

theorem fullRecordGapTerm09912_eq_value :
    recordGapCenter + 596186 = fullRecordGapValue09912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09912 (fullRecordGapValue09912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09912_not_prime : ¬(recordGapCenter + 596186).Prime := by
  rw [fullRecordGapTerm09912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09912_fast_pow_mod_ne_one

def fullRecordGapValue09913 : Nat := fullRecordGapCenterValue + 596202

theorem fullRecordGapTerm09913_eq_value :
    recordGapCenter + 596202 = fullRecordGapValue09913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09913 (fullRecordGapValue09913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09913_not_prime : ¬(recordGapCenter + 596202).Prime := by
  rw [fullRecordGapTerm09913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09913_fast_pow_mod_ne_one

def fullRecordGapValue09914 : Nat := fullRecordGapCenterValue + 596216

theorem fullRecordGapTerm09914_eq_value :
    recordGapCenter + 596216 = fullRecordGapValue09914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09914 (fullRecordGapValue09914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09914_not_prime : ¬(recordGapCenter + 596216).Prime := by
  rw [fullRecordGapTerm09914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09914_fast_pow_mod_ne_one

def fullRecordGapValue09915 : Nat := fullRecordGapCenterValue + 596226

theorem fullRecordGapTerm09915_eq_value :
    recordGapCenter + 596226 = fullRecordGapValue09915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09915 (fullRecordGapValue09915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09915_not_prime : ¬(recordGapCenter + 596226).Prime := by
  rw [fullRecordGapTerm09915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09915_fast_pow_mod_ne_one

def fullRecordGapValue09916 : Nat := fullRecordGapCenterValue + 596276

theorem fullRecordGapTerm09916_eq_value :
    recordGapCenter + 596276 = fullRecordGapValue09916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09916 (fullRecordGapValue09916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09916_not_prime : ¬(recordGapCenter + 596276).Prime := by
  rw [fullRecordGapTerm09916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09916_fast_pow_mod_ne_one

def fullRecordGapValue09917 : Nat := fullRecordGapCenterValue + 596288

theorem fullRecordGapTerm09917_eq_value :
    recordGapCenter + 596288 = fullRecordGapValue09917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09917 (fullRecordGapValue09917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09917_not_prime : ¬(recordGapCenter + 596288).Prime := by
  rw [fullRecordGapTerm09917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09917_fast_pow_mod_ne_one

def fullRecordGapValue09918 : Nat := fullRecordGapCenterValue + 596346

theorem fullRecordGapTerm09918_eq_value :
    recordGapCenter + 596346 = fullRecordGapValue09918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09918 (fullRecordGapValue09918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09918_not_prime : ¬(recordGapCenter + 596346).Prime := by
  rw [fullRecordGapTerm09918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09918_fast_pow_mod_ne_one

def fullRecordGapValue09919 : Nat := fullRecordGapCenterValue + 596348

theorem fullRecordGapTerm09919_eq_value :
    recordGapCenter + 596348 = fullRecordGapValue09919 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09919_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09919 (fullRecordGapValue09919 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09919_not_prime : ¬(recordGapCenter + 596348).Prime := by
  rw [fullRecordGapTerm09919_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09919, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09919_fast_pow_mod_ne_one

def fullRecordGapValue09920 : Nat := fullRecordGapCenterValue + 596382

theorem fullRecordGapTerm09920_eq_value :
    recordGapCenter + 596382 = fullRecordGapValue09920 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09920_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09920 (fullRecordGapValue09920 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09920_not_prime : ¬(recordGapCenter + 596382).Prime := by
  rw [fullRecordGapTerm09920_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09920, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09920_fast_pow_mod_ne_one

def fullRecordGapValue09921 : Nat := fullRecordGapCenterValue + 596396

theorem fullRecordGapTerm09921_eq_value :
    recordGapCenter + 596396 = fullRecordGapValue09921 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09921_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09921 (fullRecordGapValue09921 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09921_not_prime : ¬(recordGapCenter + 596396).Prime := by
  rw [fullRecordGapTerm09921_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09921, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09921_fast_pow_mod_ne_one

def fullRecordGapValue09922 : Nat := fullRecordGapCenterValue + 596408

theorem fullRecordGapTerm09922_eq_value :
    recordGapCenter + 596408 = fullRecordGapValue09922 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09922_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09922 (fullRecordGapValue09922 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09922_not_prime : ¬(recordGapCenter + 596408).Prime := by
  rw [fullRecordGapTerm09922_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09922, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09922_fast_pow_mod_ne_one

def fullRecordGapValue09923 : Nat := fullRecordGapCenterValue + 596426

theorem fullRecordGapTerm09923_eq_value :
    recordGapCenter + 596426 = fullRecordGapValue09923 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09923_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09923 (fullRecordGapValue09923 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09923_not_prime : ¬(recordGapCenter + 596426).Prime := by
  rw [fullRecordGapTerm09923_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09923, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09923_fast_pow_mod_ne_one

def fullRecordGapValue09924 : Nat := fullRecordGapCenterValue + 596522

theorem fullRecordGapTerm09924_eq_value :
    recordGapCenter + 596522 = fullRecordGapValue09924 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09924_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09924 (fullRecordGapValue09924 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09924_not_prime : ¬(recordGapCenter + 596522).Prime := by
  rw [fullRecordGapTerm09924_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09924, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09924_fast_pow_mod_ne_one

def fullRecordGapValue09925 : Nat := fullRecordGapCenterValue + 596586

theorem fullRecordGapTerm09925_eq_value :
    recordGapCenter + 596586 = fullRecordGapValue09925 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09925_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09925 (fullRecordGapValue09925 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09925_not_prime : ¬(recordGapCenter + 596586).Prime := by
  rw [fullRecordGapTerm09925_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09925, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09925_fast_pow_mod_ne_one

def fullRecordGapValue09926 : Nat := fullRecordGapCenterValue + 596606

theorem fullRecordGapTerm09926_eq_value :
    recordGapCenter + 596606 = fullRecordGapValue09926 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09926_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09926 (fullRecordGapValue09926 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09926_not_prime : ¬(recordGapCenter + 596606).Prime := by
  rw [fullRecordGapTerm09926_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09926, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09926_fast_pow_mod_ne_one

def fullRecordGapValue09927 : Nat := fullRecordGapCenterValue + 596612

theorem fullRecordGapTerm09927_eq_value :
    recordGapCenter + 596612 = fullRecordGapValue09927 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09927_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09927 (fullRecordGapValue09927 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09927_not_prime : ¬(recordGapCenter + 596612).Prime := by
  rw [fullRecordGapTerm09927_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09927, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09927_fast_pow_mod_ne_one

def fullRecordGapValue09928 : Nat := fullRecordGapCenterValue + 596678

theorem fullRecordGapTerm09928_eq_value :
    recordGapCenter + 596678 = fullRecordGapValue09928 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09928_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09928 (fullRecordGapValue09928 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09928_not_prime : ¬(recordGapCenter + 596678).Prime := by
  rw [fullRecordGapTerm09928_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09928, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09928_fast_pow_mod_ne_one

def fullRecordGapValue09929 : Nat := fullRecordGapCenterValue + 596690

theorem fullRecordGapTerm09929_eq_value :
    recordGapCenter + 596690 = fullRecordGapValue09929 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09929_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09929 (fullRecordGapValue09929 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09929_not_prime : ¬(recordGapCenter + 596690).Prime := by
  rw [fullRecordGapTerm09929_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09929, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09929_fast_pow_mod_ne_one

def fullRecordGapValue09930 : Nat := fullRecordGapCenterValue + 596732

theorem fullRecordGapTerm09930_eq_value :
    recordGapCenter + 596732 = fullRecordGapValue09930 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09930_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09930 (fullRecordGapValue09930 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09930_not_prime : ¬(recordGapCenter + 596732).Prime := by
  rw [fullRecordGapTerm09930_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09930, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09930_fast_pow_mod_ne_one

def fullRecordGapValue09931 : Nat := fullRecordGapCenterValue + 596738

theorem fullRecordGapTerm09931_eq_value :
    recordGapCenter + 596738 = fullRecordGapValue09931 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09931_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09931 (fullRecordGapValue09931 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09931_not_prime : ¬(recordGapCenter + 596738).Prime := by
  rw [fullRecordGapTerm09931_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09931, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09931_fast_pow_mod_ne_one

def fullRecordGapValue09932 : Nat := fullRecordGapCenterValue + 596822

theorem fullRecordGapTerm09932_eq_value :
    recordGapCenter + 596822 = fullRecordGapValue09932 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09932_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09932 (fullRecordGapValue09932 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09932_not_prime : ¬(recordGapCenter + 596822).Prime := by
  rw [fullRecordGapTerm09932_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09932, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09932_fast_pow_mod_ne_one

def fullRecordGapValue09933 : Nat := fullRecordGapCenterValue + 596888

theorem fullRecordGapTerm09933_eq_value :
    recordGapCenter + 596888 = fullRecordGapValue09933 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09933_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09933 (fullRecordGapValue09933 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09933_not_prime : ¬(recordGapCenter + 596888).Prime := by
  rw [fullRecordGapTerm09933_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09933, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09933_fast_pow_mod_ne_one

def fullRecordGapValue09934 : Nat := fullRecordGapCenterValue + 596982

theorem fullRecordGapTerm09934_eq_value :
    recordGapCenter + 596982 = fullRecordGapValue09934 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09934_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09934 (fullRecordGapValue09934 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09934_not_prime : ¬(recordGapCenter + 596982).Prime := by
  rw [fullRecordGapTerm09934_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09934, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09934_fast_pow_mod_ne_one

def fullRecordGapValue09935 : Nat := fullRecordGapCenterValue + 596996

theorem fullRecordGapTerm09935_eq_value :
    recordGapCenter + 596996 = fullRecordGapValue09935 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09935_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09935 (fullRecordGapValue09935 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09935_not_prime : ¬(recordGapCenter + 596996).Prime := by
  rw [fullRecordGapTerm09935_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09935, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09935_fast_pow_mod_ne_one

def fullRecordGapValue09936 : Nat := fullRecordGapCenterValue + 597026

theorem fullRecordGapTerm09936_eq_value :
    recordGapCenter + 597026 = fullRecordGapValue09936 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09936_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09936 (fullRecordGapValue09936 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09936_not_prime : ¬(recordGapCenter + 597026).Prime := by
  rw [fullRecordGapTerm09936_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09936, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09936_fast_pow_mod_ne_one

def fullRecordGapValue09937 : Nat := fullRecordGapCenterValue + 597158

theorem fullRecordGapTerm09937_eq_value :
    recordGapCenter + 597158 = fullRecordGapValue09937 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09937_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09937 (fullRecordGapValue09937 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09937_not_prime : ¬(recordGapCenter + 597158).Prime := by
  rw [fullRecordGapTerm09937_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09937, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09937_fast_pow_mod_ne_one

def fullRecordGapValue09938 : Nat := fullRecordGapCenterValue + 597242

theorem fullRecordGapTerm09938_eq_value :
    recordGapCenter + 597242 = fullRecordGapValue09938 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09938_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09938 (fullRecordGapValue09938 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09938_not_prime : ¬(recordGapCenter + 597242).Prime := by
  rw [fullRecordGapTerm09938_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09938, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09938_fast_pow_mod_ne_one

def fullRecordGapValue09939 : Nat := fullRecordGapCenterValue + 597306

theorem fullRecordGapTerm09939_eq_value :
    recordGapCenter + 597306 = fullRecordGapValue09939 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09939_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09939 (fullRecordGapValue09939 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09939_not_prime : ¬(recordGapCenter + 597306).Prime := by
  rw [fullRecordGapTerm09939_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09939, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09939_fast_pow_mod_ne_one

def fullRecordGapValue09940 : Nat := fullRecordGapCenterValue + 597396

theorem fullRecordGapTerm09940_eq_value :
    recordGapCenter + 597396 = fullRecordGapValue09940 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09940_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09940 (fullRecordGapValue09940 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09940_not_prime : ¬(recordGapCenter + 597396).Prime := by
  rw [fullRecordGapTerm09940_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09940, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09940_fast_pow_mod_ne_one

def fullRecordGapValue09941 : Nat := fullRecordGapCenterValue + 597446

theorem fullRecordGapTerm09941_eq_value :
    recordGapCenter + 597446 = fullRecordGapValue09941 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09941_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09941 (fullRecordGapValue09941 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09941_not_prime : ¬(recordGapCenter + 597446).Prime := by
  rw [fullRecordGapTerm09941_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09941, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09941_fast_pow_mod_ne_one

def fullRecordGapValue09942 : Nat := fullRecordGapCenterValue + 597518

theorem fullRecordGapTerm09942_eq_value :
    recordGapCenter + 597518 = fullRecordGapValue09942 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09942_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09942 (fullRecordGapValue09942 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09942_not_prime : ¬(recordGapCenter + 597518).Prime := by
  rw [fullRecordGapTerm09942_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09942, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09942_fast_pow_mod_ne_one

def fullRecordGapValue09943 : Nat := fullRecordGapCenterValue + 597572

theorem fullRecordGapTerm09943_eq_value :
    recordGapCenter + 597572 = fullRecordGapValue09943 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09943_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09943 (fullRecordGapValue09943 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09943_not_prime : ¬(recordGapCenter + 597572).Prime := by
  rw [fullRecordGapTerm09943_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09943, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09943_fast_pow_mod_ne_one

def fullRecordGapValue09944 : Nat := fullRecordGapCenterValue + 597612

theorem fullRecordGapTerm09944_eq_value :
    recordGapCenter + 597612 = fullRecordGapValue09944 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09944_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09944 (fullRecordGapValue09944 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09944_not_prime : ¬(recordGapCenter + 597612).Prime := by
  rw [fullRecordGapTerm09944_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09944, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09944_fast_pow_mod_ne_one

def fullRecordGapValue09945 : Nat := fullRecordGapCenterValue + 597642

theorem fullRecordGapTerm09945_eq_value :
    recordGapCenter + 597642 = fullRecordGapValue09945 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09945_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09945 (fullRecordGapValue09945 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09945_not_prime : ¬(recordGapCenter + 597642).Prime := by
  rw [fullRecordGapTerm09945_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09945, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09945_fast_pow_mod_ne_one

def fullRecordGapValue09946 : Nat := fullRecordGapCenterValue + 597656

theorem fullRecordGapTerm09946_eq_value :
    recordGapCenter + 597656 = fullRecordGapValue09946 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09946_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09946 (fullRecordGapValue09946 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09946_not_prime : ¬(recordGapCenter + 597656).Prime := by
  rw [fullRecordGapTerm09946_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09946, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09946_fast_pow_mod_ne_one

def fullRecordGapValue09947 : Nat := fullRecordGapCenterValue + 597738

theorem fullRecordGapTerm09947_eq_value :
    recordGapCenter + 597738 = fullRecordGapValue09947 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09947_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09947 (fullRecordGapValue09947 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09947_not_prime : ¬(recordGapCenter + 597738).Prime := by
  rw [fullRecordGapTerm09947_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09947, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09947_fast_pow_mod_ne_one

def fullRecordGapValue09948 : Nat := fullRecordGapCenterValue + 597836

theorem fullRecordGapTerm09948_eq_value :
    recordGapCenter + 597836 = fullRecordGapValue09948 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09948_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09948 (fullRecordGapValue09948 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09948_not_prime : ¬(recordGapCenter + 597836).Prime := by
  rw [fullRecordGapTerm09948_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09948, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09948_fast_pow_mod_ne_one

def fullRecordGapValue09949 : Nat := fullRecordGapCenterValue + 597858

theorem fullRecordGapTerm09949_eq_value :
    recordGapCenter + 597858 = fullRecordGapValue09949 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09949_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09949 (fullRecordGapValue09949 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09949_not_prime : ¬(recordGapCenter + 597858).Prime := by
  rw [fullRecordGapTerm09949_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09949, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09949_fast_pow_mod_ne_one

def fullRecordGapValue09950 : Nat := fullRecordGapCenterValue + 597966

theorem fullRecordGapTerm09950_eq_value :
    recordGapCenter + 597966 = fullRecordGapValue09950 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09950_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09950 (fullRecordGapValue09950 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09950_not_prime : ¬(recordGapCenter + 597966).Prime := by
  rw [fullRecordGapTerm09950_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09950, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09950_fast_pow_mod_ne_one

def fullRecordGapValue09951 : Nat := fullRecordGapCenterValue + 597972

theorem fullRecordGapTerm09951_eq_value :
    recordGapCenter + 597972 = fullRecordGapValue09951 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09951_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09951 (fullRecordGapValue09951 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09951_not_prime : ¬(recordGapCenter + 597972).Prime := by
  rw [fullRecordGapTerm09951_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09951, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09951_fast_pow_mod_ne_one

def fullRecordGapValue09952 : Nat := fullRecordGapCenterValue + 597986

theorem fullRecordGapTerm09952_eq_value :
    recordGapCenter + 597986 = fullRecordGapValue09952 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09952_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09952 (fullRecordGapValue09952 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09952_not_prime : ¬(recordGapCenter + 597986).Prime := by
  rw [fullRecordGapTerm09952_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09952, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09952_fast_pow_mod_ne_one

def fullRecordGapValue09953 : Nat := fullRecordGapCenterValue + 598232

theorem fullRecordGapTerm09953_eq_value :
    recordGapCenter + 598232 = fullRecordGapValue09953 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09953_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09953 (fullRecordGapValue09953 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09953_not_prime : ¬(recordGapCenter + 598232).Prime := by
  rw [fullRecordGapTerm09953_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09953, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09953_fast_pow_mod_ne_one

def fullRecordGapValue09954 : Nat := fullRecordGapCenterValue + 598236

theorem fullRecordGapTerm09954_eq_value :
    recordGapCenter + 598236 = fullRecordGapValue09954 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09954_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09954 (fullRecordGapValue09954 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09954_not_prime : ¬(recordGapCenter + 598236).Prime := by
  rw [fullRecordGapTerm09954_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09954, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09954_fast_pow_mod_ne_one

def fullRecordGapValue09955 : Nat := fullRecordGapCenterValue + 598358

theorem fullRecordGapTerm09955_eq_value :
    recordGapCenter + 598358 = fullRecordGapValue09955 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09955_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09955 (fullRecordGapValue09955 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09955_not_prime : ¬(recordGapCenter + 598358).Prime := by
  rw [fullRecordGapTerm09955_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09955, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09955_fast_pow_mod_ne_one

def fullRecordGapValue09956 : Nat := fullRecordGapCenterValue + 598398

theorem fullRecordGapTerm09956_eq_value :
    recordGapCenter + 598398 = fullRecordGapValue09956 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09956_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09956 (fullRecordGapValue09956 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09956_not_prime : ¬(recordGapCenter + 598398).Prime := by
  rw [fullRecordGapTerm09956_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09956, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09956_fast_pow_mod_ne_one

def fullRecordGapValue09957 : Nat := fullRecordGapCenterValue + 598412

theorem fullRecordGapTerm09957_eq_value :
    recordGapCenter + 598412 = fullRecordGapValue09957 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09957_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09957 (fullRecordGapValue09957 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09957_not_prime : ¬(recordGapCenter + 598412).Prime := by
  rw [fullRecordGapTerm09957_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09957, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09957_fast_pow_mod_ne_one

def fullRecordGapValue09958 : Nat := fullRecordGapCenterValue + 598508

theorem fullRecordGapTerm09958_eq_value :
    recordGapCenter + 598508 = fullRecordGapValue09958 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09958_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09958 (fullRecordGapValue09958 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09958_not_prime : ¬(recordGapCenter + 598508).Prime := by
  rw [fullRecordGapTerm09958_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09958, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09958_fast_pow_mod_ne_one

def fullRecordGapValue09959 : Nat := fullRecordGapCenterValue + 598568

theorem fullRecordGapTerm09959_eq_value :
    recordGapCenter + 598568 = fullRecordGapValue09959 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09959_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09959 (fullRecordGapValue09959 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09959_not_prime : ¬(recordGapCenter + 598568).Prime := by
  rw [fullRecordGapTerm09959_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09959, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09959_fast_pow_mod_ne_one

def fullRecordGapValue09960 : Nat := fullRecordGapCenterValue + 598622

theorem fullRecordGapTerm09960_eq_value :
    recordGapCenter + 598622 = fullRecordGapValue09960 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09960_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09960 (fullRecordGapValue09960 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09960_not_prime : ¬(recordGapCenter + 598622).Prime := by
  rw [fullRecordGapTerm09960_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09960, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09960_fast_pow_mod_ne_one

def fullRecordGapValue09961 : Nat := fullRecordGapCenterValue + 598692

theorem fullRecordGapTerm09961_eq_value :
    recordGapCenter + 598692 = fullRecordGapValue09961 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09961_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09961 (fullRecordGapValue09961 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09961_not_prime : ¬(recordGapCenter + 598692).Prime := by
  rw [fullRecordGapTerm09961_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09961, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09961_fast_pow_mod_ne_one

def fullRecordGapValue09962 : Nat := fullRecordGapCenterValue + 598790

theorem fullRecordGapTerm09962_eq_value :
    recordGapCenter + 598790 = fullRecordGapValue09962 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09962_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09962 (fullRecordGapValue09962 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09962_not_prime : ¬(recordGapCenter + 598790).Prime := by
  rw [fullRecordGapTerm09962_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09962, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09962_fast_pow_mod_ne_one

def fullRecordGapValue09963 : Nat := fullRecordGapCenterValue + 598868

theorem fullRecordGapTerm09963_eq_value :
    recordGapCenter + 598868 = fullRecordGapValue09963 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09963_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09963 (fullRecordGapValue09963 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09963_not_prime : ¬(recordGapCenter + 598868).Prime := by
  rw [fullRecordGapTerm09963_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09963, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09963_fast_pow_mod_ne_one

def fullRecordGapValue09964 : Nat := fullRecordGapCenterValue + 598916

theorem fullRecordGapTerm09964_eq_value :
    recordGapCenter + 598916 = fullRecordGapValue09964 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09964_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09964 (fullRecordGapValue09964 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09964_not_prime : ¬(recordGapCenter + 598916).Prime := by
  rw [fullRecordGapTerm09964_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09964, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09964_fast_pow_mod_ne_one

def fullRecordGapValue09965 : Nat := fullRecordGapCenterValue + 598938

theorem fullRecordGapTerm09965_eq_value :
    recordGapCenter + 598938 = fullRecordGapValue09965 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09965_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09965 (fullRecordGapValue09965 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09965_not_prime : ¬(recordGapCenter + 598938).Prime := by
  rw [fullRecordGapTerm09965_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09965, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09965_fast_pow_mod_ne_one

def fullRecordGapValue09966 : Nat := fullRecordGapCenterValue + 598950

theorem fullRecordGapTerm09966_eq_value :
    recordGapCenter + 598950 = fullRecordGapValue09966 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09966_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09966 (fullRecordGapValue09966 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09966_not_prime : ¬(recordGapCenter + 598950).Prime := by
  rw [fullRecordGapTerm09966_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09966, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09966_fast_pow_mod_ne_one

def fullRecordGapValue09967 : Nat := fullRecordGapCenterValue + 599036

theorem fullRecordGapTerm09967_eq_value :
    recordGapCenter + 599036 = fullRecordGapValue09967 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09967_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09967 (fullRecordGapValue09967 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09967_not_prime : ¬(recordGapCenter + 599036).Prime := by
  rw [fullRecordGapTerm09967_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09967, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09967_fast_pow_mod_ne_one

def fullRecordGapValue09968 : Nat := fullRecordGapCenterValue + 599042

theorem fullRecordGapTerm09968_eq_value :
    recordGapCenter + 599042 = fullRecordGapValue09968 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09968_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09968 (fullRecordGapValue09968 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09968_not_prime : ¬(recordGapCenter + 599042).Prime := by
  rw [fullRecordGapTerm09968_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09968, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09968_fast_pow_mod_ne_one

def fullRecordGapValue09969 : Nat := fullRecordGapCenterValue + 599096

theorem fullRecordGapTerm09969_eq_value :
    recordGapCenter + 599096 = fullRecordGapValue09969 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09969_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09969 (fullRecordGapValue09969 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09969_not_prime : ¬(recordGapCenter + 599096).Prime := by
  rw [fullRecordGapTerm09969_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09969, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09969_fast_pow_mod_ne_one

def fullRecordGapValue09970 : Nat := fullRecordGapCenterValue + 599226

theorem fullRecordGapTerm09970_eq_value :
    recordGapCenter + 599226 = fullRecordGapValue09970 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09970_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09970 (fullRecordGapValue09970 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09970_not_prime : ¬(recordGapCenter + 599226).Prime := by
  rw [fullRecordGapTerm09970_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09970, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09970_fast_pow_mod_ne_one

def fullRecordGapValue09971 : Nat := fullRecordGapCenterValue + 599246

theorem fullRecordGapTerm09971_eq_value :
    recordGapCenter + 599246 = fullRecordGapValue09971 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09971_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09971 (fullRecordGapValue09971 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09971_not_prime : ¬(recordGapCenter + 599246).Prime := by
  rw [fullRecordGapTerm09971_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09971, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09971_fast_pow_mod_ne_one

def fullRecordGapValue09972 : Nat := fullRecordGapCenterValue + 599316

theorem fullRecordGapTerm09972_eq_value :
    recordGapCenter + 599316 = fullRecordGapValue09972 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09972_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09972 (fullRecordGapValue09972 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09972_not_prime : ¬(recordGapCenter + 599316).Prime := by
  rw [fullRecordGapTerm09972_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09972, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09972_fast_pow_mod_ne_one

def fullRecordGapValue09973 : Nat := fullRecordGapCenterValue + 599348

theorem fullRecordGapTerm09973_eq_value :
    recordGapCenter + 599348 = fullRecordGapValue09973 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09973_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09973 (fullRecordGapValue09973 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09973_not_prime : ¬(recordGapCenter + 599348).Prime := by
  rw [fullRecordGapTerm09973_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09973, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09973_fast_pow_mod_ne_one

def fullRecordGapValue09974 : Nat := fullRecordGapCenterValue + 599432

theorem fullRecordGapTerm09974_eq_value :
    recordGapCenter + 599432 = fullRecordGapValue09974 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09974_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09974 (fullRecordGapValue09974 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09974_not_prime : ¬(recordGapCenter + 599432).Prime := by
  rw [fullRecordGapTerm09974_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09974, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09974_fast_pow_mod_ne_one

def fullRecordGapValue09975 : Nat := fullRecordGapCenterValue + 599462

theorem fullRecordGapTerm09975_eq_value :
    recordGapCenter + 599462 = fullRecordGapValue09975 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09975_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09975 (fullRecordGapValue09975 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09975_not_prime : ¬(recordGapCenter + 599462).Prime := by
  rw [fullRecordGapTerm09975_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09975, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09975_fast_pow_mod_ne_one

def fullRecordGapValue09976 : Nat := fullRecordGapCenterValue + 599468

theorem fullRecordGapTerm09976_eq_value :
    recordGapCenter + 599468 = fullRecordGapValue09976 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09976_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09976 (fullRecordGapValue09976 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09976_not_prime : ¬(recordGapCenter + 599468).Prime := by
  rw [fullRecordGapTerm09976_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09976, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09976_fast_pow_mod_ne_one

def fullRecordGapValue09977 : Nat := fullRecordGapCenterValue + 599510

theorem fullRecordGapTerm09977_eq_value :
    recordGapCenter + 599510 = fullRecordGapValue09977 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09977_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09977 (fullRecordGapValue09977 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09977_not_prime : ¬(recordGapCenter + 599510).Prime := by
  rw [fullRecordGapTerm09977_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09977, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09977_fast_pow_mod_ne_one

def fullRecordGapValue09978 : Nat := fullRecordGapCenterValue + 599810

theorem fullRecordGapTerm09978_eq_value :
    recordGapCenter + 599810 = fullRecordGapValue09978 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09978_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09978 (fullRecordGapValue09978 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09978_not_prime : ¬(recordGapCenter + 599810).Prime := by
  rw [fullRecordGapTerm09978_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09978, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09978_fast_pow_mod_ne_one

def fullRecordGapValue09979 : Nat := fullRecordGapCenterValue + 599988

theorem fullRecordGapTerm09979_eq_value :
    recordGapCenter + 599988 = fullRecordGapValue09979 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09979_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09979 (fullRecordGapValue09979 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09979_not_prime : ¬(recordGapCenter + 599988).Prime := by
  rw [fullRecordGapTerm09979_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09979, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09979_fast_pow_mod_ne_one

def fullRecordGapValue09980 : Nat := fullRecordGapCenterValue + 600000

theorem fullRecordGapTerm09980_eq_value :
    recordGapCenter + 600000 = fullRecordGapValue09980 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09980_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09980 (fullRecordGapValue09980 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09980_not_prime : ¬(recordGapCenter + 600000).Prime := by
  rw [fullRecordGapTerm09980_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09980, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09980_fast_pow_mod_ne_one

def fullRecordGapValue09981 : Nat := fullRecordGapCenterValue + 600170

theorem fullRecordGapTerm09981_eq_value :
    recordGapCenter + 600170 = fullRecordGapValue09981 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09981_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09981 (fullRecordGapValue09981 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09981_not_prime : ¬(recordGapCenter + 600170).Prime := by
  rw [fullRecordGapTerm09981_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09981, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09981_fast_pow_mod_ne_one

def fullRecordGapValue09982 : Nat := fullRecordGapCenterValue + 600252

theorem fullRecordGapTerm09982_eq_value :
    recordGapCenter + 600252 = fullRecordGapValue09982 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09982_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09982 (fullRecordGapValue09982 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09982_not_prime : ¬(recordGapCenter + 600252).Prime := by
  rw [fullRecordGapTerm09982_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09982, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09982_fast_pow_mod_ne_one

def fullRecordGapValue09983 : Nat := fullRecordGapCenterValue + 600258

theorem fullRecordGapTerm09983_eq_value :
    recordGapCenter + 600258 = fullRecordGapValue09983 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09983_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09983 (fullRecordGapValue09983 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09983_not_prime : ¬(recordGapCenter + 600258).Prime := by
  rw [fullRecordGapTerm09983_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09983, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09983_fast_pow_mod_ne_one

def fullRecordGapValue09984 : Nat := fullRecordGapCenterValue + 600276

theorem fullRecordGapTerm09984_eq_value :
    recordGapCenter + 600276 = fullRecordGapValue09984 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09984_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09984 (fullRecordGapValue09984 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09984_not_prime : ¬(recordGapCenter + 600276).Prime := by
  rw [fullRecordGapTerm09984_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09984, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09984_fast_pow_mod_ne_one

end PrimeFactorUnimodality
