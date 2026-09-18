import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue02817 : Nat := fullRecordGapCenterValue - 205222

theorem fullRecordGapTerm02817_eq_value :
    recordGapCenter - 205222 = fullRecordGapValue02817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02817 (fullRecordGapValue02817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02817_not_prime : ¬(recordGapCenter - 205222).Prime := by
  rw [fullRecordGapTerm02817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02817_fast_pow_mod_ne_one

def fullRecordGapValue02818 : Nat := fullRecordGapCenterValue - 205174

theorem fullRecordGapTerm02818_eq_value :
    recordGapCenter - 205174 = fullRecordGapValue02818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02818 (fullRecordGapValue02818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02818_not_prime : ¬(recordGapCenter - 205174).Prime := by
  rw [fullRecordGapTerm02818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02818_fast_pow_mod_ne_one

def fullRecordGapValue02819 : Nat := fullRecordGapCenterValue - 204994

theorem fullRecordGapTerm02819_eq_value :
    recordGapCenter - 204994 = fullRecordGapValue02819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02819 (fullRecordGapValue02819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02819_not_prime : ¬(recordGapCenter - 204994).Prime := by
  rw [fullRecordGapTerm02819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02819_fast_pow_mod_ne_one

def fullRecordGapValue02820 : Nat := fullRecordGapCenterValue - 204658

theorem fullRecordGapTerm02820_eq_value :
    recordGapCenter - 204658 = fullRecordGapValue02820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02820 (fullRecordGapValue02820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02820_not_prime : ¬(recordGapCenter - 204658).Prime := by
  rw [fullRecordGapTerm02820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02820_fast_pow_mod_ne_one

def fullRecordGapValue02821 : Nat := fullRecordGapCenterValue - 204634

theorem fullRecordGapTerm02821_eq_value :
    recordGapCenter - 204634 = fullRecordGapValue02821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02821 (fullRecordGapValue02821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02821_not_prime : ¬(recordGapCenter - 204634).Prime := by
  rw [fullRecordGapTerm02821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02821_fast_pow_mod_ne_one

def fullRecordGapValue02822 : Nat := fullRecordGapCenterValue - 204298

theorem fullRecordGapTerm02822_eq_value :
    recordGapCenter - 204298 = fullRecordGapValue02822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02822 (fullRecordGapValue02822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02822_not_prime : ¬(recordGapCenter - 204298).Prime := by
  rw [fullRecordGapTerm02822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02822_fast_pow_mod_ne_one

def fullRecordGapValue02823 : Nat := fullRecordGapCenterValue - 204214

theorem fullRecordGapTerm02823_eq_value :
    recordGapCenter - 204214 = fullRecordGapValue02823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02823 (fullRecordGapValue02823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02823_not_prime : ¬(recordGapCenter - 204214).Prime := by
  rw [fullRecordGapTerm02823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02823_fast_pow_mod_ne_one

def fullRecordGapValue02824 : Nat := fullRecordGapCenterValue - 204154

theorem fullRecordGapTerm02824_eq_value :
    recordGapCenter - 204154 = fullRecordGapValue02824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02824 (fullRecordGapValue02824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02824_not_prime : ¬(recordGapCenter - 204154).Prime := by
  rw [fullRecordGapTerm02824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02824_fast_pow_mod_ne_one

def fullRecordGapValue02825 : Nat := fullRecordGapCenterValue - 203758

theorem fullRecordGapTerm02825_eq_value :
    recordGapCenter - 203758 = fullRecordGapValue02825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02825 (fullRecordGapValue02825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02825_not_prime : ¬(recordGapCenter - 203758).Prime := by
  rw [fullRecordGapTerm02825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02825_fast_pow_mod_ne_one

def fullRecordGapValue02826 : Nat := fullRecordGapCenterValue - 203742

theorem fullRecordGapTerm02826_eq_value :
    recordGapCenter - 203742 = fullRecordGapValue02826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02826 (fullRecordGapValue02826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02826_not_prime : ¬(recordGapCenter - 203742).Prime := by
  rw [fullRecordGapTerm02826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02826_fast_pow_mod_ne_one

def fullRecordGapValue02827 : Nat := fullRecordGapCenterValue - 203254

theorem fullRecordGapTerm02827_eq_value :
    recordGapCenter - 203254 = fullRecordGapValue02827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02827 (fullRecordGapValue02827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02827_not_prime : ¬(recordGapCenter - 203254).Prime := by
  rw [fullRecordGapTerm02827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02827_fast_pow_mod_ne_one

def fullRecordGapValue02828 : Nat := fullRecordGapCenterValue - 203074

theorem fullRecordGapTerm02828_eq_value :
    recordGapCenter - 203074 = fullRecordGapValue02828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02828 (fullRecordGapValue02828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02828_not_prime : ¬(recordGapCenter - 203074).Prime := by
  rw [fullRecordGapTerm02828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02828_fast_pow_mod_ne_one

def fullRecordGapValue02829 : Nat := fullRecordGapCenterValue - 203068

theorem fullRecordGapTerm02829_eq_value :
    recordGapCenter - 203068 = fullRecordGapValue02829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02829 (fullRecordGapValue02829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02829_not_prime : ¬(recordGapCenter - 203068).Prime := by
  rw [fullRecordGapTerm02829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02829_fast_pow_mod_ne_one

def fullRecordGapValue02830 : Nat := fullRecordGapCenterValue - 203062

theorem fullRecordGapTerm02830_eq_value :
    recordGapCenter - 203062 = fullRecordGapValue02830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02830 (fullRecordGapValue02830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02830_not_prime : ¬(recordGapCenter - 203062).Prime := by
  rw [fullRecordGapTerm02830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02830_fast_pow_mod_ne_one

def fullRecordGapValue02831 : Nat := fullRecordGapCenterValue - 202858

theorem fullRecordGapTerm02831_eq_value :
    recordGapCenter - 202858 = fullRecordGapValue02831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02831 (fullRecordGapValue02831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02831_not_prime : ¬(recordGapCenter - 202858).Prime := by
  rw [fullRecordGapTerm02831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02831_fast_pow_mod_ne_one

def fullRecordGapValue02832 : Nat := fullRecordGapCenterValue - 202828

theorem fullRecordGapTerm02832_eq_value :
    recordGapCenter - 202828 = fullRecordGapValue02832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02832 (fullRecordGapValue02832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02832_not_prime : ¬(recordGapCenter - 202828).Prime := by
  rw [fullRecordGapTerm02832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02832_fast_pow_mod_ne_one

def fullRecordGapValue02833 : Nat := fullRecordGapCenterValue - 202534

theorem fullRecordGapTerm02833_eq_value :
    recordGapCenter - 202534 = fullRecordGapValue02833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02833 (fullRecordGapValue02833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02833_not_prime : ¬(recordGapCenter - 202534).Prime := by
  rw [fullRecordGapTerm02833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02833_fast_pow_mod_ne_one

def fullRecordGapValue02834 : Nat := fullRecordGapCenterValue - 202348

theorem fullRecordGapTerm02834_eq_value :
    recordGapCenter - 202348 = fullRecordGapValue02834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02834 (fullRecordGapValue02834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02834_not_prime : ¬(recordGapCenter - 202348).Prime := by
  rw [fullRecordGapTerm02834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02834_fast_pow_mod_ne_one

def fullRecordGapValue02835 : Nat := fullRecordGapCenterValue - 202324

theorem fullRecordGapTerm02835_eq_value :
    recordGapCenter - 202324 = fullRecordGapValue02835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02835 (fullRecordGapValue02835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02835_not_prime : ¬(recordGapCenter - 202324).Prime := by
  rw [fullRecordGapTerm02835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02835_fast_pow_mod_ne_one

def fullRecordGapValue02836 : Nat := fullRecordGapCenterValue - 202222

theorem fullRecordGapTerm02836_eq_value :
    recordGapCenter - 202222 = fullRecordGapValue02836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02836 (fullRecordGapValue02836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02836_not_prime : ¬(recordGapCenter - 202222).Prime := by
  rw [fullRecordGapTerm02836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02836_fast_pow_mod_ne_one

def fullRecordGapValue02837 : Nat := fullRecordGapCenterValue - 202012

theorem fullRecordGapTerm02837_eq_value :
    recordGapCenter - 202012 = fullRecordGapValue02837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02837 (fullRecordGapValue02837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02837_not_prime : ¬(recordGapCenter - 202012).Prime := by
  rw [fullRecordGapTerm02837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02837_fast_pow_mod_ne_one

def fullRecordGapValue02838 : Nat := fullRecordGapCenterValue - 201988

theorem fullRecordGapTerm02838_eq_value :
    recordGapCenter - 201988 = fullRecordGapValue02838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02838 (fullRecordGapValue02838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02838_not_prime : ¬(recordGapCenter - 201988).Prime := by
  rw [fullRecordGapTerm02838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02838_fast_pow_mod_ne_one

def fullRecordGapValue02839 : Nat := fullRecordGapCenterValue - 201862

theorem fullRecordGapTerm02839_eq_value :
    recordGapCenter - 201862 = fullRecordGapValue02839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02839 (fullRecordGapValue02839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02839_not_prime : ¬(recordGapCenter - 201862).Prime := by
  rw [fullRecordGapTerm02839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02839_fast_pow_mod_ne_one

def fullRecordGapValue02840 : Nat := fullRecordGapCenterValue - 201814

theorem fullRecordGapTerm02840_eq_value :
    recordGapCenter - 201814 = fullRecordGapValue02840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02840 (fullRecordGapValue02840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02840_not_prime : ¬(recordGapCenter - 201814).Prime := by
  rw [fullRecordGapTerm02840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02840_fast_pow_mod_ne_one

def fullRecordGapValue02841 : Nat := fullRecordGapCenterValue - 201694

theorem fullRecordGapTerm02841_eq_value :
    recordGapCenter - 201694 = fullRecordGapValue02841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02841 (fullRecordGapValue02841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02841_not_prime : ¬(recordGapCenter - 201694).Prime := by
  rw [fullRecordGapTerm02841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02841_fast_pow_mod_ne_one

def fullRecordGapValue02842 : Nat := fullRecordGapCenterValue - 201532

theorem fullRecordGapTerm02842_eq_value :
    recordGapCenter - 201532 = fullRecordGapValue02842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02842 (fullRecordGapValue02842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02842_not_prime : ¬(recordGapCenter - 201532).Prime := by
  rw [fullRecordGapTerm02842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02842_fast_pow_mod_ne_one

def fullRecordGapValue02843 : Nat := fullRecordGapCenterValue - 201364

theorem fullRecordGapTerm02843_eq_value :
    recordGapCenter - 201364 = fullRecordGapValue02843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02843 (fullRecordGapValue02843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02843_not_prime : ¬(recordGapCenter - 201364).Prime := by
  rw [fullRecordGapTerm02843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02843_fast_pow_mod_ne_one

def fullRecordGapValue02844 : Nat := fullRecordGapCenterValue - 201298

theorem fullRecordGapTerm02844_eq_value :
    recordGapCenter - 201298 = fullRecordGapValue02844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02844 (fullRecordGapValue02844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02844_not_prime : ¬(recordGapCenter - 201298).Prime := by
  rw [fullRecordGapTerm02844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02844_fast_pow_mod_ne_one

def fullRecordGapValue02845 : Nat := fullRecordGapCenterValue - 200542

theorem fullRecordGapTerm02845_eq_value :
    recordGapCenter - 200542 = fullRecordGapValue02845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02845 (fullRecordGapValue02845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02845_not_prime : ¬(recordGapCenter - 200542).Prime := by
  rw [fullRecordGapTerm02845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02845_fast_pow_mod_ne_one

def fullRecordGapValue02846 : Nat := fullRecordGapCenterValue - 200338

theorem fullRecordGapTerm02846_eq_value :
    recordGapCenter - 200338 = fullRecordGapValue02846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02846 (fullRecordGapValue02846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02846_not_prime : ¬(recordGapCenter - 200338).Prime := by
  rw [fullRecordGapTerm02846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02846_fast_pow_mod_ne_one

def fullRecordGapValue02847 : Nat := fullRecordGapCenterValue - 200218

theorem fullRecordGapTerm02847_eq_value :
    recordGapCenter - 200218 = fullRecordGapValue02847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02847 (fullRecordGapValue02847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02847_not_prime : ¬(recordGapCenter - 200218).Prime := by
  rw [fullRecordGapTerm02847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02847_fast_pow_mod_ne_one

def fullRecordGapValue02848 : Nat := fullRecordGapCenterValue - 200212

theorem fullRecordGapTerm02848_eq_value :
    recordGapCenter - 200212 = fullRecordGapValue02848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02848 (fullRecordGapValue02848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02848_not_prime : ¬(recordGapCenter - 200212).Prime := by
  rw [fullRecordGapTerm02848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02848_fast_pow_mod_ne_one

def fullRecordGapValue02849 : Nat := fullRecordGapCenterValue - 199978

theorem fullRecordGapTerm02849_eq_value :
    recordGapCenter - 199978 = fullRecordGapValue02849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02849 (fullRecordGapValue02849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02849_not_prime : ¬(recordGapCenter - 199978).Prime := by
  rw [fullRecordGapTerm02849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02849_fast_pow_mod_ne_one

def fullRecordGapValue02850 : Nat := fullRecordGapCenterValue - 199650

theorem fullRecordGapTerm02850_eq_value :
    recordGapCenter - 199650 = fullRecordGapValue02850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02850 (fullRecordGapValue02850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02850_not_prime : ¬(recordGapCenter - 199650).Prime := by
  rw [fullRecordGapTerm02850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02850_fast_pow_mod_ne_one

def fullRecordGapValue02851 : Nat := fullRecordGapCenterValue - 199414

theorem fullRecordGapTerm02851_eq_value :
    recordGapCenter - 199414 = fullRecordGapValue02851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02851 (fullRecordGapValue02851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02851_not_prime : ¬(recordGapCenter - 199414).Prime := by
  rw [fullRecordGapTerm02851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02851_fast_pow_mod_ne_one

def fullRecordGapValue02852 : Nat := fullRecordGapCenterValue - 199204

theorem fullRecordGapTerm02852_eq_value :
    recordGapCenter - 199204 = fullRecordGapValue02852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02852 (fullRecordGapValue02852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02852_not_prime : ¬(recordGapCenter - 199204).Prime := by
  rw [fullRecordGapTerm02852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02852_fast_pow_mod_ne_one

def fullRecordGapValue02853 : Nat := fullRecordGapCenterValue - 198988

theorem fullRecordGapTerm02853_eq_value :
    recordGapCenter - 198988 = fullRecordGapValue02853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02853 (fullRecordGapValue02853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02853_not_prime : ¬(recordGapCenter - 198988).Prime := by
  rw [fullRecordGapTerm02853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02853_fast_pow_mod_ne_one

def fullRecordGapValue02854 : Nat := fullRecordGapCenterValue - 198844

theorem fullRecordGapTerm02854_eq_value :
    recordGapCenter - 198844 = fullRecordGapValue02854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02854 (fullRecordGapValue02854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02854_not_prime : ¬(recordGapCenter - 198844).Prime := by
  rw [fullRecordGapTerm02854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02854_fast_pow_mod_ne_one

def fullRecordGapValue02855 : Nat := fullRecordGapCenterValue - 198742

theorem fullRecordGapTerm02855_eq_value :
    recordGapCenter - 198742 = fullRecordGapValue02855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02855 (fullRecordGapValue02855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02855_not_prime : ¬(recordGapCenter - 198742).Prime := by
  rw [fullRecordGapTerm02855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02855_fast_pow_mod_ne_one

def fullRecordGapValue02856 : Nat := fullRecordGapCenterValue - 198634

theorem fullRecordGapTerm02856_eq_value :
    recordGapCenter - 198634 = fullRecordGapValue02856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02856 (fullRecordGapValue02856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02856_not_prime : ¬(recordGapCenter - 198634).Prime := by
  rw [fullRecordGapTerm02856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02856_fast_pow_mod_ne_one

def fullRecordGapValue02857 : Nat := fullRecordGapCenterValue - 198508

theorem fullRecordGapTerm02857_eq_value :
    recordGapCenter - 198508 = fullRecordGapValue02857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02857 (fullRecordGapValue02857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02857_not_prime : ¬(recordGapCenter - 198508).Prime := by
  rw [fullRecordGapTerm02857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02857_fast_pow_mod_ne_one

def fullRecordGapValue02858 : Nat := fullRecordGapCenterValue - 198382

theorem fullRecordGapTerm02858_eq_value :
    recordGapCenter - 198382 = fullRecordGapValue02858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02858 (fullRecordGapValue02858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02858_not_prime : ¬(recordGapCenter - 198382).Prime := by
  rw [fullRecordGapTerm02858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02858_fast_pow_mod_ne_one

def fullRecordGapValue02859 : Nat := fullRecordGapCenterValue - 198274

theorem fullRecordGapTerm02859_eq_value :
    recordGapCenter - 198274 = fullRecordGapValue02859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02859 (fullRecordGapValue02859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02859_not_prime : ¬(recordGapCenter - 198274).Prime := by
  rw [fullRecordGapTerm02859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02859_fast_pow_mod_ne_one

def fullRecordGapValue02860 : Nat := fullRecordGapCenterValue - 198238

theorem fullRecordGapTerm02860_eq_value :
    recordGapCenter - 198238 = fullRecordGapValue02860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02860 (fullRecordGapValue02860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02860_not_prime : ¬(recordGapCenter - 198238).Prime := by
  rw [fullRecordGapTerm02860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02860_fast_pow_mod_ne_one

def fullRecordGapValue02861 : Nat := fullRecordGapCenterValue - 198148

theorem fullRecordGapTerm02861_eq_value :
    recordGapCenter - 198148 = fullRecordGapValue02861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02861 (fullRecordGapValue02861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02861_not_prime : ¬(recordGapCenter - 198148).Prime := by
  rw [fullRecordGapTerm02861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02861_fast_pow_mod_ne_one

def fullRecordGapValue02862 : Nat := fullRecordGapCenterValue - 198082

theorem fullRecordGapTerm02862_eq_value :
    recordGapCenter - 198082 = fullRecordGapValue02862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02862 (fullRecordGapValue02862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02862_not_prime : ¬(recordGapCenter - 198082).Prime := by
  rw [fullRecordGapTerm02862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02862_fast_pow_mod_ne_one

def fullRecordGapValue02863 : Nat := fullRecordGapCenterValue - 198034

theorem fullRecordGapTerm02863_eq_value :
    recordGapCenter - 198034 = fullRecordGapValue02863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02863 (fullRecordGapValue02863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02863_not_prime : ¬(recordGapCenter - 198034).Prime := by
  rw [fullRecordGapTerm02863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02863_fast_pow_mod_ne_one

def fullRecordGapValue02864 : Nat := fullRecordGapCenterValue - 197908

theorem fullRecordGapTerm02864_eq_value :
    recordGapCenter - 197908 = fullRecordGapValue02864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02864 (fullRecordGapValue02864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02864_not_prime : ¬(recordGapCenter - 197908).Prime := by
  rw [fullRecordGapTerm02864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02864_fast_pow_mod_ne_one

def fullRecordGapValue02865 : Nat := fullRecordGapCenterValue - 197878

theorem fullRecordGapTerm02865_eq_value :
    recordGapCenter - 197878 = fullRecordGapValue02865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02865 (fullRecordGapValue02865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02865_not_prime : ¬(recordGapCenter - 197878).Prime := by
  rw [fullRecordGapTerm02865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02865_fast_pow_mod_ne_one

def fullRecordGapValue02866 : Nat := fullRecordGapCenterValue - 197854

theorem fullRecordGapTerm02866_eq_value :
    recordGapCenter - 197854 = fullRecordGapValue02866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02866 (fullRecordGapValue02866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02866_not_prime : ¬(recordGapCenter - 197854).Prime := by
  rw [fullRecordGapTerm02866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02866_fast_pow_mod_ne_one

def fullRecordGapValue02867 : Nat := fullRecordGapCenterValue - 197818

theorem fullRecordGapTerm02867_eq_value :
    recordGapCenter - 197818 = fullRecordGapValue02867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02867 (fullRecordGapValue02867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02867_not_prime : ¬(recordGapCenter - 197818).Prime := by
  rw [fullRecordGapTerm02867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02867_fast_pow_mod_ne_one

def fullRecordGapValue02868 : Nat := fullRecordGapCenterValue - 197734

theorem fullRecordGapTerm02868_eq_value :
    recordGapCenter - 197734 = fullRecordGapValue02868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02868 (fullRecordGapValue02868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02868_not_prime : ¬(recordGapCenter - 197734).Prime := by
  rw [fullRecordGapTerm02868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02868_fast_pow_mod_ne_one

def fullRecordGapValue02869 : Nat := fullRecordGapCenterValue - 197668

theorem fullRecordGapTerm02869_eq_value :
    recordGapCenter - 197668 = fullRecordGapValue02869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02869 (fullRecordGapValue02869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02869_not_prime : ¬(recordGapCenter - 197668).Prime := by
  rw [fullRecordGapTerm02869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02869_fast_pow_mod_ne_one

def fullRecordGapValue02870 : Nat := fullRecordGapCenterValue - 197644

theorem fullRecordGapTerm02870_eq_value :
    recordGapCenter - 197644 = fullRecordGapValue02870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02870 (fullRecordGapValue02870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02870_not_prime : ¬(recordGapCenter - 197644).Prime := by
  rw [fullRecordGapTerm02870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02870_fast_pow_mod_ne_one

def fullRecordGapValue02871 : Nat := fullRecordGapCenterValue - 197614

theorem fullRecordGapTerm02871_eq_value :
    recordGapCenter - 197614 = fullRecordGapValue02871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02871 (fullRecordGapValue02871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02871_not_prime : ¬(recordGapCenter - 197614).Prime := by
  rw [fullRecordGapTerm02871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02871_fast_pow_mod_ne_one

def fullRecordGapValue02872 : Nat := fullRecordGapCenterValue - 197602

theorem fullRecordGapTerm02872_eq_value :
    recordGapCenter - 197602 = fullRecordGapValue02872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02872 (fullRecordGapValue02872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02872_not_prime : ¬(recordGapCenter - 197602).Prime := by
  rw [fullRecordGapTerm02872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02872_fast_pow_mod_ne_one

def fullRecordGapValue02873 : Nat := fullRecordGapCenterValue - 197452

theorem fullRecordGapTerm02873_eq_value :
    recordGapCenter - 197452 = fullRecordGapValue02873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02873 (fullRecordGapValue02873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02873_not_prime : ¬(recordGapCenter - 197452).Prime := by
  rw [fullRecordGapTerm02873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02873_fast_pow_mod_ne_one

def fullRecordGapValue02874 : Nat := fullRecordGapCenterValue - 197332

theorem fullRecordGapTerm02874_eq_value :
    recordGapCenter - 197332 = fullRecordGapValue02874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02874 (fullRecordGapValue02874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02874_not_prime : ¬(recordGapCenter - 197332).Prime := by
  rw [fullRecordGapTerm02874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02874_fast_pow_mod_ne_one

def fullRecordGapValue02875 : Nat := fullRecordGapCenterValue - 197194

theorem fullRecordGapTerm02875_eq_value :
    recordGapCenter - 197194 = fullRecordGapValue02875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02875 (fullRecordGapValue02875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02875_not_prime : ¬(recordGapCenter - 197194).Prime := by
  rw [fullRecordGapTerm02875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02875_fast_pow_mod_ne_one

def fullRecordGapValue02876 : Nat := fullRecordGapCenterValue - 197188

theorem fullRecordGapTerm02876_eq_value :
    recordGapCenter - 197188 = fullRecordGapValue02876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02876 (fullRecordGapValue02876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02876_not_prime : ¬(recordGapCenter - 197188).Prime := by
  rw [fullRecordGapTerm02876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02876_fast_pow_mod_ne_one

def fullRecordGapValue02877 : Nat := fullRecordGapCenterValue - 197122

theorem fullRecordGapTerm02877_eq_value :
    recordGapCenter - 197122 = fullRecordGapValue02877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02877 (fullRecordGapValue02877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02877_not_prime : ¬(recordGapCenter - 197122).Prime := by
  rw [fullRecordGapTerm02877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02877_fast_pow_mod_ne_one

def fullRecordGapValue02878 : Nat := fullRecordGapCenterValue - 196858

theorem fullRecordGapTerm02878_eq_value :
    recordGapCenter - 196858 = fullRecordGapValue02878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02878 (fullRecordGapValue02878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02878_not_prime : ¬(recordGapCenter - 196858).Prime := by
  rw [fullRecordGapTerm02878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02878_fast_pow_mod_ne_one

def fullRecordGapValue02879 : Nat := fullRecordGapCenterValue - 196830

theorem fullRecordGapTerm02879_eq_value :
    recordGapCenter - 196830 = fullRecordGapValue02879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02879 (fullRecordGapValue02879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02879_not_prime : ¬(recordGapCenter - 196830).Prime := by
  rw [fullRecordGapTerm02879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02879_fast_pow_mod_ne_one

def fullRecordGapValue02880 : Nat := fullRecordGapCenterValue - 196828

theorem fullRecordGapTerm02880_eq_value :
    recordGapCenter - 196828 = fullRecordGapValue02880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02880 (fullRecordGapValue02880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02880_not_prime : ¬(recordGapCenter - 196828).Prime := by
  rw [fullRecordGapTerm02880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02880_fast_pow_mod_ne_one

def fullRecordGapValue02881 : Nat := fullRecordGapCenterValue - 196804

theorem fullRecordGapTerm02881_eq_value :
    recordGapCenter - 196804 = fullRecordGapValue02881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02881 (fullRecordGapValue02881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02881_not_prime : ¬(recordGapCenter - 196804).Prime := by
  rw [fullRecordGapTerm02881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02881_fast_pow_mod_ne_one

def fullRecordGapValue02882 : Nat := fullRecordGapCenterValue - 196774

theorem fullRecordGapTerm02882_eq_value :
    recordGapCenter - 196774 = fullRecordGapValue02882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02882 (fullRecordGapValue02882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02882_not_prime : ¬(recordGapCenter - 196774).Prime := by
  rw [fullRecordGapTerm02882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02882_fast_pow_mod_ne_one

def fullRecordGapValue02883 : Nat := fullRecordGapCenterValue - 196738

theorem fullRecordGapTerm02883_eq_value :
    recordGapCenter - 196738 = fullRecordGapValue02883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02883 (fullRecordGapValue02883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02883_not_prime : ¬(recordGapCenter - 196738).Prime := by
  rw [fullRecordGapTerm02883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02883_fast_pow_mod_ne_one

def fullRecordGapValue02884 : Nat := fullRecordGapCenterValue - 196608

theorem fullRecordGapTerm02884_eq_value :
    recordGapCenter - 196608 = fullRecordGapValue02884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02884 (fullRecordGapValue02884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02884_not_prime : ¬(recordGapCenter - 196608).Prime := by
  rw [fullRecordGapTerm02884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02884_fast_pow_mod_ne_one

def fullRecordGapValue02885 : Nat := fullRecordGapCenterValue - 196468

theorem fullRecordGapTerm02885_eq_value :
    recordGapCenter - 196468 = fullRecordGapValue02885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02885 (fullRecordGapValue02885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02885_not_prime : ¬(recordGapCenter - 196468).Prime := by
  rw [fullRecordGapTerm02885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02885_fast_pow_mod_ne_one

def fullRecordGapValue02886 : Nat := fullRecordGapCenterValue - 196132

theorem fullRecordGapTerm02886_eq_value :
    recordGapCenter - 196132 = fullRecordGapValue02886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02886 (fullRecordGapValue02886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02886_not_prime : ¬(recordGapCenter - 196132).Prime := by
  rw [fullRecordGapTerm02886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02886_fast_pow_mod_ne_one

def fullRecordGapValue02887 : Nat := fullRecordGapCenterValue - 196114

theorem fullRecordGapTerm02887_eq_value :
    recordGapCenter - 196114 = fullRecordGapValue02887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02887 (fullRecordGapValue02887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02887_not_prime : ¬(recordGapCenter - 196114).Prime := by
  rw [fullRecordGapTerm02887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02887_fast_pow_mod_ne_one

def fullRecordGapValue02888 : Nat := fullRecordGapCenterValue - 196018

theorem fullRecordGapTerm02888_eq_value :
    recordGapCenter - 196018 = fullRecordGapValue02888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02888 (fullRecordGapValue02888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02888_not_prime : ¬(recordGapCenter - 196018).Prime := by
  rw [fullRecordGapTerm02888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02888_fast_pow_mod_ne_one

def fullRecordGapValue02889 : Nat := fullRecordGapCenterValue - 196012

theorem fullRecordGapTerm02889_eq_value :
    recordGapCenter - 196012 = fullRecordGapValue02889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02889 (fullRecordGapValue02889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02889_not_prime : ¬(recordGapCenter - 196012).Prime := by
  rw [fullRecordGapTerm02889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02889_fast_pow_mod_ne_one

def fullRecordGapValue02890 : Nat := fullRecordGapCenterValue - 195964

theorem fullRecordGapTerm02890_eq_value :
    recordGapCenter - 195964 = fullRecordGapValue02890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02890 (fullRecordGapValue02890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02890_not_prime : ¬(recordGapCenter - 195964).Prime := by
  rw [fullRecordGapTerm02890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02890_fast_pow_mod_ne_one

def fullRecordGapValue02891 : Nat := fullRecordGapCenterValue - 195268

theorem fullRecordGapTerm02891_eq_value :
    recordGapCenter - 195268 = fullRecordGapValue02891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02891 (fullRecordGapValue02891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02891_not_prime : ¬(recordGapCenter - 195268).Prime := by
  rw [fullRecordGapTerm02891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02891_fast_pow_mod_ne_one

def fullRecordGapValue02892 : Nat := fullRecordGapCenterValue - 195214

theorem fullRecordGapTerm02892_eq_value :
    recordGapCenter - 195214 = fullRecordGapValue02892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02892 (fullRecordGapValue02892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02892_not_prime : ¬(recordGapCenter - 195214).Prime := by
  rw [fullRecordGapTerm02892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02892_fast_pow_mod_ne_one

def fullRecordGapValue02893 : Nat := fullRecordGapCenterValue - 195124

theorem fullRecordGapTerm02893_eq_value :
    recordGapCenter - 195124 = fullRecordGapValue02893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02893 (fullRecordGapValue02893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02893_not_prime : ¬(recordGapCenter - 195124).Prime := by
  rw [fullRecordGapTerm02893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02893_fast_pow_mod_ne_one

def fullRecordGapValue02894 : Nat := fullRecordGapCenterValue - 195094

theorem fullRecordGapTerm02894_eq_value :
    recordGapCenter - 195094 = fullRecordGapValue02894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02894 (fullRecordGapValue02894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02894_not_prime : ¬(recordGapCenter - 195094).Prime := by
  rw [fullRecordGapTerm02894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02894_fast_pow_mod_ne_one

def fullRecordGapValue02895 : Nat := fullRecordGapCenterValue - 194758

theorem fullRecordGapTerm02895_eq_value :
    recordGapCenter - 194758 = fullRecordGapValue02895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02895 (fullRecordGapValue02895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02895_not_prime : ¬(recordGapCenter - 194758).Prime := by
  rw [fullRecordGapTerm02895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02895_fast_pow_mod_ne_one

def fullRecordGapValue02896 : Nat := fullRecordGapCenterValue - 194644

theorem fullRecordGapTerm02896_eq_value :
    recordGapCenter - 194644 = fullRecordGapValue02896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02896 (fullRecordGapValue02896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02896_not_prime : ¬(recordGapCenter - 194644).Prime := by
  rw [fullRecordGapTerm02896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02896_fast_pow_mod_ne_one

def fullRecordGapValue02897 : Nat := fullRecordGapCenterValue - 194400

theorem fullRecordGapTerm02897_eq_value :
    recordGapCenter - 194400 = fullRecordGapValue02897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02897 (fullRecordGapValue02897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02897_not_prime : ¬(recordGapCenter - 194400).Prime := by
  rw [fullRecordGapTerm02897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02897_fast_pow_mod_ne_one

def fullRecordGapValue02898 : Nat := fullRecordGapCenterValue - 194338

theorem fullRecordGapTerm02898_eq_value :
    recordGapCenter - 194338 = fullRecordGapValue02898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02898 (fullRecordGapValue02898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02898_not_prime : ¬(recordGapCenter - 194338).Prime := by
  rw [fullRecordGapTerm02898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02898_fast_pow_mod_ne_one

def fullRecordGapValue02899 : Nat := fullRecordGapCenterValue - 194254

theorem fullRecordGapTerm02899_eq_value :
    recordGapCenter - 194254 = fullRecordGapValue02899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02899 (fullRecordGapValue02899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02899_not_prime : ¬(recordGapCenter - 194254).Prime := by
  rw [fullRecordGapTerm02899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02899_fast_pow_mod_ne_one

def fullRecordGapValue02900 : Nat := fullRecordGapCenterValue - 194014

theorem fullRecordGapTerm02900_eq_value :
    recordGapCenter - 194014 = fullRecordGapValue02900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02900 (fullRecordGapValue02900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02900_not_prime : ¬(recordGapCenter - 194014).Prime := by
  rw [fullRecordGapTerm02900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02900_fast_pow_mod_ne_one

def fullRecordGapValue02901 : Nat := fullRecordGapCenterValue - 194002

theorem fullRecordGapTerm02901_eq_value :
    recordGapCenter - 194002 = fullRecordGapValue02901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02901 (fullRecordGapValue02901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02901_not_prime : ¬(recordGapCenter - 194002).Prime := by
  rw [fullRecordGapTerm02901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02901_fast_pow_mod_ne_one

def fullRecordGapValue02902 : Nat := fullRecordGapCenterValue - 193654

theorem fullRecordGapTerm02902_eq_value :
    recordGapCenter - 193654 = fullRecordGapValue02902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02902 (fullRecordGapValue02902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02902_not_prime : ¬(recordGapCenter - 193654).Prime := by
  rw [fullRecordGapTerm02902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02902_fast_pow_mod_ne_one

def fullRecordGapValue02903 : Nat := fullRecordGapCenterValue - 193594

theorem fullRecordGapTerm02903_eq_value :
    recordGapCenter - 193594 = fullRecordGapValue02903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02903 (fullRecordGapValue02903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02903_not_prime : ¬(recordGapCenter - 193594).Prime := by
  rw [fullRecordGapTerm02903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02903_fast_pow_mod_ne_one

def fullRecordGapValue02904 : Nat := fullRecordGapCenterValue - 193588

theorem fullRecordGapTerm02904_eq_value :
    recordGapCenter - 193588 = fullRecordGapValue02904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02904 (fullRecordGapValue02904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02904_not_prime : ¬(recordGapCenter - 193588).Prime := by
  rw [fullRecordGapTerm02904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02904_fast_pow_mod_ne_one

def fullRecordGapValue02905 : Nat := fullRecordGapCenterValue - 193162

theorem fullRecordGapTerm02905_eq_value :
    recordGapCenter - 193162 = fullRecordGapValue02905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02905 (fullRecordGapValue02905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02905_not_prime : ¬(recordGapCenter - 193162).Prime := by
  rw [fullRecordGapTerm02905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02905_fast_pow_mod_ne_one

def fullRecordGapValue02906 : Nat := fullRecordGapCenterValue - 192958

theorem fullRecordGapTerm02906_eq_value :
    recordGapCenter - 192958 = fullRecordGapValue02906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02906 (fullRecordGapValue02906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02906_not_prime : ¬(recordGapCenter - 192958).Prime := by
  rw [fullRecordGapTerm02906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02906_fast_pow_mod_ne_one

def fullRecordGapValue02907 : Nat := fullRecordGapCenterValue - 192772

theorem fullRecordGapTerm02907_eq_value :
    recordGapCenter - 192772 = fullRecordGapValue02907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02907 (fullRecordGapValue02907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02907_not_prime : ¬(recordGapCenter - 192772).Prime := by
  rw [fullRecordGapTerm02907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02907_fast_pow_mod_ne_one

def fullRecordGapValue02908 : Nat := fullRecordGapCenterValue - 192034

theorem fullRecordGapTerm02908_eq_value :
    recordGapCenter - 192034 = fullRecordGapValue02908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02908 (fullRecordGapValue02908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02908_not_prime : ¬(recordGapCenter - 192034).Prime := by
  rw [fullRecordGapTerm02908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02908_fast_pow_mod_ne_one

def fullRecordGapValue02909 : Nat := fullRecordGapCenterValue - 192000

theorem fullRecordGapTerm02909_eq_value :
    recordGapCenter - 192000 = fullRecordGapValue02909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02909 (fullRecordGapValue02909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02909_not_prime : ¬(recordGapCenter - 192000).Prime := by
  rw [fullRecordGapTerm02909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02909_fast_pow_mod_ne_one

def fullRecordGapValue02910 : Nat := fullRecordGapCenterValue - 191914

theorem fullRecordGapTerm02910_eq_value :
    recordGapCenter - 191914 = fullRecordGapValue02910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02910 (fullRecordGapValue02910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02910_not_prime : ¬(recordGapCenter - 191914).Prime := by
  rw [fullRecordGapTerm02910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02910_fast_pow_mod_ne_one

def fullRecordGapValue02911 : Nat := fullRecordGapCenterValue - 191908

theorem fullRecordGapTerm02911_eq_value :
    recordGapCenter - 191908 = fullRecordGapValue02911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02911 (fullRecordGapValue02911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02911_not_prime : ¬(recordGapCenter - 191908).Prime := by
  rw [fullRecordGapTerm02911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02911_fast_pow_mod_ne_one

def fullRecordGapValue02912 : Nat := fullRecordGapCenterValue - 191788

theorem fullRecordGapTerm02912_eq_value :
    recordGapCenter - 191788 = fullRecordGapValue02912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02912 (fullRecordGapValue02912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02912_not_prime : ¬(recordGapCenter - 191788).Prime := by
  rw [fullRecordGapTerm02912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02912_fast_pow_mod_ne_one

def fullRecordGapValue02913 : Nat := fullRecordGapCenterValue - 191782

theorem fullRecordGapTerm02913_eq_value :
    recordGapCenter - 191782 = fullRecordGapValue02913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02913 (fullRecordGapValue02913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02913_not_prime : ¬(recordGapCenter - 191782).Prime := by
  rw [fullRecordGapTerm02913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02913_fast_pow_mod_ne_one

def fullRecordGapValue02914 : Nat := fullRecordGapCenterValue - 191664

theorem fullRecordGapTerm02914_eq_value :
    recordGapCenter - 191664 = fullRecordGapValue02914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02914 (fullRecordGapValue02914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02914_not_prime : ¬(recordGapCenter - 191664).Prime := by
  rw [fullRecordGapTerm02914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02914_fast_pow_mod_ne_one

def fullRecordGapValue02915 : Nat := fullRecordGapCenterValue - 191578

theorem fullRecordGapTerm02915_eq_value :
    recordGapCenter - 191578 = fullRecordGapValue02915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02915 (fullRecordGapValue02915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02915_not_prime : ¬(recordGapCenter - 191578).Prime := by
  rw [fullRecordGapTerm02915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02915_fast_pow_mod_ne_one

def fullRecordGapValue02916 : Nat := fullRecordGapCenterValue - 191524

theorem fullRecordGapTerm02916_eq_value :
    recordGapCenter - 191524 = fullRecordGapValue02916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02916 (fullRecordGapValue02916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02916_not_prime : ¬(recordGapCenter - 191524).Prime := by
  rw [fullRecordGapTerm02916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02916_fast_pow_mod_ne_one

def fullRecordGapValue02917 : Nat := fullRecordGapCenterValue - 191242

theorem fullRecordGapTerm02917_eq_value :
    recordGapCenter - 191242 = fullRecordGapValue02917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02917 (fullRecordGapValue02917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02917_not_prime : ¬(recordGapCenter - 191242).Prime := by
  rw [fullRecordGapTerm02917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02917_fast_pow_mod_ne_one

def fullRecordGapValue02918 : Nat := fullRecordGapCenterValue - 191194

theorem fullRecordGapTerm02918_eq_value :
    recordGapCenter - 191194 = fullRecordGapValue02918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02918 (fullRecordGapValue02918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02918_not_prime : ¬(recordGapCenter - 191194).Prime := by
  rw [fullRecordGapTerm02918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02918_fast_pow_mod_ne_one

def fullRecordGapValue02919 : Nat := fullRecordGapCenterValue - 191188

theorem fullRecordGapTerm02919_eq_value :
    recordGapCenter - 191188 = fullRecordGapValue02919 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02919_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02919 (fullRecordGapValue02919 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02919_not_prime : ¬(recordGapCenter - 191188).Prime := by
  rw [fullRecordGapTerm02919_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02919, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02919_fast_pow_mod_ne_one

def fullRecordGapValue02920 : Nat := fullRecordGapCenterValue - 191098

theorem fullRecordGapTerm02920_eq_value :
    recordGapCenter - 191098 = fullRecordGapValue02920 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02920_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02920 (fullRecordGapValue02920 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02920_not_prime : ¬(recordGapCenter - 191098).Prime := by
  rw [fullRecordGapTerm02920_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02920, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02920_fast_pow_mod_ne_one

def fullRecordGapValue02921 : Nat := fullRecordGapCenterValue - 191062

theorem fullRecordGapTerm02921_eq_value :
    recordGapCenter - 191062 = fullRecordGapValue02921 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02921_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02921 (fullRecordGapValue02921 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02921_not_prime : ¬(recordGapCenter - 191062).Prime := by
  rw [fullRecordGapTerm02921_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02921, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02921_fast_pow_mod_ne_one

def fullRecordGapValue02922 : Nat := fullRecordGapCenterValue - 191014

theorem fullRecordGapTerm02922_eq_value :
    recordGapCenter - 191014 = fullRecordGapValue02922 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02922_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02922 (fullRecordGapValue02922 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02922_not_prime : ¬(recordGapCenter - 191014).Prime := by
  rw [fullRecordGapTerm02922_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02922, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02922_fast_pow_mod_ne_one

def fullRecordGapValue02923 : Nat := fullRecordGapCenterValue - 190972

theorem fullRecordGapTerm02923_eq_value :
    recordGapCenter - 190972 = fullRecordGapValue02923 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02923_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02923 (fullRecordGapValue02923 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02923_not_prime : ¬(recordGapCenter - 190972).Prime := by
  rw [fullRecordGapTerm02923_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02923, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02923_fast_pow_mod_ne_one

def fullRecordGapValue02924 : Nat := fullRecordGapCenterValue - 190948

theorem fullRecordGapTerm02924_eq_value :
    recordGapCenter - 190948 = fullRecordGapValue02924 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02924_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02924 (fullRecordGapValue02924 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02924_not_prime : ¬(recordGapCenter - 190948).Prime := by
  rw [fullRecordGapTerm02924_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02924, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02924_fast_pow_mod_ne_one

def fullRecordGapValue02925 : Nat := fullRecordGapCenterValue - 190882

theorem fullRecordGapTerm02925_eq_value :
    recordGapCenter - 190882 = fullRecordGapValue02925 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02925_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02925 (fullRecordGapValue02925 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02925_not_prime : ¬(recordGapCenter - 190882).Prime := by
  rw [fullRecordGapTerm02925_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02925, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02925_fast_pow_mod_ne_one

def fullRecordGapValue02926 : Nat := fullRecordGapCenterValue - 190858

theorem fullRecordGapTerm02926_eq_value :
    recordGapCenter - 190858 = fullRecordGapValue02926 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02926_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02926 (fullRecordGapValue02926 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02926_not_prime : ¬(recordGapCenter - 190858).Prime := by
  rw [fullRecordGapTerm02926_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02926, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02926_fast_pow_mod_ne_one

def fullRecordGapValue02927 : Nat := fullRecordGapCenterValue - 190804

theorem fullRecordGapTerm02927_eq_value :
    recordGapCenter - 190804 = fullRecordGapValue02927 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02927_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02927 (fullRecordGapValue02927 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02927_not_prime : ¬(recordGapCenter - 190804).Prime := by
  rw [fullRecordGapTerm02927_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02927, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02927_fast_pow_mod_ne_one

def fullRecordGapValue02928 : Nat := fullRecordGapCenterValue - 190512

theorem fullRecordGapTerm02928_eq_value :
    recordGapCenter - 190512 = fullRecordGapValue02928 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02928_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02928 (fullRecordGapValue02928 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02928_not_prime : ¬(recordGapCenter - 190512).Prime := by
  rw [fullRecordGapTerm02928_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02928, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02928_fast_pow_mod_ne_one

def fullRecordGapValue02929 : Nat := fullRecordGapCenterValue - 190462

theorem fullRecordGapTerm02929_eq_value :
    recordGapCenter - 190462 = fullRecordGapValue02929 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02929_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02929 (fullRecordGapValue02929 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02929_not_prime : ¬(recordGapCenter - 190462).Prime := by
  rw [fullRecordGapTerm02929_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02929, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02929_fast_pow_mod_ne_one

def fullRecordGapValue02930 : Nat := fullRecordGapCenterValue - 190378

theorem fullRecordGapTerm02930_eq_value :
    recordGapCenter - 190378 = fullRecordGapValue02930 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02930_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02930 (fullRecordGapValue02930 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02930_not_prime : ¬(recordGapCenter - 190378).Prime := by
  rw [fullRecordGapTerm02930_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02930, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02930_fast_pow_mod_ne_one

def fullRecordGapValue02931 : Nat := fullRecordGapCenterValue - 190354

theorem fullRecordGapTerm02931_eq_value :
    recordGapCenter - 190354 = fullRecordGapValue02931 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02931_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02931 (fullRecordGapValue02931 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02931_not_prime : ¬(recordGapCenter - 190354).Prime := by
  rw [fullRecordGapTerm02931_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02931, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02931_fast_pow_mod_ne_one

def fullRecordGapValue02932 : Nat := fullRecordGapCenterValue - 190080

theorem fullRecordGapTerm02932_eq_value :
    recordGapCenter - 190080 = fullRecordGapValue02932 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02932_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02932 (fullRecordGapValue02932 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02932_not_prime : ¬(recordGapCenter - 190080).Prime := by
  rw [fullRecordGapTerm02932_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02932, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02932_fast_pow_mod_ne_one

def fullRecordGapValue02933 : Nat := fullRecordGapCenterValue - 190054

theorem fullRecordGapTerm02933_eq_value :
    recordGapCenter - 190054 = fullRecordGapValue02933 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02933_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02933 (fullRecordGapValue02933 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02933_not_prime : ¬(recordGapCenter - 190054).Prime := by
  rw [fullRecordGapTerm02933_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02933, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02933_fast_pow_mod_ne_one

def fullRecordGapValue02934 : Nat := fullRecordGapCenterValue - 189964

theorem fullRecordGapTerm02934_eq_value :
    recordGapCenter - 189964 = fullRecordGapValue02934 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02934_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02934 (fullRecordGapValue02934 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02934_not_prime : ¬(recordGapCenter - 189964).Prime := by
  rw [fullRecordGapTerm02934_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02934, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02934_fast_pow_mod_ne_one

def fullRecordGapValue02935 : Nat := fullRecordGapCenterValue - 189922

theorem fullRecordGapTerm02935_eq_value :
    recordGapCenter - 189922 = fullRecordGapValue02935 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02935_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02935 (fullRecordGapValue02935 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02935_not_prime : ¬(recordGapCenter - 189922).Prime := by
  rw [fullRecordGapTerm02935_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02935, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02935_fast_pow_mod_ne_one

def fullRecordGapValue02936 : Nat := fullRecordGapCenterValue - 189814

theorem fullRecordGapTerm02936_eq_value :
    recordGapCenter - 189814 = fullRecordGapValue02936 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02936_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02936 (fullRecordGapValue02936 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02936_not_prime : ¬(recordGapCenter - 189814).Prime := by
  rw [fullRecordGapTerm02936_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02936, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02936_fast_pow_mod_ne_one

def fullRecordGapValue02937 : Nat := fullRecordGapCenterValue - 189724

theorem fullRecordGapTerm02937_eq_value :
    recordGapCenter - 189724 = fullRecordGapValue02937 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02937_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02937 (fullRecordGapValue02937 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02937_not_prime : ¬(recordGapCenter - 189724).Prime := by
  rw [fullRecordGapTerm02937_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02937, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02937_fast_pow_mod_ne_one

def fullRecordGapValue02938 : Nat := fullRecordGapCenterValue - 189454

theorem fullRecordGapTerm02938_eq_value :
    recordGapCenter - 189454 = fullRecordGapValue02938 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02938_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02938 (fullRecordGapValue02938 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02938_not_prime : ¬(recordGapCenter - 189454).Prime := by
  rw [fullRecordGapTerm02938_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02938, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02938_fast_pow_mod_ne_one

def fullRecordGapValue02939 : Nat := fullRecordGapCenterValue - 189418

theorem fullRecordGapTerm02939_eq_value :
    recordGapCenter - 189418 = fullRecordGapValue02939 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02939_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02939 (fullRecordGapValue02939 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02939_not_prime : ¬(recordGapCenter - 189418).Prime := by
  rw [fullRecordGapTerm02939_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02939, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02939_fast_pow_mod_ne_one

def fullRecordGapValue02940 : Nat := fullRecordGapCenterValue - 189298

theorem fullRecordGapTerm02940_eq_value :
    recordGapCenter - 189298 = fullRecordGapValue02940 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02940_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02940 (fullRecordGapValue02940 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02940_not_prime : ¬(recordGapCenter - 189298).Prime := by
  rw [fullRecordGapTerm02940_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02940, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02940_fast_pow_mod_ne_one

def fullRecordGapValue02941 : Nat := fullRecordGapCenterValue - 189268

theorem fullRecordGapTerm02941_eq_value :
    recordGapCenter - 189268 = fullRecordGapValue02941 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02941_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02941 (fullRecordGapValue02941 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02941_not_prime : ¬(recordGapCenter - 189268).Prime := by
  rw [fullRecordGapTerm02941_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02941, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02941_fast_pow_mod_ne_one

def fullRecordGapValue02942 : Nat := fullRecordGapCenterValue - 189172

theorem fullRecordGapTerm02942_eq_value :
    recordGapCenter - 189172 = fullRecordGapValue02942 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02942_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02942 (fullRecordGapValue02942 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02942_not_prime : ¬(recordGapCenter - 189172).Prime := by
  rw [fullRecordGapTerm02942_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02942, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02942_fast_pow_mod_ne_one

def fullRecordGapValue02943 : Nat := fullRecordGapCenterValue - 189118

theorem fullRecordGapTerm02943_eq_value :
    recordGapCenter - 189118 = fullRecordGapValue02943 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02943_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02943 (fullRecordGapValue02943 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02943_not_prime : ¬(recordGapCenter - 189118).Prime := by
  rw [fullRecordGapTerm02943_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02943, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02943_fast_pow_mod_ne_one

def fullRecordGapValue02944 : Nat := fullRecordGapCenterValue - 188878

theorem fullRecordGapTerm02944_eq_value :
    recordGapCenter - 188878 = fullRecordGapValue02944 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02944_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02944 (fullRecordGapValue02944 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02944_not_prime : ¬(recordGapCenter - 188878).Prime := by
  rw [fullRecordGapTerm02944_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02944, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02944_fast_pow_mod_ne_one

def fullRecordGapValue02945 : Nat := fullRecordGapCenterValue - 188794

theorem fullRecordGapTerm02945_eq_value :
    recordGapCenter - 188794 = fullRecordGapValue02945 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02945_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02945 (fullRecordGapValue02945 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02945_not_prime : ¬(recordGapCenter - 188794).Prime := by
  rw [fullRecordGapTerm02945_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02945, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02945_fast_pow_mod_ne_one

def fullRecordGapValue02946 : Nat := fullRecordGapCenterValue - 188662

theorem fullRecordGapTerm02946_eq_value :
    recordGapCenter - 188662 = fullRecordGapValue02946 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02946_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02946 (fullRecordGapValue02946 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02946_not_prime : ¬(recordGapCenter - 188662).Prime := by
  rw [fullRecordGapTerm02946_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02946, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02946_fast_pow_mod_ne_one

def fullRecordGapValue02947 : Nat := fullRecordGapCenterValue - 188548

theorem fullRecordGapTerm02947_eq_value :
    recordGapCenter - 188548 = fullRecordGapValue02947 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02947_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02947 (fullRecordGapValue02947 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02947_not_prime : ¬(recordGapCenter - 188548).Prime := by
  rw [fullRecordGapTerm02947_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02947, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02947_fast_pow_mod_ne_one

def fullRecordGapValue02948 : Nat := fullRecordGapCenterValue - 188458

theorem fullRecordGapTerm02948_eq_value :
    recordGapCenter - 188458 = fullRecordGapValue02948 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02948_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02948 (fullRecordGapValue02948 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02948_not_prime : ¬(recordGapCenter - 188458).Prime := by
  rw [fullRecordGapTerm02948_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02948, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02948_fast_pow_mod_ne_one

def fullRecordGapValue02949 : Nat := fullRecordGapCenterValue - 188218

theorem fullRecordGapTerm02949_eq_value :
    recordGapCenter - 188218 = fullRecordGapValue02949 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02949_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02949 (fullRecordGapValue02949 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02949_not_prime : ¬(recordGapCenter - 188218).Prime := by
  rw [fullRecordGapTerm02949_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02949, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02949_fast_pow_mod_ne_one

def fullRecordGapValue02950 : Nat := fullRecordGapCenterValue - 188164

theorem fullRecordGapTerm02950_eq_value :
    recordGapCenter - 188164 = fullRecordGapValue02950 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02950_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02950 (fullRecordGapValue02950 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02950_not_prime : ¬(recordGapCenter - 188164).Prime := by
  rw [fullRecordGapTerm02950_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02950, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02950_fast_pow_mod_ne_one

def fullRecordGapValue02951 : Nat := fullRecordGapCenterValue - 188160

theorem fullRecordGapTerm02951_eq_value :
    recordGapCenter - 188160 = fullRecordGapValue02951 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02951_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02951 (fullRecordGapValue02951 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02951_not_prime : ¬(recordGapCenter - 188160).Prime := by
  rw [fullRecordGapTerm02951_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02951, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02951_fast_pow_mod_ne_one

def fullRecordGapValue02952 : Nat := fullRecordGapCenterValue - 188158

theorem fullRecordGapTerm02952_eq_value :
    recordGapCenter - 188158 = fullRecordGapValue02952 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02952_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02952 (fullRecordGapValue02952 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02952_not_prime : ¬(recordGapCenter - 188158).Prime := by
  rw [fullRecordGapTerm02952_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02952, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02952_fast_pow_mod_ne_one

def fullRecordGapValue02953 : Nat := fullRecordGapCenterValue - 187822

theorem fullRecordGapTerm02953_eq_value :
    recordGapCenter - 187822 = fullRecordGapValue02953 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02953_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02953 (fullRecordGapValue02953 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02953_not_prime : ¬(recordGapCenter - 187822).Prime := by
  rw [fullRecordGapTerm02953_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02953, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02953_fast_pow_mod_ne_one

def fullRecordGapValue02954 : Nat := fullRecordGapCenterValue - 187732

theorem fullRecordGapTerm02954_eq_value :
    recordGapCenter - 187732 = fullRecordGapValue02954 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02954_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02954 (fullRecordGapValue02954 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02954_not_prime : ¬(recordGapCenter - 187732).Prime := by
  rw [fullRecordGapTerm02954_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02954, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02954_fast_pow_mod_ne_one

def fullRecordGapValue02955 : Nat := fullRecordGapCenterValue - 187522

theorem fullRecordGapTerm02955_eq_value :
    recordGapCenter - 187522 = fullRecordGapValue02955 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02955_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02955 (fullRecordGapValue02955 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02955_not_prime : ¬(recordGapCenter - 187522).Prime := by
  rw [fullRecordGapTerm02955_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02955, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02955_fast_pow_mod_ne_one

def fullRecordGapValue02956 : Nat := fullRecordGapCenterValue - 187500

theorem fullRecordGapTerm02956_eq_value :
    recordGapCenter - 187500 = fullRecordGapValue02956 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02956_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02956 (fullRecordGapValue02956 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02956_not_prime : ¬(recordGapCenter - 187500).Prime := by
  rw [fullRecordGapTerm02956_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02956, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02956_fast_pow_mod_ne_one

def fullRecordGapValue02957 : Nat := fullRecordGapCenterValue - 187438

theorem fullRecordGapTerm02957_eq_value :
    recordGapCenter - 187438 = fullRecordGapValue02957 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02957_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02957 (fullRecordGapValue02957 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02957_not_prime : ¬(recordGapCenter - 187438).Prime := by
  rw [fullRecordGapTerm02957_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02957, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02957_fast_pow_mod_ne_one

def fullRecordGapValue02958 : Nat := fullRecordGapCenterValue - 187324

theorem fullRecordGapTerm02958_eq_value :
    recordGapCenter - 187324 = fullRecordGapValue02958 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02958_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02958 (fullRecordGapValue02958 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02958_not_prime : ¬(recordGapCenter - 187324).Prime := by
  rw [fullRecordGapTerm02958_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02958, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02958_fast_pow_mod_ne_one

def fullRecordGapValue02959 : Nat := fullRecordGapCenterValue - 187084

theorem fullRecordGapTerm02959_eq_value :
    recordGapCenter - 187084 = fullRecordGapValue02959 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02959_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02959 (fullRecordGapValue02959 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02959_not_prime : ¬(recordGapCenter - 187084).Prime := by
  rw [fullRecordGapTerm02959_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02959, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02959_fast_pow_mod_ne_one

def fullRecordGapValue02960 : Nat := fullRecordGapCenterValue - 186994

theorem fullRecordGapTerm02960_eq_value :
    recordGapCenter - 186994 = fullRecordGapValue02960 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02960_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02960 (fullRecordGapValue02960 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02960_not_prime : ¬(recordGapCenter - 186994).Prime := by
  rw [fullRecordGapTerm02960_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02960, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02960_fast_pow_mod_ne_one

def fullRecordGapValue02961 : Nat := fullRecordGapCenterValue - 186988

theorem fullRecordGapTerm02961_eq_value :
    recordGapCenter - 186988 = fullRecordGapValue02961 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02961_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02961 (fullRecordGapValue02961 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02961_not_prime : ¬(recordGapCenter - 186988).Prime := by
  rw [fullRecordGapTerm02961_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02961, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02961_fast_pow_mod_ne_one

def fullRecordGapValue02962 : Nat := fullRecordGapCenterValue - 186958

theorem fullRecordGapTerm02962_eq_value :
    recordGapCenter - 186958 = fullRecordGapValue02962 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02962_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02962 (fullRecordGapValue02962 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02962_not_prime : ¬(recordGapCenter - 186958).Prime := by
  rw [fullRecordGapTerm02962_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02962, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02962_fast_pow_mod_ne_one

def fullRecordGapValue02963 : Nat := fullRecordGapCenterValue - 186724

theorem fullRecordGapTerm02963_eq_value :
    recordGapCenter - 186724 = fullRecordGapValue02963 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02963_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02963 (fullRecordGapValue02963 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02963_not_prime : ¬(recordGapCenter - 186724).Prime := by
  rw [fullRecordGapTerm02963_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02963, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02963_fast_pow_mod_ne_one

def fullRecordGapValue02964 : Nat := fullRecordGapCenterValue - 186624

theorem fullRecordGapTerm02964_eq_value :
    recordGapCenter - 186624 = fullRecordGapValue02964 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02964_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02964 (fullRecordGapValue02964 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02964_not_prime : ¬(recordGapCenter - 186624).Prime := by
  rw [fullRecordGapTerm02964_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02964, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02964_fast_pow_mod_ne_one

def fullRecordGapValue02965 : Nat := fullRecordGapCenterValue - 186574

theorem fullRecordGapTerm02965_eq_value :
    recordGapCenter - 186574 = fullRecordGapValue02965 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02965_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02965 (fullRecordGapValue02965 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02965_not_prime : ¬(recordGapCenter - 186574).Prime := by
  rw [fullRecordGapTerm02965_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02965, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02965_fast_pow_mod_ne_one

def fullRecordGapValue02966 : Nat := fullRecordGapCenterValue - 186478

theorem fullRecordGapTerm02966_eq_value :
    recordGapCenter - 186478 = fullRecordGapValue02966 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02966_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02966 (fullRecordGapValue02966 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02966_not_prime : ¬(recordGapCenter - 186478).Prime := by
  rw [fullRecordGapTerm02966_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02966, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02966_fast_pow_mod_ne_one

def fullRecordGapValue02967 : Nat := fullRecordGapCenterValue - 186340

theorem fullRecordGapTerm02967_eq_value :
    recordGapCenter - 186340 = fullRecordGapValue02967 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02967_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02967 (fullRecordGapValue02967 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02967_not_prime : ¬(recordGapCenter - 186340).Prime := by
  rw [fullRecordGapTerm02967_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02967, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02967_fast_pow_mod_ne_one

def fullRecordGapValue02968 : Nat := fullRecordGapCenterValue - 186268

theorem fullRecordGapTerm02968_eq_value :
    recordGapCenter - 186268 = fullRecordGapValue02968 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02968_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02968 (fullRecordGapValue02968 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02968_not_prime : ¬(recordGapCenter - 186268).Prime := by
  rw [fullRecordGapTerm02968_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02968, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02968_fast_pow_mod_ne_one

def fullRecordGapValue02969 : Nat := fullRecordGapCenterValue - 186262

theorem fullRecordGapTerm02969_eq_value :
    recordGapCenter - 186262 = fullRecordGapValue02969 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02969_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02969 (fullRecordGapValue02969 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02969_not_prime : ¬(recordGapCenter - 186262).Prime := by
  rw [fullRecordGapTerm02969_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02969, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02969_fast_pow_mod_ne_one

def fullRecordGapValue02970 : Nat := fullRecordGapCenterValue - 186178

theorem fullRecordGapTerm02970_eq_value :
    recordGapCenter - 186178 = fullRecordGapValue02970 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02970_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02970 (fullRecordGapValue02970 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02970_not_prime : ¬(recordGapCenter - 186178).Prime := by
  rw [fullRecordGapTerm02970_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02970, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02970_fast_pow_mod_ne_one

def fullRecordGapValue02971 : Nat := fullRecordGapCenterValue - 186094

theorem fullRecordGapTerm02971_eq_value :
    recordGapCenter - 186094 = fullRecordGapValue02971 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02971_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02971 (fullRecordGapValue02971 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02971_not_prime : ¬(recordGapCenter - 186094).Prime := by
  rw [fullRecordGapTerm02971_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02971, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02971_fast_pow_mod_ne_one

def fullRecordGapValue02972 : Nat := fullRecordGapCenterValue - 186028

theorem fullRecordGapTerm02972_eq_value :
    recordGapCenter - 186028 = fullRecordGapValue02972 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02972_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02972 (fullRecordGapValue02972 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02972_not_prime : ¬(recordGapCenter - 186028).Prime := by
  rw [fullRecordGapTerm02972_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02972, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02972_fast_pow_mod_ne_one

def fullRecordGapValue02973 : Nat := fullRecordGapCenterValue - 185908

theorem fullRecordGapTerm02973_eq_value :
    recordGapCenter - 185908 = fullRecordGapValue02973 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02973_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02973 (fullRecordGapValue02973 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02973_not_prime : ¬(recordGapCenter - 185908).Prime := by
  rw [fullRecordGapTerm02973_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02973, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02973_fast_pow_mod_ne_one

def fullRecordGapValue02974 : Nat := fullRecordGapCenterValue - 185884

theorem fullRecordGapTerm02974_eq_value :
    recordGapCenter - 185884 = fullRecordGapValue02974 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02974_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02974 (fullRecordGapValue02974 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02974_not_prime : ¬(recordGapCenter - 185884).Prime := by
  rw [fullRecordGapTerm02974_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02974, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02974_fast_pow_mod_ne_one

def fullRecordGapValue02975 : Nat := fullRecordGapCenterValue - 185842

theorem fullRecordGapTerm02975_eq_value :
    recordGapCenter - 185842 = fullRecordGapValue02975 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02975_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02975 (fullRecordGapValue02975 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02975_not_prime : ¬(recordGapCenter - 185842).Prime := by
  rw [fullRecordGapTerm02975_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02975, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02975_fast_pow_mod_ne_one

def fullRecordGapValue02976 : Nat := fullRecordGapCenterValue - 185698

theorem fullRecordGapTerm02976_eq_value :
    recordGapCenter - 185698 = fullRecordGapValue02976 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02976_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02976 (fullRecordGapValue02976 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02976_not_prime : ¬(recordGapCenter - 185698).Prime := by
  rw [fullRecordGapTerm02976_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02976, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02976_fast_pow_mod_ne_one

def fullRecordGapValue02977 : Nat := fullRecordGapCenterValue - 185404

theorem fullRecordGapTerm02977_eq_value :
    recordGapCenter - 185404 = fullRecordGapValue02977 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02977_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02977 (fullRecordGapValue02977 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02977_not_prime : ¬(recordGapCenter - 185404).Prime := by
  rw [fullRecordGapTerm02977_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02977, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02977_fast_pow_mod_ne_one

def fullRecordGapValue02978 : Nat := fullRecordGapCenterValue - 185220

theorem fullRecordGapTerm02978_eq_value :
    recordGapCenter - 185220 = fullRecordGapValue02978 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02978_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02978 (fullRecordGapValue02978 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02978_not_prime : ¬(recordGapCenter - 185220).Prime := by
  rw [fullRecordGapTerm02978_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02978, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02978_fast_pow_mod_ne_one

def fullRecordGapValue02979 : Nat := fullRecordGapCenterValue - 185092

theorem fullRecordGapTerm02979_eq_value :
    recordGapCenter - 185092 = fullRecordGapValue02979 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02979_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02979 (fullRecordGapValue02979 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02979_not_prime : ¬(recordGapCenter - 185092).Prime := by
  rw [fullRecordGapTerm02979_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02979, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02979_fast_pow_mod_ne_one

def fullRecordGapValue02980 : Nat := fullRecordGapCenterValue - 185044

theorem fullRecordGapTerm02980_eq_value :
    recordGapCenter - 185044 = fullRecordGapValue02980 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02980_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02980 (fullRecordGapValue02980 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02980_not_prime : ¬(recordGapCenter - 185044).Prime := by
  rw [fullRecordGapTerm02980_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02980, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02980_fast_pow_mod_ne_one

def fullRecordGapValue02981 : Nat := fullRecordGapCenterValue - 184800

theorem fullRecordGapTerm02981_eq_value :
    recordGapCenter - 184800 = fullRecordGapValue02981 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02981_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02981 (fullRecordGapValue02981 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02981_not_prime : ¬(recordGapCenter - 184800).Prime := by
  rw [fullRecordGapTerm02981_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02981, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02981_fast_pow_mod_ne_one

def fullRecordGapValue02982 : Nat := fullRecordGapCenterValue - 184774

theorem fullRecordGapTerm02982_eq_value :
    recordGapCenter - 184774 = fullRecordGapValue02982 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02982_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02982 (fullRecordGapValue02982 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02982_not_prime : ¬(recordGapCenter - 184774).Prime := by
  rw [fullRecordGapTerm02982_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02982, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02982_fast_pow_mod_ne_one

def fullRecordGapValue02983 : Nat := fullRecordGapCenterValue - 184762

theorem fullRecordGapTerm02983_eq_value :
    recordGapCenter - 184762 = fullRecordGapValue02983 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02983_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02983 (fullRecordGapValue02983 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02983_not_prime : ¬(recordGapCenter - 184762).Prime := by
  rw [fullRecordGapTerm02983_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02983, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02983_fast_pow_mod_ne_one

def fullRecordGapValue02984 : Nat := fullRecordGapCenterValue - 184714

theorem fullRecordGapTerm02984_eq_value :
    recordGapCenter - 184714 = fullRecordGapValue02984 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02984_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02984 (fullRecordGapValue02984 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02984_not_prime : ¬(recordGapCenter - 184714).Prime := by
  rw [fullRecordGapTerm02984_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02984, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02984_fast_pow_mod_ne_one

def fullRecordGapValue02985 : Nat := fullRecordGapCenterValue - 184588

theorem fullRecordGapTerm02985_eq_value :
    recordGapCenter - 184588 = fullRecordGapValue02985 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02985_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02985 (fullRecordGapValue02985 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02985_not_prime : ¬(recordGapCenter - 184588).Prime := by
  rw [fullRecordGapTerm02985_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02985, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02985_fast_pow_mod_ne_one

def fullRecordGapValue02986 : Nat := fullRecordGapCenterValue - 184378

theorem fullRecordGapTerm02986_eq_value :
    recordGapCenter - 184378 = fullRecordGapValue02986 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02986_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02986 (fullRecordGapValue02986 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02986_not_prime : ¬(recordGapCenter - 184378).Prime := by
  rw [fullRecordGapTerm02986_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02986, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02986_fast_pow_mod_ne_one

def fullRecordGapValue02987 : Nat := fullRecordGapCenterValue - 184354

theorem fullRecordGapTerm02987_eq_value :
    recordGapCenter - 184354 = fullRecordGapValue02987 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02987_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02987 (fullRecordGapValue02987 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02987_not_prime : ¬(recordGapCenter - 184354).Prime := by
  rw [fullRecordGapTerm02987_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02987, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02987_fast_pow_mod_ne_one

def fullRecordGapValue02988 : Nat := fullRecordGapCenterValue - 184018

theorem fullRecordGapTerm02988_eq_value :
    recordGapCenter - 184018 = fullRecordGapValue02988 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02988_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02988 (fullRecordGapValue02988 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02988_not_prime : ¬(recordGapCenter - 184018).Prime := by
  rw [fullRecordGapTerm02988_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02988, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02988_fast_pow_mod_ne_one

def fullRecordGapValue02989 : Nat := fullRecordGapCenterValue - 183994

theorem fullRecordGapTerm02989_eq_value :
    recordGapCenter - 183994 = fullRecordGapValue02989 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02989_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02989 (fullRecordGapValue02989 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02989_not_prime : ¬(recordGapCenter - 183994).Prime := by
  rw [fullRecordGapTerm02989_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02989, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02989_fast_pow_mod_ne_one

def fullRecordGapValue02990 : Nat := fullRecordGapCenterValue - 183934

theorem fullRecordGapTerm02990_eq_value :
    recordGapCenter - 183934 = fullRecordGapValue02990 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02990_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02990 (fullRecordGapValue02990 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02990_not_prime : ¬(recordGapCenter - 183934).Prime := by
  rw [fullRecordGapTerm02990_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02990, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02990_fast_pow_mod_ne_one

def fullRecordGapValue02991 : Nat := fullRecordGapCenterValue - 183750

theorem fullRecordGapTerm02991_eq_value :
    recordGapCenter - 183750 = fullRecordGapValue02991 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02991_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02991 (fullRecordGapValue02991 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02991_not_prime : ¬(recordGapCenter - 183750).Prime := by
  rw [fullRecordGapTerm02991_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02991, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02991_fast_pow_mod_ne_one

def fullRecordGapValue02992 : Nat := fullRecordGapCenterValue - 183622

theorem fullRecordGapTerm02992_eq_value :
    recordGapCenter - 183622 = fullRecordGapValue02992 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02992_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02992 (fullRecordGapValue02992 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02992_not_prime : ¬(recordGapCenter - 183622).Prime := by
  rw [fullRecordGapTerm02992_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02992, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02992_fast_pow_mod_ne_one

def fullRecordGapValue02993 : Nat := fullRecordGapCenterValue - 183412

theorem fullRecordGapTerm02993_eq_value :
    recordGapCenter - 183412 = fullRecordGapValue02993 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02993_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02993 (fullRecordGapValue02993 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02993_not_prime : ¬(recordGapCenter - 183412).Prime := by
  rw [fullRecordGapTerm02993_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02993, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02993_fast_pow_mod_ne_one

def fullRecordGapValue02994 : Nat := fullRecordGapCenterValue - 183382

theorem fullRecordGapTerm02994_eq_value :
    recordGapCenter - 183382 = fullRecordGapValue02994 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02994_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02994 (fullRecordGapValue02994 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02994_not_prime : ¬(recordGapCenter - 183382).Prime := by
  rw [fullRecordGapTerm02994_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02994, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02994_fast_pow_mod_ne_one

def fullRecordGapValue02995 : Nat := fullRecordGapCenterValue - 183262

theorem fullRecordGapTerm02995_eq_value :
    recordGapCenter - 183262 = fullRecordGapValue02995 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02995_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02995 (fullRecordGapValue02995 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02995_not_prime : ¬(recordGapCenter - 183262).Prime := by
  rw [fullRecordGapTerm02995_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02995, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02995_fast_pow_mod_ne_one

def fullRecordGapValue02996 : Nat := fullRecordGapCenterValue - 183028

theorem fullRecordGapTerm02996_eq_value :
    recordGapCenter - 183028 = fullRecordGapValue02996 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02996_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02996 (fullRecordGapValue02996 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02996_not_prime : ¬(recordGapCenter - 183028).Prime := by
  rw [fullRecordGapTerm02996_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02996, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02996_fast_pow_mod_ne_one

def fullRecordGapValue02997 : Nat := fullRecordGapCenterValue - 183004

theorem fullRecordGapTerm02997_eq_value :
    recordGapCenter - 183004 = fullRecordGapValue02997 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02997_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02997 (fullRecordGapValue02997 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02997_not_prime : ¬(recordGapCenter - 183004).Prime := by
  rw [fullRecordGapTerm02997_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02997, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02997_fast_pow_mod_ne_one

def fullRecordGapValue02998 : Nat := fullRecordGapCenterValue - 182952

theorem fullRecordGapTerm02998_eq_value :
    recordGapCenter - 182952 = fullRecordGapValue02998 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02998_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02998 (fullRecordGapValue02998 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02998_not_prime : ¬(recordGapCenter - 182952).Prime := by
  rw [fullRecordGapTerm02998_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02998, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02998_fast_pow_mod_ne_one

def fullRecordGapValue02999 : Nat := fullRecordGapCenterValue - 182914

theorem fullRecordGapTerm02999_eq_value :
    recordGapCenter - 182914 = fullRecordGapValue02999 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02999_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02999 (fullRecordGapValue02999 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02999_not_prime : ¬(recordGapCenter - 182914).Prime := by
  rw [fullRecordGapTerm02999_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02999, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02999_fast_pow_mod_ne_one

def fullRecordGapValue03000 : Nat := fullRecordGapCenterValue - 182794

theorem fullRecordGapTerm03000_eq_value :
    recordGapCenter - 182794 = fullRecordGapValue03000 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03000_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03000 (fullRecordGapValue03000 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03000_not_prime : ¬(recordGapCenter - 182794).Prime := by
  rw [fullRecordGapTerm03000_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03000, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03000_fast_pow_mod_ne_one

def fullRecordGapValue03001 : Nat := fullRecordGapCenterValue - 182788

theorem fullRecordGapTerm03001_eq_value :
    recordGapCenter - 182788 = fullRecordGapValue03001 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03001_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03001 (fullRecordGapValue03001 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03001_not_prime : ¬(recordGapCenter - 182788).Prime := by
  rw [fullRecordGapTerm03001_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03001, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03001_fast_pow_mod_ne_one

def fullRecordGapValue03002 : Nat := fullRecordGapCenterValue - 182662

theorem fullRecordGapTerm03002_eq_value :
    recordGapCenter - 182662 = fullRecordGapValue03002 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03002_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03002 (fullRecordGapValue03002 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03002_not_prime : ¬(recordGapCenter - 182662).Prime := by
  rw [fullRecordGapTerm03002_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03002, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03002_fast_pow_mod_ne_one

def fullRecordGapValue03003 : Nat := fullRecordGapCenterValue - 182524

theorem fullRecordGapTerm03003_eq_value :
    recordGapCenter - 182524 = fullRecordGapValue03003 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03003_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03003 (fullRecordGapValue03003 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03003_not_prime : ¬(recordGapCenter - 182524).Prime := by
  rw [fullRecordGapTerm03003_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03003, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03003_fast_pow_mod_ne_one

def fullRecordGapValue03004 : Nat := fullRecordGapCenterValue - 182458

theorem fullRecordGapTerm03004_eq_value :
    recordGapCenter - 182458 = fullRecordGapValue03004 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03004_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03004 (fullRecordGapValue03004 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03004_not_prime : ¬(recordGapCenter - 182458).Prime := by
  rw [fullRecordGapTerm03004_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03004, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03004_fast_pow_mod_ne_one

def fullRecordGapValue03005 : Nat := fullRecordGapCenterValue - 182254

theorem fullRecordGapTerm03005_eq_value :
    recordGapCenter - 182254 = fullRecordGapValue03005 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03005_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03005 (fullRecordGapValue03005 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03005_not_prime : ¬(recordGapCenter - 182254).Prime := by
  rw [fullRecordGapTerm03005_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03005, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03005_fast_pow_mod_ne_one

def fullRecordGapValue03006 : Nat := fullRecordGapCenterValue - 182250

theorem fullRecordGapTerm03006_eq_value :
    recordGapCenter - 182250 = fullRecordGapValue03006 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03006_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03006 (fullRecordGapValue03006 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03006_not_prime : ¬(recordGapCenter - 182250).Prime := by
  rw [fullRecordGapTerm03006_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03006, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03006_fast_pow_mod_ne_one

def fullRecordGapValue03007 : Nat := fullRecordGapCenterValue - 182194

theorem fullRecordGapTerm03007_eq_value :
    recordGapCenter - 182194 = fullRecordGapValue03007 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03007_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03007 (fullRecordGapValue03007 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03007_not_prime : ¬(recordGapCenter - 182194).Prime := by
  rw [fullRecordGapTerm03007_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03007, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03007_fast_pow_mod_ne_one

def fullRecordGapValue03008 : Nat := fullRecordGapCenterValue - 181942

theorem fullRecordGapTerm03008_eq_value :
    recordGapCenter - 181942 = fullRecordGapValue03008 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03008_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03008 (fullRecordGapValue03008 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03008_not_prime : ¬(recordGapCenter - 181942).Prime := by
  rw [fullRecordGapTerm03008_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03008, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03008_fast_pow_mod_ne_one

def fullRecordGapValue03009 : Nat := fullRecordGapCenterValue - 181894

theorem fullRecordGapTerm03009_eq_value :
    recordGapCenter - 181894 = fullRecordGapValue03009 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03009_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03009 (fullRecordGapValue03009 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03009_not_prime : ¬(recordGapCenter - 181894).Prime := by
  rw [fullRecordGapTerm03009_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03009, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03009_fast_pow_mod_ne_one

def fullRecordGapValue03010 : Nat := fullRecordGapCenterValue - 181822

theorem fullRecordGapTerm03010_eq_value :
    recordGapCenter - 181822 = fullRecordGapValue03010 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03010_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03010 (fullRecordGapValue03010 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03010_not_prime : ¬(recordGapCenter - 181822).Prime := by
  rw [fullRecordGapTerm03010_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03010, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03010_fast_pow_mod_ne_one

def fullRecordGapValue03011 : Nat := fullRecordGapCenterValue - 181642

theorem fullRecordGapTerm03011_eq_value :
    recordGapCenter - 181642 = fullRecordGapValue03011 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03011_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03011 (fullRecordGapValue03011 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03011_not_prime : ¬(recordGapCenter - 181642).Prime := by
  rw [fullRecordGapTerm03011_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03011, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03011_fast_pow_mod_ne_one

def fullRecordGapValue03012 : Nat := fullRecordGapCenterValue - 181444

theorem fullRecordGapTerm03012_eq_value :
    recordGapCenter - 181444 = fullRecordGapValue03012 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03012_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03012 (fullRecordGapValue03012 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03012_not_prime : ¬(recordGapCenter - 181444).Prime := by
  rw [fullRecordGapTerm03012_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03012, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03012_fast_pow_mod_ne_one

def fullRecordGapValue03013 : Nat := fullRecordGapCenterValue - 181348

theorem fullRecordGapTerm03013_eq_value :
    recordGapCenter - 181348 = fullRecordGapValue03013 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03013_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03013 (fullRecordGapValue03013 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03013_not_prime : ¬(recordGapCenter - 181348).Prime := by
  rw [fullRecordGapTerm03013_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03013, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03013_fast_pow_mod_ne_one

def fullRecordGapValue03014 : Nat := fullRecordGapCenterValue - 181318

theorem fullRecordGapTerm03014_eq_value :
    recordGapCenter - 181318 = fullRecordGapValue03014 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03014_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03014 (fullRecordGapValue03014 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03014_not_prime : ¬(recordGapCenter - 181318).Prime := by
  rw [fullRecordGapTerm03014_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03014, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03014_fast_pow_mod_ne_one

def fullRecordGapValue03015 : Nat := fullRecordGapCenterValue - 181234

theorem fullRecordGapTerm03015_eq_value :
    recordGapCenter - 181234 = fullRecordGapValue03015 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03015_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03015 (fullRecordGapValue03015 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03015_not_prime : ¬(recordGapCenter - 181234).Prime := by
  rw [fullRecordGapTerm03015_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03015, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03015_fast_pow_mod_ne_one

def fullRecordGapValue03016 : Nat := fullRecordGapCenterValue - 180988

theorem fullRecordGapTerm03016_eq_value :
    recordGapCenter - 180988 = fullRecordGapValue03016 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03016_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03016 (fullRecordGapValue03016 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03016_not_prime : ¬(recordGapCenter - 180988).Prime := by
  rw [fullRecordGapTerm03016_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03016, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03016_fast_pow_mod_ne_one

def fullRecordGapValue03017 : Nat := fullRecordGapCenterValue - 180802

theorem fullRecordGapTerm03017_eq_value :
    recordGapCenter - 180802 = fullRecordGapValue03017 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03017_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03017 (fullRecordGapValue03017 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03017_not_prime : ¬(recordGapCenter - 180802).Prime := by
  rw [fullRecordGapTerm03017_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03017, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03017_fast_pow_mod_ne_one

def fullRecordGapValue03018 : Nat := fullRecordGapCenterValue - 180724

theorem fullRecordGapTerm03018_eq_value :
    recordGapCenter - 180724 = fullRecordGapValue03018 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03018_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03018 (fullRecordGapValue03018 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03018_not_prime : ¬(recordGapCenter - 180724).Prime := by
  rw [fullRecordGapTerm03018_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03018, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03018_fast_pow_mod_ne_one

def fullRecordGapValue03019 : Nat := fullRecordGapCenterValue - 180394

theorem fullRecordGapTerm03019_eq_value :
    recordGapCenter - 180394 = fullRecordGapValue03019 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03019_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03019 (fullRecordGapValue03019 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03019_not_prime : ¬(recordGapCenter - 180394).Prime := by
  rw [fullRecordGapTerm03019_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03019, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03019_fast_pow_mod_ne_one

def fullRecordGapValue03020 : Nat := fullRecordGapCenterValue - 180178

theorem fullRecordGapTerm03020_eq_value :
    recordGapCenter - 180178 = fullRecordGapValue03020 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03020_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03020 (fullRecordGapValue03020 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03020_not_prime : ¬(recordGapCenter - 180178).Prime := by
  rw [fullRecordGapTerm03020_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03020, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03020_fast_pow_mod_ne_one

def fullRecordGapValue03021 : Nat := fullRecordGapCenterValue - 180142

theorem fullRecordGapTerm03021_eq_value :
    recordGapCenter - 180142 = fullRecordGapValue03021 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03021_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03021 (fullRecordGapValue03021 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03021_not_prime : ¬(recordGapCenter - 180142).Prime := by
  rw [fullRecordGapTerm03021_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03021, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03021_fast_pow_mod_ne_one

def fullRecordGapValue03022 : Nat := fullRecordGapCenterValue - 180022

theorem fullRecordGapTerm03022_eq_value :
    recordGapCenter - 180022 = fullRecordGapValue03022 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03022_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03022 (fullRecordGapValue03022 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03022_not_prime : ¬(recordGapCenter - 180022).Prime := by
  rw [fullRecordGapTerm03022_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03022, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03022_fast_pow_mod_ne_one

def fullRecordGapValue03023 : Nat := fullRecordGapCenterValue - 179878

theorem fullRecordGapTerm03023_eq_value :
    recordGapCenter - 179878 = fullRecordGapValue03023 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03023_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03023 (fullRecordGapValue03023 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03023_not_prime : ¬(recordGapCenter - 179878).Prime := by
  rw [fullRecordGapTerm03023_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03023, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03023_fast_pow_mod_ne_one

def fullRecordGapValue03024 : Nat := fullRecordGapCenterValue - 179818

theorem fullRecordGapTerm03024_eq_value :
    recordGapCenter - 179818 = fullRecordGapValue03024 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03024_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03024 (fullRecordGapValue03024 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03024_not_prime : ¬(recordGapCenter - 179818).Prime := by
  rw [fullRecordGapTerm03024_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03024, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03024_fast_pow_mod_ne_one

def fullRecordGapValue03025 : Nat := fullRecordGapCenterValue - 179794

theorem fullRecordGapTerm03025_eq_value :
    recordGapCenter - 179794 = fullRecordGapValue03025 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03025_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03025 (fullRecordGapValue03025 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03025_not_prime : ¬(recordGapCenter - 179794).Prime := by
  rw [fullRecordGapTerm03025_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03025, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03025_fast_pow_mod_ne_one

def fullRecordGapValue03026 : Nat := fullRecordGapCenterValue - 179734

theorem fullRecordGapTerm03026_eq_value :
    recordGapCenter - 179734 = fullRecordGapValue03026 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03026_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03026 (fullRecordGapValue03026 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03026_not_prime : ¬(recordGapCenter - 179734).Prime := by
  rw [fullRecordGapTerm03026_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03026, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03026_fast_pow_mod_ne_one

def fullRecordGapValue03027 : Nat := fullRecordGapCenterValue - 179668

theorem fullRecordGapTerm03027_eq_value :
    recordGapCenter - 179668 = fullRecordGapValue03027 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03027_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03027 (fullRecordGapValue03027 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03027_not_prime : ¬(recordGapCenter - 179668).Prime := by
  rw [fullRecordGapTerm03027_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03027, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03027_fast_pow_mod_ne_one

def fullRecordGapValue03028 : Nat := fullRecordGapCenterValue - 179638

theorem fullRecordGapTerm03028_eq_value :
    recordGapCenter - 179638 = fullRecordGapValue03028 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03028_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03028 (fullRecordGapValue03028 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03028_not_prime : ¬(recordGapCenter - 179638).Prime := by
  rw [fullRecordGapTerm03028_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03028, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03028_fast_pow_mod_ne_one

def fullRecordGapValue03029 : Nat := fullRecordGapCenterValue - 179548

theorem fullRecordGapTerm03029_eq_value :
    recordGapCenter - 179548 = fullRecordGapValue03029 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03029_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03029 (fullRecordGapValue03029 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03029_not_prime : ¬(recordGapCenter - 179548).Prime := by
  rw [fullRecordGapTerm03029_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03029, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03029_fast_pow_mod_ne_one

def fullRecordGapValue03030 : Nat := fullRecordGapCenterValue - 179200

theorem fullRecordGapTerm03030_eq_value :
    recordGapCenter - 179200 = fullRecordGapValue03030 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03030_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03030 (fullRecordGapValue03030 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03030_not_prime : ¬(recordGapCenter - 179200).Prime := by
  rw [fullRecordGapTerm03030_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03030, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03030_fast_pow_mod_ne_one

def fullRecordGapValue03031 : Nat := fullRecordGapCenterValue - 179188

theorem fullRecordGapTerm03031_eq_value :
    recordGapCenter - 179188 = fullRecordGapValue03031 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03031_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03031 (fullRecordGapValue03031 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03031_not_prime : ¬(recordGapCenter - 179188).Prime := by
  rw [fullRecordGapTerm03031_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03031, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03031_fast_pow_mod_ne_one

def fullRecordGapValue03032 : Nat := fullRecordGapCenterValue - 179092

theorem fullRecordGapTerm03032_eq_value :
    recordGapCenter - 179092 = fullRecordGapValue03032 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03032_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03032 (fullRecordGapValue03032 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03032_not_prime : ¬(recordGapCenter - 179092).Prime := by
  rw [fullRecordGapTerm03032_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03032, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03032_fast_pow_mod_ne_one

def fullRecordGapValue03033 : Nat := fullRecordGapCenterValue - 179038

theorem fullRecordGapTerm03033_eq_value :
    recordGapCenter - 179038 = fullRecordGapValue03033 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03033_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03033 (fullRecordGapValue03033 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03033_not_prime : ¬(recordGapCenter - 179038).Prime := by
  rw [fullRecordGapTerm03033_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03033, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03033_fast_pow_mod_ne_one

def fullRecordGapValue03034 : Nat := fullRecordGapCenterValue - 178954

theorem fullRecordGapTerm03034_eq_value :
    recordGapCenter - 178954 = fullRecordGapValue03034 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03034_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03034 (fullRecordGapValue03034 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03034_not_prime : ¬(recordGapCenter - 178954).Prime := by
  rw [fullRecordGapTerm03034_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03034, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03034_fast_pow_mod_ne_one

def fullRecordGapValue03035 : Nat := fullRecordGapCenterValue - 178762

theorem fullRecordGapTerm03035_eq_value :
    recordGapCenter - 178762 = fullRecordGapValue03035 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03035_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03035 (fullRecordGapValue03035 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03035_not_prime : ¬(recordGapCenter - 178762).Prime := by
  rw [fullRecordGapTerm03035_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03035, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03035_fast_pow_mod_ne_one

def fullRecordGapValue03036 : Nat := fullRecordGapCenterValue - 178588

theorem fullRecordGapTerm03036_eq_value :
    recordGapCenter - 178588 = fullRecordGapValue03036 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03036_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03036 (fullRecordGapValue03036 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03036_not_prime : ¬(recordGapCenter - 178588).Prime := by
  rw [fullRecordGapTerm03036_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03036, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03036_fast_pow_mod_ne_one

def fullRecordGapValue03037 : Nat := fullRecordGapCenterValue - 178378

theorem fullRecordGapTerm03037_eq_value :
    recordGapCenter - 178378 = fullRecordGapValue03037 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03037_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03037 (fullRecordGapValue03037 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03037_not_prime : ¬(recordGapCenter - 178378).Prime := by
  rw [fullRecordGapTerm03037_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03037, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03037_fast_pow_mod_ne_one

def fullRecordGapValue03038 : Nat := fullRecordGapCenterValue - 178252

theorem fullRecordGapTerm03038_eq_value :
    recordGapCenter - 178252 = fullRecordGapValue03038 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03038_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03038 (fullRecordGapValue03038 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03038_not_prime : ¬(recordGapCenter - 178252).Prime := by
  rw [fullRecordGapTerm03038_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03038, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03038_fast_pow_mod_ne_one

def fullRecordGapValue03039 : Nat := fullRecordGapCenterValue - 178114

theorem fullRecordGapTerm03039_eq_value :
    recordGapCenter - 178114 = fullRecordGapValue03039 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03039_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03039 (fullRecordGapValue03039 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03039_not_prime : ¬(recordGapCenter - 178114).Prime := by
  rw [fullRecordGapTerm03039_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03039, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03039_fast_pow_mod_ne_one

def fullRecordGapValue03040 : Nat := fullRecordGapCenterValue - 178042

theorem fullRecordGapTerm03040_eq_value :
    recordGapCenter - 178042 = fullRecordGapValue03040 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03040_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03040 (fullRecordGapValue03040 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03040_not_prime : ¬(recordGapCenter - 178042).Prime := by
  rw [fullRecordGapTerm03040_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03040, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03040_fast_pow_mod_ne_one

def fullRecordGapValue03041 : Nat := fullRecordGapCenterValue - 177870

theorem fullRecordGapTerm03041_eq_value :
    recordGapCenter - 177870 = fullRecordGapValue03041 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03041_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03041 (fullRecordGapValue03041 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03041_not_prime : ¬(recordGapCenter - 177870).Prime := by
  rw [fullRecordGapTerm03041_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03041, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03041_fast_pow_mod_ne_one

def fullRecordGapValue03042 : Nat := fullRecordGapCenterValue - 177634

theorem fullRecordGapTerm03042_eq_value :
    recordGapCenter - 177634 = fullRecordGapValue03042 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03042_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03042 (fullRecordGapValue03042 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03042_not_prime : ¬(recordGapCenter - 177634).Prime := by
  rw [fullRecordGapTerm03042_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03042, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03042_fast_pow_mod_ne_one

def fullRecordGapValue03043 : Nat := fullRecordGapCenterValue - 177622

theorem fullRecordGapTerm03043_eq_value :
    recordGapCenter - 177622 = fullRecordGapValue03043 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03043_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03043 (fullRecordGapValue03043 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03043_not_prime : ¬(recordGapCenter - 177622).Prime := by
  rw [fullRecordGapTerm03043_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03043, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03043_fast_pow_mod_ne_one

def fullRecordGapValue03044 : Nat := fullRecordGapCenterValue - 177532

theorem fullRecordGapTerm03044_eq_value :
    recordGapCenter - 177532 = fullRecordGapValue03044 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03044_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03044 (fullRecordGapValue03044 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03044_not_prime : ¬(recordGapCenter - 177532).Prime := by
  rw [fullRecordGapTerm03044_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03044, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03044_fast_pow_mod_ne_one

def fullRecordGapValue03045 : Nat := fullRecordGapCenterValue - 177408

theorem fullRecordGapTerm03045_eq_value :
    recordGapCenter - 177408 = fullRecordGapValue03045 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03045_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03045 (fullRecordGapValue03045 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03045_not_prime : ¬(recordGapCenter - 177408).Prime := by
  rw [fullRecordGapTerm03045_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03045, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03045_fast_pow_mod_ne_one

def fullRecordGapValue03046 : Nat := fullRecordGapCenterValue - 176854

theorem fullRecordGapTerm03046_eq_value :
    recordGapCenter - 176854 = fullRecordGapValue03046 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03046_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03046 (fullRecordGapValue03046 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03046_not_prime : ¬(recordGapCenter - 176854).Prime := by
  rw [fullRecordGapTerm03046_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03046, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03046_fast_pow_mod_ne_one

def fullRecordGapValue03047 : Nat := fullRecordGapCenterValue - 176794

theorem fullRecordGapTerm03047_eq_value :
    recordGapCenter - 176794 = fullRecordGapValue03047 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03047_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03047 (fullRecordGapValue03047 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03047_not_prime : ¬(recordGapCenter - 176794).Prime := by
  rw [fullRecordGapTerm03047_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03047, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03047_fast_pow_mod_ne_one

def fullRecordGapValue03048 : Nat := fullRecordGapCenterValue - 176418

theorem fullRecordGapTerm03048_eq_value :
    recordGapCenter - 176418 = fullRecordGapValue03048 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03048_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03048 (fullRecordGapValue03048 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03048_not_prime : ¬(recordGapCenter - 176418).Prime := by
  rw [fullRecordGapTerm03048_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03048, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03048_fast_pow_mod_ne_one

def fullRecordGapValue03049 : Nat := fullRecordGapCenterValue - 176284

theorem fullRecordGapTerm03049_eq_value :
    recordGapCenter - 176284 = fullRecordGapValue03049 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03049_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03049 (fullRecordGapValue03049 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03049_not_prime : ¬(recordGapCenter - 176284).Prime := by
  rw [fullRecordGapTerm03049_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03049, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03049_fast_pow_mod_ne_one

def fullRecordGapValue03050 : Nat := fullRecordGapCenterValue - 176074

theorem fullRecordGapTerm03050_eq_value :
    recordGapCenter - 176074 = fullRecordGapValue03050 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03050_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03050 (fullRecordGapValue03050 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03050_not_prime : ¬(recordGapCenter - 176074).Prime := by
  rw [fullRecordGapTerm03050_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03050, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03050_fast_pow_mod_ne_one

def fullRecordGapValue03051 : Nat := fullRecordGapCenterValue - 175948

theorem fullRecordGapTerm03051_eq_value :
    recordGapCenter - 175948 = fullRecordGapValue03051 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03051_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03051 (fullRecordGapValue03051 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03051_not_prime : ¬(recordGapCenter - 175948).Prime := by
  rw [fullRecordGapTerm03051_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03051, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03051_fast_pow_mod_ne_one

def fullRecordGapValue03052 : Nat := fullRecordGapCenterValue - 175822

theorem fullRecordGapTerm03052_eq_value :
    recordGapCenter - 175822 = fullRecordGapValue03052 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03052_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03052 (fullRecordGapValue03052 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03052_not_prime : ¬(recordGapCenter - 175822).Prime := by
  rw [fullRecordGapTerm03052_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03052, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03052_fast_pow_mod_ne_one

def fullRecordGapValue03053 : Nat := fullRecordGapCenterValue - 175774

theorem fullRecordGapTerm03053_eq_value :
    recordGapCenter - 175774 = fullRecordGapValue03053 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03053_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03053 (fullRecordGapValue03053 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03053_not_prime : ¬(recordGapCenter - 175774).Prime := by
  rw [fullRecordGapTerm03053_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03053, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03053_fast_pow_mod_ne_one

def fullRecordGapValue03054 : Nat := fullRecordGapCenterValue - 175738

theorem fullRecordGapTerm03054_eq_value :
    recordGapCenter - 175738 = fullRecordGapValue03054 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03054_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03054 (fullRecordGapValue03054 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03054_not_prime : ¬(recordGapCenter - 175738).Prime := by
  rw [fullRecordGapTerm03054_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03054, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03054_fast_pow_mod_ne_one

def fullRecordGapValue03055 : Nat := fullRecordGapCenterValue - 175402

theorem fullRecordGapTerm03055_eq_value :
    recordGapCenter - 175402 = fullRecordGapValue03055 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03055_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03055 (fullRecordGapValue03055 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03055_not_prime : ¬(recordGapCenter - 175402).Prime := by
  rw [fullRecordGapTerm03055_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03055, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03055_fast_pow_mod_ne_one

def fullRecordGapValue03056 : Nat := fullRecordGapCenterValue - 175114

theorem fullRecordGapTerm03056_eq_value :
    recordGapCenter - 175114 = fullRecordGapValue03056 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03056_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03056 (fullRecordGapValue03056 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03056_not_prime : ¬(recordGapCenter - 175114).Prime := by
  rw [fullRecordGapTerm03056_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03056, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03056_fast_pow_mod_ne_one

def fullRecordGapValue03057 : Nat := fullRecordGapCenterValue - 175018

theorem fullRecordGapTerm03057_eq_value :
    recordGapCenter - 175018 = fullRecordGapValue03057 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03057_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03057 (fullRecordGapValue03057 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03057_not_prime : ¬(recordGapCenter - 175018).Prime := by
  rw [fullRecordGapTerm03057_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03057, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03057_fast_pow_mod_ne_one

def fullRecordGapValue03058 : Nat := fullRecordGapCenterValue - 175000

theorem fullRecordGapTerm03058_eq_value :
    recordGapCenter - 175000 = fullRecordGapValue03058 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03058_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03058 (fullRecordGapValue03058 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03058_not_prime : ¬(recordGapCenter - 175000).Prime := by
  rw [fullRecordGapTerm03058_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03058, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03058_fast_pow_mod_ne_one

def fullRecordGapValue03059 : Nat := fullRecordGapCenterValue - 174982

theorem fullRecordGapTerm03059_eq_value :
    recordGapCenter - 174982 = fullRecordGapValue03059 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03059_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03059 (fullRecordGapValue03059 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03059_not_prime : ¬(recordGapCenter - 174982).Prime := by
  rw [fullRecordGapTerm03059_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03059, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03059_fast_pow_mod_ne_one

def fullRecordGapValue03060 : Nat := fullRecordGapCenterValue - 174604

theorem fullRecordGapTerm03060_eq_value :
    recordGapCenter - 174604 = fullRecordGapValue03060 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03060_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03060 (fullRecordGapValue03060 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03060_not_prime : ¬(recordGapCenter - 174604).Prime := by
  rw [fullRecordGapTerm03060_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03060, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03060_fast_pow_mod_ne_one

def fullRecordGapValue03061 : Nat := fullRecordGapCenterValue - 174562

theorem fullRecordGapTerm03061_eq_value :
    recordGapCenter - 174562 = fullRecordGapValue03061 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03061_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03061 (fullRecordGapValue03061 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03061_not_prime : ¬(recordGapCenter - 174562).Prime := by
  rw [fullRecordGapTerm03061_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03061, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03061_fast_pow_mod_ne_one

def fullRecordGapValue03062 : Nat := fullRecordGapCenterValue - 174514

theorem fullRecordGapTerm03062_eq_value :
    recordGapCenter - 174514 = fullRecordGapValue03062 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03062_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03062 (fullRecordGapValue03062 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03062_not_prime : ¬(recordGapCenter - 174514).Prime := by
  rw [fullRecordGapTerm03062_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03062, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03062_fast_pow_mod_ne_one

def fullRecordGapValue03063 : Nat := fullRecordGapCenterValue - 174502

theorem fullRecordGapTerm03063_eq_value :
    recordGapCenter - 174502 = fullRecordGapValue03063 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03063_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03063 (fullRecordGapValue03063 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03063_not_prime : ¬(recordGapCenter - 174502).Prime := by
  rw [fullRecordGapTerm03063_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03063, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03063_fast_pow_mod_ne_one

def fullRecordGapValue03064 : Nat := fullRecordGapCenterValue - 174358

theorem fullRecordGapTerm03064_eq_value :
    recordGapCenter - 174358 = fullRecordGapValue03064 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03064_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03064 (fullRecordGapValue03064 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03064_not_prime : ¬(recordGapCenter - 174358).Prime := by
  rw [fullRecordGapTerm03064_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03064, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03064_fast_pow_mod_ne_one

def fullRecordGapValue03065 : Nat := fullRecordGapCenterValue - 174292

theorem fullRecordGapTerm03065_eq_value :
    recordGapCenter - 174292 = fullRecordGapValue03065 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03065_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03065 (fullRecordGapValue03065 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03065_not_prime : ¬(recordGapCenter - 174292).Prime := by
  rw [fullRecordGapTerm03065_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03065, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03065_fast_pow_mod_ne_one

def fullRecordGapValue03066 : Nat := fullRecordGapCenterValue - 173962

theorem fullRecordGapTerm03066_eq_value :
    recordGapCenter - 173962 = fullRecordGapValue03066 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03066_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03066 (fullRecordGapValue03066 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03066_not_prime : ¬(recordGapCenter - 173962).Prime := by
  rw [fullRecordGapTerm03066_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03066, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03066_fast_pow_mod_ne_one

def fullRecordGapValue03067 : Nat := fullRecordGapCenterValue - 173938

theorem fullRecordGapTerm03067_eq_value :
    recordGapCenter - 173938 = fullRecordGapValue03067 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03067_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03067 (fullRecordGapValue03067 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03067_not_prime : ¬(recordGapCenter - 173938).Prime := by
  rw [fullRecordGapTerm03067_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03067, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03067_fast_pow_mod_ne_one

def fullRecordGapValue03068 : Nat := fullRecordGapCenterValue - 173854

theorem fullRecordGapTerm03068_eq_value :
    recordGapCenter - 173854 = fullRecordGapValue03068 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03068_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03068 (fullRecordGapValue03068 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03068_not_prime : ¬(recordGapCenter - 173854).Prime := by
  rw [fullRecordGapTerm03068_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03068, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03068_fast_pow_mod_ne_one

def fullRecordGapValue03069 : Nat := fullRecordGapCenterValue - 173764

theorem fullRecordGapTerm03069_eq_value :
    recordGapCenter - 173764 = fullRecordGapValue03069 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03069_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03069 (fullRecordGapValue03069 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03069_not_prime : ¬(recordGapCenter - 173764).Prime := by
  rw [fullRecordGapTerm03069_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03069, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03069_fast_pow_mod_ne_one

def fullRecordGapValue03070 : Nat := fullRecordGapCenterValue - 173722

theorem fullRecordGapTerm03070_eq_value :
    recordGapCenter - 173722 = fullRecordGapValue03070 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03070_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03070 (fullRecordGapValue03070 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03070_not_prime : ¬(recordGapCenter - 173722).Prime := by
  rw [fullRecordGapTerm03070_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03070, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03070_fast_pow_mod_ne_one

def fullRecordGapValue03071 : Nat := fullRecordGapCenterValue - 173674

theorem fullRecordGapTerm03071_eq_value :
    recordGapCenter - 173674 = fullRecordGapValue03071 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03071_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03071 (fullRecordGapValue03071 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03071_not_prime : ¬(recordGapCenter - 173674).Prime := by
  rw [fullRecordGapTerm03071_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03071, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03071_fast_pow_mod_ne_one

def fullRecordGapValue03072 : Nat := fullRecordGapCenterValue - 173284

theorem fullRecordGapTerm03072_eq_value :
    recordGapCenter - 173284 = fullRecordGapValue03072 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03072_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03072 (fullRecordGapValue03072 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03072_not_prime : ¬(recordGapCenter - 173284).Prime := by
  rw [fullRecordGapTerm03072_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03072, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03072_fast_pow_mod_ne_one

end PrimeFactorUnimodality
