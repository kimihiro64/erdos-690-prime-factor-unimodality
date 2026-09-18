import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue01793 : Nat := fullRecordGapCenterValue - 310782

theorem fullRecordGapTerm01793_eq_value :
    recordGapCenter - 310782 = fullRecordGapValue01793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01793 (fullRecordGapValue01793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01793_not_prime : ¬(recordGapCenter - 310782).Prime := by
  rw [fullRecordGapTerm01793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01793_fast_pow_mod_ne_one

def fullRecordGapValue01794 : Nat := fullRecordGapCenterValue - 310762

theorem fullRecordGapTerm01794_eq_value :
    recordGapCenter - 310762 = fullRecordGapValue01794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01794 (fullRecordGapValue01794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01794_not_prime : ¬(recordGapCenter - 310762).Prime := by
  rw [fullRecordGapTerm01794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01794_fast_pow_mod_ne_one

def fullRecordGapValue01795 : Nat := fullRecordGapCenterValue - 310438

theorem fullRecordGapTerm01795_eq_value :
    recordGapCenter - 310438 = fullRecordGapValue01795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01795 (fullRecordGapValue01795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01795_not_prime : ¬(recordGapCenter - 310438).Prime := by
  rw [fullRecordGapTerm01795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01795_fast_pow_mod_ne_one

def fullRecordGapValue01796 : Nat := fullRecordGapCenterValue - 310348

theorem fullRecordGapTerm01796_eq_value :
    recordGapCenter - 310348 = fullRecordGapValue01796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01796 (fullRecordGapValue01796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01796_not_prime : ¬(recordGapCenter - 310348).Prime := by
  rw [fullRecordGapTerm01796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01796_fast_pow_mod_ne_one

def fullRecordGapValue01797 : Nat := fullRecordGapCenterValue - 310342

theorem fullRecordGapTerm01797_eq_value :
    recordGapCenter - 310342 = fullRecordGapValue01797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01797 (fullRecordGapValue01797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01797_not_prime : ¬(recordGapCenter - 310342).Prime := by
  rw [fullRecordGapTerm01797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01797_fast_pow_mod_ne_one

def fullRecordGapValue01798 : Nat := fullRecordGapCenterValue - 310228

theorem fullRecordGapTerm01798_eq_value :
    recordGapCenter - 310228 = fullRecordGapValue01798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01798 (fullRecordGapValue01798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01798_not_prime : ¬(recordGapCenter - 310228).Prime := by
  rw [fullRecordGapTerm01798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01798_fast_pow_mod_ne_one

def fullRecordGapValue01799 : Nat := fullRecordGapCenterValue - 310162

theorem fullRecordGapTerm01799_eq_value :
    recordGapCenter - 310162 = fullRecordGapValue01799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01799 (fullRecordGapValue01799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01799_not_prime : ¬(recordGapCenter - 310162).Prime := by
  rw [fullRecordGapTerm01799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01799_fast_pow_mod_ne_one

def fullRecordGapValue01800 : Nat := fullRecordGapCenterValue - 310098

theorem fullRecordGapTerm01800_eq_value :
    recordGapCenter - 310098 = fullRecordGapValue01800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01800 (fullRecordGapValue01800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01800_not_prime : ¬(recordGapCenter - 310098).Prime := by
  rw [fullRecordGapTerm01800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01800_fast_pow_mod_ne_one

def fullRecordGapValue01801 : Nat := fullRecordGapCenterValue - 310084

theorem fullRecordGapTerm01801_eq_value :
    recordGapCenter - 310084 = fullRecordGapValue01801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01801 (fullRecordGapValue01801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01801_not_prime : ¬(recordGapCenter - 310084).Prime := by
  rw [fullRecordGapTerm01801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01801_fast_pow_mod_ne_one

def fullRecordGapValue01802 : Nat := fullRecordGapCenterValue - 310074

theorem fullRecordGapTerm01802_eq_value :
    recordGapCenter - 310074 = fullRecordGapValue01802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01802 (fullRecordGapValue01802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01802_not_prime : ¬(recordGapCenter - 310074).Prime := by
  rw [fullRecordGapTerm01802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01802_fast_pow_mod_ne_one

def fullRecordGapValue01803 : Nat := fullRecordGapCenterValue - 310018

theorem fullRecordGapTerm01803_eq_value :
    recordGapCenter - 310018 = fullRecordGapValue01803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01803 (fullRecordGapValue01803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01803_not_prime : ¬(recordGapCenter - 310018).Prime := by
  rw [fullRecordGapTerm01803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01803_fast_pow_mod_ne_one

def fullRecordGapValue01804 : Nat := fullRecordGapCenterValue - 309882

theorem fullRecordGapTerm01804_eq_value :
    recordGapCenter - 309882 = fullRecordGapValue01804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01804 (fullRecordGapValue01804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01804_not_prime : ¬(recordGapCenter - 309882).Prime := by
  rw [fullRecordGapTerm01804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01804_fast_pow_mod_ne_one

def fullRecordGapValue01805 : Nat := fullRecordGapCenterValue - 309822

theorem fullRecordGapTerm01805_eq_value :
    recordGapCenter - 309822 = fullRecordGapValue01805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01805 (fullRecordGapValue01805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01805_not_prime : ¬(recordGapCenter - 309822).Prime := by
  rw [fullRecordGapTerm01805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01805_fast_pow_mod_ne_one

def fullRecordGapValue01806 : Nat := fullRecordGapCenterValue - 309760

theorem fullRecordGapTerm01806_eq_value :
    recordGapCenter - 309760 = fullRecordGapValue01806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01806 (fullRecordGapValue01806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01806_not_prime : ¬(recordGapCenter - 309760).Prime := by
  rw [fullRecordGapTerm01806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01806_fast_pow_mod_ne_one

def fullRecordGapValue01807 : Nat := fullRecordGapCenterValue - 309682

theorem fullRecordGapTerm01807_eq_value :
    recordGapCenter - 309682 = fullRecordGapValue01807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01807 (fullRecordGapValue01807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01807_not_prime : ¬(recordGapCenter - 309682).Prime := by
  rw [fullRecordGapTerm01807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01807_fast_pow_mod_ne_one

def fullRecordGapValue01808 : Nat := fullRecordGapCenterValue - 309678

theorem fullRecordGapTerm01808_eq_value :
    recordGapCenter - 309678 = fullRecordGapValue01808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01808 (fullRecordGapValue01808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01808_not_prime : ¬(recordGapCenter - 309678).Prime := by
  rw [fullRecordGapTerm01808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01808_fast_pow_mod_ne_one

def fullRecordGapValue01809 : Nat := fullRecordGapCenterValue - 309598

theorem fullRecordGapTerm01809_eq_value :
    recordGapCenter - 309598 = fullRecordGapValue01809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01809 (fullRecordGapValue01809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01809_not_prime : ¬(recordGapCenter - 309598).Prime := by
  rw [fullRecordGapTerm01809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01809_fast_pow_mod_ne_one

def fullRecordGapValue01810 : Nat := fullRecordGapCenterValue - 309574

theorem fullRecordGapTerm01810_eq_value :
    recordGapCenter - 309574 = fullRecordGapValue01810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01810 (fullRecordGapValue01810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01810_not_prime : ¬(recordGapCenter - 309574).Prime := by
  rw [fullRecordGapTerm01810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01810_fast_pow_mod_ne_one

def fullRecordGapValue01811 : Nat := fullRecordGapCenterValue - 309538

theorem fullRecordGapTerm01811_eq_value :
    recordGapCenter - 309538 = fullRecordGapValue01811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01811 (fullRecordGapValue01811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01811_not_prime : ¬(recordGapCenter - 309538).Prime := by
  rw [fullRecordGapTerm01811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01811_fast_pow_mod_ne_one

def fullRecordGapValue01812 : Nat := fullRecordGapCenterValue - 309382

theorem fullRecordGapTerm01812_eq_value :
    recordGapCenter - 309382 = fullRecordGapValue01812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01812 (fullRecordGapValue01812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01812_not_prime : ¬(recordGapCenter - 309382).Prime := by
  rw [fullRecordGapTerm01812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01812_fast_pow_mod_ne_one

def fullRecordGapValue01813 : Nat := fullRecordGapCenterValue - 309378

theorem fullRecordGapTerm01813_eq_value :
    recordGapCenter - 309378 = fullRecordGapValue01813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01813 (fullRecordGapValue01813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01813_not_prime : ¬(recordGapCenter - 309378).Prime := by
  rw [fullRecordGapTerm01813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01813_fast_pow_mod_ne_one

def fullRecordGapValue01814 : Nat := fullRecordGapCenterValue - 309292

theorem fullRecordGapTerm01814_eq_value :
    recordGapCenter - 309292 = fullRecordGapValue01814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01814 (fullRecordGapValue01814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01814_not_prime : ¬(recordGapCenter - 309292).Prime := by
  rw [fullRecordGapTerm01814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01814_fast_pow_mod_ne_one

def fullRecordGapValue01815 : Nat := fullRecordGapCenterValue - 308878

theorem fullRecordGapTerm01815_eq_value :
    recordGapCenter - 308878 = fullRecordGapValue01815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01815 (fullRecordGapValue01815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01815_not_prime : ¬(recordGapCenter - 308878).Prime := by
  rw [fullRecordGapTerm01815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01815_fast_pow_mod_ne_one

def fullRecordGapValue01816 : Nat := fullRecordGapCenterValue - 308874

theorem fullRecordGapTerm01816_eq_value :
    recordGapCenter - 308874 = fullRecordGapValue01816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01816 (fullRecordGapValue01816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01816_not_prime : ¬(recordGapCenter - 308874).Prime := by
  rw [fullRecordGapTerm01816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01816_fast_pow_mod_ne_one

def fullRecordGapValue01817 : Nat := fullRecordGapCenterValue - 308838

theorem fullRecordGapTerm01817_eq_value :
    recordGapCenter - 308838 = fullRecordGapValue01817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01817 (fullRecordGapValue01817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01817_not_prime : ¬(recordGapCenter - 308838).Prime := by
  rw [fullRecordGapTerm01817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01817_fast_pow_mod_ne_one

def fullRecordGapValue01818 : Nat := fullRecordGapCenterValue - 308700

theorem fullRecordGapTerm01818_eq_value :
    recordGapCenter - 308700 = fullRecordGapValue01818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01818 (fullRecordGapValue01818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01818_not_prime : ¬(recordGapCenter - 308700).Prime := by
  rw [fullRecordGapTerm01818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01818_fast_pow_mod_ne_one

def fullRecordGapValue01819 : Nat := fullRecordGapCenterValue - 308668

theorem fullRecordGapTerm01819_eq_value :
    recordGapCenter - 308668 = fullRecordGapValue01819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01819 (fullRecordGapValue01819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01819_not_prime : ¬(recordGapCenter - 308668).Prime := by
  rw [fullRecordGapTerm01819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01819_fast_pow_mod_ne_one

def fullRecordGapValue01820 : Nat := fullRecordGapCenterValue - 308622

theorem fullRecordGapTerm01820_eq_value :
    recordGapCenter - 308622 = fullRecordGapValue01820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01820 (fullRecordGapValue01820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01820_not_prime : ¬(recordGapCenter - 308622).Prime := by
  rw [fullRecordGapTerm01820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01820_fast_pow_mod_ne_one

def fullRecordGapValue01821 : Nat := fullRecordGapCenterValue - 308478

theorem fullRecordGapTerm01821_eq_value :
    recordGapCenter - 308478 = fullRecordGapValue01821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01821 (fullRecordGapValue01821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01821_not_prime : ¬(recordGapCenter - 308478).Prime := by
  rw [fullRecordGapTerm01821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01821_fast_pow_mod_ne_one

def fullRecordGapValue01822 : Nat := fullRecordGapCenterValue - 308314

theorem fullRecordGapTerm01822_eq_value :
    recordGapCenter - 308314 = fullRecordGapValue01822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01822 (fullRecordGapValue01822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01822_not_prime : ¬(recordGapCenter - 308314).Prime := by
  rw [fullRecordGapTerm01822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01822_fast_pow_mod_ne_one

def fullRecordGapValue01823 : Nat := fullRecordGapCenterValue - 308188

theorem fullRecordGapTerm01823_eq_value :
    recordGapCenter - 308188 = fullRecordGapValue01823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01823 (fullRecordGapValue01823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01823_not_prime : ¬(recordGapCenter - 308188).Prime := by
  rw [fullRecordGapTerm01823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01823_fast_pow_mod_ne_one

def fullRecordGapValue01824 : Nat := fullRecordGapCenterValue - 308164

theorem fullRecordGapTerm01824_eq_value :
    recordGapCenter - 308164 = fullRecordGapValue01824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01824 (fullRecordGapValue01824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01824_not_prime : ¬(recordGapCenter - 308164).Prime := by
  rw [fullRecordGapTerm01824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01824_fast_pow_mod_ne_one

def fullRecordGapValue01825 : Nat := fullRecordGapCenterValue - 308122

theorem fullRecordGapTerm01825_eq_value :
    recordGapCenter - 308122 = fullRecordGapValue01825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01825 (fullRecordGapValue01825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01825_not_prime : ¬(recordGapCenter - 308122).Prime := by
  rw [fullRecordGapTerm01825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01825_fast_pow_mod_ne_one

def fullRecordGapValue01826 : Nat := fullRecordGapCenterValue - 308094

theorem fullRecordGapTerm01826_eq_value :
    recordGapCenter - 308094 = fullRecordGapValue01826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01826 (fullRecordGapValue01826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01826_not_prime : ¬(recordGapCenter - 308094).Prime := by
  rw [fullRecordGapTerm01826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01826_fast_pow_mod_ne_one

def fullRecordGapValue01827 : Nat := fullRecordGapCenterValue - 308082

theorem fullRecordGapTerm01827_eq_value :
    recordGapCenter - 308082 = fullRecordGapValue01827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01827 (fullRecordGapValue01827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01827_not_prime : ¬(recordGapCenter - 308082).Prime := by
  rw [fullRecordGapTerm01827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01827_fast_pow_mod_ne_one

def fullRecordGapValue01828 : Nat := fullRecordGapCenterValue - 308068

theorem fullRecordGapTerm01828_eq_value :
    recordGapCenter - 308068 = fullRecordGapValue01828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01828 (fullRecordGapValue01828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01828_not_prime : ¬(recordGapCenter - 308068).Prime := by
  rw [fullRecordGapTerm01828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01828_fast_pow_mod_ne_one

def fullRecordGapValue01829 : Nat := fullRecordGapCenterValue - 308058

theorem fullRecordGapTerm01829_eq_value :
    recordGapCenter - 308058 = fullRecordGapValue01829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01829 (fullRecordGapValue01829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01829_not_prime : ¬(recordGapCenter - 308058).Prime := by
  rw [fullRecordGapTerm01829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01829_fast_pow_mod_ne_one

def fullRecordGapValue01830 : Nat := fullRecordGapCenterValue - 308002

theorem fullRecordGapTerm01830_eq_value :
    recordGapCenter - 308002 = fullRecordGapValue01830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01830 (fullRecordGapValue01830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01830_not_prime : ¬(recordGapCenter - 308002).Prime := by
  rw [fullRecordGapTerm01830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01830_fast_pow_mod_ne_one

def fullRecordGapValue01831 : Nat := fullRecordGapCenterValue - 307852

theorem fullRecordGapTerm01831_eq_value :
    recordGapCenter - 307852 = fullRecordGapValue01831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01831 (fullRecordGapValue01831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01831_not_prime : ¬(recordGapCenter - 307852).Prime := by
  rw [fullRecordGapTerm01831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01831_fast_pow_mod_ne_one

def fullRecordGapValue01832 : Nat := fullRecordGapCenterValue - 307774

theorem fullRecordGapTerm01832_eq_value :
    recordGapCenter - 307774 = fullRecordGapValue01832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01832 (fullRecordGapValue01832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01832_not_prime : ¬(recordGapCenter - 307774).Prime := by
  rw [fullRecordGapTerm01832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01832_fast_pow_mod_ne_one

def fullRecordGapValue01833 : Nat := fullRecordGapCenterValue - 307698

theorem fullRecordGapTerm01833_eq_value :
    recordGapCenter - 307698 = fullRecordGapValue01833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01833 (fullRecordGapValue01833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01833_not_prime : ¬(recordGapCenter - 307698).Prime := by
  rw [fullRecordGapTerm01833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01833_fast_pow_mod_ne_one

def fullRecordGapValue01834 : Nat := fullRecordGapCenterValue - 307578

theorem fullRecordGapTerm01834_eq_value :
    recordGapCenter - 307578 = fullRecordGapValue01834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01834 (fullRecordGapValue01834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01834_not_prime : ¬(recordGapCenter - 307578).Prime := by
  rw [fullRecordGapTerm01834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01834_fast_pow_mod_ne_one

def fullRecordGapValue01835 : Nat := fullRecordGapCenterValue - 307402

theorem fullRecordGapTerm01835_eq_value :
    recordGapCenter - 307402 = fullRecordGapValue01835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01835 (fullRecordGapValue01835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01835_not_prime : ¬(recordGapCenter - 307402).Prime := by
  rw [fullRecordGapTerm01835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01835_fast_pow_mod_ne_one

def fullRecordGapValue01836 : Nat := fullRecordGapCenterValue - 307348

theorem fullRecordGapTerm01836_eq_value :
    recordGapCenter - 307348 = fullRecordGapValue01836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01836 (fullRecordGapValue01836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01836_not_prime : ¬(recordGapCenter - 307348).Prime := by
  rw [fullRecordGapTerm01836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01836_fast_pow_mod_ne_one

def fullRecordGapValue01837 : Nat := fullRecordGapCenterValue - 307282

theorem fullRecordGapTerm01837_eq_value :
    recordGapCenter - 307282 = fullRecordGapValue01837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01837 (fullRecordGapValue01837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01837_not_prime : ¬(recordGapCenter - 307282).Prime := by
  rw [fullRecordGapTerm01837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01837_fast_pow_mod_ne_one

def fullRecordGapValue01838 : Nat := fullRecordGapCenterValue - 307158

theorem fullRecordGapTerm01838_eq_value :
    recordGapCenter - 307158 = fullRecordGapValue01838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01838 (fullRecordGapValue01838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01838_not_prime : ¬(recordGapCenter - 307158).Prime := by
  rw [fullRecordGapTerm01838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01838_fast_pow_mod_ne_one

def fullRecordGapValue01839 : Nat := fullRecordGapCenterValue - 307114

theorem fullRecordGapTerm01839_eq_value :
    recordGapCenter - 307114 = fullRecordGapValue01839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01839 (fullRecordGapValue01839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01839_not_prime : ¬(recordGapCenter - 307114).Prime := by
  rw [fullRecordGapTerm01839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01839_fast_pow_mod_ne_one

def fullRecordGapValue01840 : Nat := fullRecordGapCenterValue - 307018

theorem fullRecordGapTerm01840_eq_value :
    recordGapCenter - 307018 = fullRecordGapValue01840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01840 (fullRecordGapValue01840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01840_not_prime : ¬(recordGapCenter - 307018).Prime := by
  rw [fullRecordGapTerm01840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01840_fast_pow_mod_ne_one

def fullRecordGapValue01841 : Nat := fullRecordGapCenterValue - 306942

theorem fullRecordGapTerm01841_eq_value :
    recordGapCenter - 306942 = fullRecordGapValue01841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01841 (fullRecordGapValue01841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01841_not_prime : ¬(recordGapCenter - 306942).Prime := by
  rw [fullRecordGapTerm01841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01841_fast_pow_mod_ne_one

def fullRecordGapValue01842 : Nat := fullRecordGapCenterValue - 306814

theorem fullRecordGapTerm01842_eq_value :
    recordGapCenter - 306814 = fullRecordGapValue01842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01842 (fullRecordGapValue01842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01842_not_prime : ¬(recordGapCenter - 306814).Prime := by
  rw [fullRecordGapTerm01842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01842_fast_pow_mod_ne_one

def fullRecordGapValue01843 : Nat := fullRecordGapCenterValue - 306798

theorem fullRecordGapTerm01843_eq_value :
    recordGapCenter - 306798 = fullRecordGapValue01843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01843 (fullRecordGapValue01843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01843_not_prime : ¬(recordGapCenter - 306798).Prime := by
  rw [fullRecordGapTerm01843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01843_fast_pow_mod_ne_one

def fullRecordGapValue01844 : Nat := fullRecordGapCenterValue - 306742

theorem fullRecordGapTerm01844_eq_value :
    recordGapCenter - 306742 = fullRecordGapValue01844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01844 (fullRecordGapValue01844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01844_not_prime : ¬(recordGapCenter - 306742).Prime := by
  rw [fullRecordGapTerm01844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01844_fast_pow_mod_ne_one

def fullRecordGapValue01845 : Nat := fullRecordGapCenterValue - 306654

theorem fullRecordGapTerm01845_eq_value :
    recordGapCenter - 306654 = fullRecordGapValue01845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01845 (fullRecordGapValue01845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01845_not_prime : ¬(recordGapCenter - 306654).Prime := by
  rw [fullRecordGapTerm01845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01845_fast_pow_mod_ne_one

def fullRecordGapValue01846 : Nat := fullRecordGapCenterValue - 306604

theorem fullRecordGapTerm01846_eq_value :
    recordGapCenter - 306604 = fullRecordGapValue01846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01846 (fullRecordGapValue01846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01846_not_prime : ¬(recordGapCenter - 306604).Prime := by
  rw [fullRecordGapTerm01846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01846_fast_pow_mod_ne_one

def fullRecordGapValue01847 : Nat := fullRecordGapCenterValue - 306562

theorem fullRecordGapTerm01847_eq_value :
    recordGapCenter - 306562 = fullRecordGapValue01847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01847 (fullRecordGapValue01847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01847_not_prime : ¬(recordGapCenter - 306562).Prime := by
  rw [fullRecordGapTerm01847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01847_fast_pow_mod_ne_one

def fullRecordGapValue01848 : Nat := fullRecordGapCenterValue - 306388

theorem fullRecordGapTerm01848_eq_value :
    recordGapCenter - 306388 = fullRecordGapValue01848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01848 (fullRecordGapValue01848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01848_not_prime : ¬(recordGapCenter - 306388).Prime := by
  rw [fullRecordGapTerm01848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01848_fast_pow_mod_ne_one

def fullRecordGapValue01849 : Nat := fullRecordGapCenterValue - 306274

theorem fullRecordGapTerm01849_eq_value :
    recordGapCenter - 306274 = fullRecordGapValue01849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01849 (fullRecordGapValue01849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01849_not_prime : ¬(recordGapCenter - 306274).Prime := by
  rw [fullRecordGapTerm01849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01849_fast_pow_mod_ne_one

def fullRecordGapValue01850 : Nat := fullRecordGapCenterValue - 306214

theorem fullRecordGapTerm01850_eq_value :
    recordGapCenter - 306214 = fullRecordGapValue01850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01850 (fullRecordGapValue01850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01850_not_prime : ¬(recordGapCenter - 306214).Prime := by
  rw [fullRecordGapTerm01850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01850_fast_pow_mod_ne_one

def fullRecordGapValue01851 : Nat := fullRecordGapCenterValue - 306154

theorem fullRecordGapTerm01851_eq_value :
    recordGapCenter - 306154 = fullRecordGapValue01851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01851 (fullRecordGapValue01851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01851_not_prime : ¬(recordGapCenter - 306154).Prime := by
  rw [fullRecordGapTerm01851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01851_fast_pow_mod_ne_one

def fullRecordGapValue01852 : Nat := fullRecordGapCenterValue - 306142

theorem fullRecordGapTerm01852_eq_value :
    recordGapCenter - 306142 = fullRecordGapValue01852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01852 (fullRecordGapValue01852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01852_not_prime : ¬(recordGapCenter - 306142).Prime := by
  rw [fullRecordGapTerm01852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01852_fast_pow_mod_ne_one

def fullRecordGapValue01853 : Nat := fullRecordGapCenterValue - 306028

theorem fullRecordGapTerm01853_eq_value :
    recordGapCenter - 306028 = fullRecordGapValue01853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01853 (fullRecordGapValue01853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01853_not_prime : ¬(recordGapCenter - 306028).Prime := by
  rw [fullRecordGapTerm01853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01853_fast_pow_mod_ne_one

def fullRecordGapValue01854 : Nat := fullRecordGapCenterValue - 305962

theorem fullRecordGapTerm01854_eq_value :
    recordGapCenter - 305962 = fullRecordGapValue01854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01854 (fullRecordGapValue01854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01854_not_prime : ¬(recordGapCenter - 305962).Prime := by
  rw [fullRecordGapTerm01854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01854_fast_pow_mod_ne_one

def fullRecordGapValue01855 : Nat := fullRecordGapCenterValue - 305934

theorem fullRecordGapTerm01855_eq_value :
    recordGapCenter - 305934 = fullRecordGapValue01855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01855 (fullRecordGapValue01855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01855_not_prime : ¬(recordGapCenter - 305934).Prime := by
  rw [fullRecordGapTerm01855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01855_fast_pow_mod_ne_one

def fullRecordGapValue01856 : Nat := fullRecordGapCenterValue - 305884

theorem fullRecordGapTerm01856_eq_value :
    recordGapCenter - 305884 = fullRecordGapValue01856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01856 (fullRecordGapValue01856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01856_not_prime : ¬(recordGapCenter - 305884).Prime := by
  rw [fullRecordGapTerm01856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01856_fast_pow_mod_ne_one

def fullRecordGapValue01857 : Nat := fullRecordGapCenterValue - 305878

theorem fullRecordGapTerm01857_eq_value :
    recordGapCenter - 305878 = fullRecordGapValue01857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01857 (fullRecordGapValue01857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01857_not_prime : ¬(recordGapCenter - 305878).Prime := by
  rw [fullRecordGapTerm01857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01857_fast_pow_mod_ne_one

def fullRecordGapValue01858 : Nat := fullRecordGapCenterValue - 305818

theorem fullRecordGapTerm01858_eq_value :
    recordGapCenter - 305818 = fullRecordGapValue01858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01858 (fullRecordGapValue01858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01858_not_prime : ¬(recordGapCenter - 305818).Prime := by
  rw [fullRecordGapTerm01858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01858_fast_pow_mod_ne_one

def fullRecordGapValue01859 : Nat := fullRecordGapCenterValue - 305814

theorem fullRecordGapTerm01859_eq_value :
    recordGapCenter - 305814 = fullRecordGapValue01859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01859 (fullRecordGapValue01859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01859_not_prime : ¬(recordGapCenter - 305814).Prime := by
  rw [fullRecordGapTerm01859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01859_fast_pow_mod_ne_one

def fullRecordGapValue01860 : Nat := fullRecordGapCenterValue - 305692

theorem fullRecordGapTerm01860_eq_value :
    recordGapCenter - 305692 = fullRecordGapValue01860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01860 (fullRecordGapValue01860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01860_not_prime : ¬(recordGapCenter - 305692).Prime := by
  rw [fullRecordGapTerm01860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01860_fast_pow_mod_ne_one

def fullRecordGapValue01861 : Nat := fullRecordGapCenterValue - 305638

theorem fullRecordGapTerm01861_eq_value :
    recordGapCenter - 305638 = fullRecordGapValue01861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01861 (fullRecordGapValue01861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01861_not_prime : ¬(recordGapCenter - 305638).Prime := by
  rw [fullRecordGapTerm01861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01861_fast_pow_mod_ne_one

def fullRecordGapValue01862 : Nat := fullRecordGapCenterValue - 305454

theorem fullRecordGapTerm01862_eq_value :
    recordGapCenter - 305454 = fullRecordGapValue01862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01862 (fullRecordGapValue01862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01862_not_prime : ¬(recordGapCenter - 305454).Prime := by
  rw [fullRecordGapTerm01862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01862_fast_pow_mod_ne_one

def fullRecordGapValue01863 : Nat := fullRecordGapCenterValue - 305212

theorem fullRecordGapTerm01863_eq_value :
    recordGapCenter - 305212 = fullRecordGapValue01863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01863 (fullRecordGapValue01863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01863_not_prime : ¬(recordGapCenter - 305212).Prime := by
  rw [fullRecordGapTerm01863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01863_fast_pow_mod_ne_one

def fullRecordGapValue01864 : Nat := fullRecordGapCenterValue - 305202

theorem fullRecordGapTerm01864_eq_value :
    recordGapCenter - 305202 = fullRecordGapValue01864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01864 (fullRecordGapValue01864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01864_not_prime : ¬(recordGapCenter - 305202).Prime := by
  rw [fullRecordGapTerm01864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01864_fast_pow_mod_ne_one

def fullRecordGapValue01865 : Nat := fullRecordGapCenterValue - 305142

theorem fullRecordGapTerm01865_eq_value :
    recordGapCenter - 305142 = fullRecordGapValue01865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01865 (fullRecordGapValue01865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01865_not_prime : ¬(recordGapCenter - 305142).Prime := by
  rw [fullRecordGapTerm01865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01865_fast_pow_mod_ne_one

def fullRecordGapValue01866 : Nat := fullRecordGapCenterValue - 305134

theorem fullRecordGapTerm01866_eq_value :
    recordGapCenter - 305134 = fullRecordGapValue01866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01866 (fullRecordGapValue01866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01866_not_prime : ¬(recordGapCenter - 305134).Prime := by
  rw [fullRecordGapTerm01866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01866_fast_pow_mod_ne_one

def fullRecordGapValue01867 : Nat := fullRecordGapCenterValue - 305062

theorem fullRecordGapTerm01867_eq_value :
    recordGapCenter - 305062 = fullRecordGapValue01867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01867 (fullRecordGapValue01867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01867_not_prime : ¬(recordGapCenter - 305062).Prime := by
  rw [fullRecordGapTerm01867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01867_fast_pow_mod_ne_one

def fullRecordGapValue01868 : Nat := fullRecordGapCenterValue - 305044

theorem fullRecordGapTerm01868_eq_value :
    recordGapCenter - 305044 = fullRecordGapValue01868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01868 (fullRecordGapValue01868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01868_not_prime : ¬(recordGapCenter - 305044).Prime := by
  rw [fullRecordGapTerm01868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01868_fast_pow_mod_ne_one

def fullRecordGapValue01869 : Nat := fullRecordGapCenterValue - 304918

theorem fullRecordGapTerm01869_eq_value :
    recordGapCenter - 304918 = fullRecordGapValue01869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01869 (fullRecordGapValue01869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01869_not_prime : ¬(recordGapCenter - 304918).Prime := by
  rw [fullRecordGapTerm01869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01869_fast_pow_mod_ne_one

def fullRecordGapValue01870 : Nat := fullRecordGapCenterValue - 304834

theorem fullRecordGapTerm01870_eq_value :
    recordGapCenter - 304834 = fullRecordGapValue01870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01870 (fullRecordGapValue01870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01870_not_prime : ¬(recordGapCenter - 304834).Prime := by
  rw [fullRecordGapTerm01870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01870_fast_pow_mod_ne_one

def fullRecordGapValue01871 : Nat := fullRecordGapCenterValue - 304762

theorem fullRecordGapTerm01871_eq_value :
    recordGapCenter - 304762 = fullRecordGapValue01871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01871 (fullRecordGapValue01871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01871_not_prime : ¬(recordGapCenter - 304762).Prime := by
  rw [fullRecordGapTerm01871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01871_fast_pow_mod_ne_one

def fullRecordGapValue01872 : Nat := fullRecordGapCenterValue - 304534

theorem fullRecordGapTerm01872_eq_value :
    recordGapCenter - 304534 = fullRecordGapValue01872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01872 (fullRecordGapValue01872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01872_not_prime : ¬(recordGapCenter - 304534).Prime := by
  rw [fullRecordGapTerm01872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01872_fast_pow_mod_ne_one

def fullRecordGapValue01873 : Nat := fullRecordGapCenterValue - 304518

theorem fullRecordGapTerm01873_eq_value :
    recordGapCenter - 304518 = fullRecordGapValue01873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01873 (fullRecordGapValue01873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01873_not_prime : ¬(recordGapCenter - 304518).Prime := by
  rw [fullRecordGapTerm01873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01873_fast_pow_mod_ne_one

def fullRecordGapValue01874 : Nat := fullRecordGapCenterValue - 304498

theorem fullRecordGapTerm01874_eq_value :
    recordGapCenter - 304498 = fullRecordGapValue01874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01874 (fullRecordGapValue01874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01874_not_prime : ¬(recordGapCenter - 304498).Prime := by
  rw [fullRecordGapTerm01874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01874_fast_pow_mod_ne_one

def fullRecordGapValue01875 : Nat := fullRecordGapCenterValue - 304338

theorem fullRecordGapTerm01875_eq_value :
    recordGapCenter - 304338 = fullRecordGapValue01875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01875 (fullRecordGapValue01875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01875_not_prime : ¬(recordGapCenter - 304338).Prime := by
  rw [fullRecordGapTerm01875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01875_fast_pow_mod_ne_one

def fullRecordGapValue01876 : Nat := fullRecordGapCenterValue - 304324

theorem fullRecordGapTerm01876_eq_value :
    recordGapCenter - 304324 = fullRecordGapValue01876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01876 (fullRecordGapValue01876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01876_not_prime : ¬(recordGapCenter - 304324).Prime := by
  rw [fullRecordGapTerm01876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01876_fast_pow_mod_ne_one

def fullRecordGapValue01877 : Nat := fullRecordGapCenterValue - 304294

theorem fullRecordGapTerm01877_eq_value :
    recordGapCenter - 304294 = fullRecordGapValue01877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01877 (fullRecordGapValue01877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01877_not_prime : ¬(recordGapCenter - 304294).Prime := by
  rw [fullRecordGapTerm01877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01877_fast_pow_mod_ne_one

def fullRecordGapValue01878 : Nat := fullRecordGapCenterValue - 304098

theorem fullRecordGapTerm01878_eq_value :
    recordGapCenter - 304098 = fullRecordGapValue01878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01878 (fullRecordGapValue01878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01878_not_prime : ¬(recordGapCenter - 304098).Prime := by
  rw [fullRecordGapTerm01878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01878_fast_pow_mod_ne_one

def fullRecordGapValue01879 : Nat := fullRecordGapCenterValue - 304078

theorem fullRecordGapTerm01879_eq_value :
    recordGapCenter - 304078 = fullRecordGapValue01879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01879 (fullRecordGapValue01879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01879_not_prime : ¬(recordGapCenter - 304078).Prime := by
  rw [fullRecordGapTerm01879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01879_fast_pow_mod_ne_one

def fullRecordGapValue01880 : Nat := fullRecordGapCenterValue - 303988

theorem fullRecordGapTerm01880_eq_value :
    recordGapCenter - 303988 = fullRecordGapValue01880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01880 (fullRecordGapValue01880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01880_not_prime : ¬(recordGapCenter - 303988).Prime := by
  rw [fullRecordGapTerm01880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01880_fast_pow_mod_ne_one

def fullRecordGapValue01881 : Nat := fullRecordGapCenterValue - 303694

theorem fullRecordGapTerm01881_eq_value :
    recordGapCenter - 303694 = fullRecordGapValue01881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01881 (fullRecordGapValue01881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01881_not_prime : ¬(recordGapCenter - 303694).Prime := by
  rw [fullRecordGapTerm01881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01881_fast_pow_mod_ne_one

def fullRecordGapValue01882 : Nat := fullRecordGapCenterValue - 303652

theorem fullRecordGapTerm01882_eq_value :
    recordGapCenter - 303652 = fullRecordGapValue01882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01882 (fullRecordGapValue01882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01882_not_prime : ¬(recordGapCenter - 303652).Prime := by
  rw [fullRecordGapTerm01882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01882_fast_pow_mod_ne_one

def fullRecordGapValue01883 : Nat := fullRecordGapCenterValue - 303532

theorem fullRecordGapTerm01883_eq_value :
    recordGapCenter - 303532 = fullRecordGapValue01883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01883 (fullRecordGapValue01883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01883_not_prime : ¬(recordGapCenter - 303532).Prime := by
  rw [fullRecordGapTerm01883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01883_fast_pow_mod_ne_one

def fullRecordGapValue01884 : Nat := fullRecordGapCenterValue - 303522

theorem fullRecordGapTerm01884_eq_value :
    recordGapCenter - 303522 = fullRecordGapValue01884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01884 (fullRecordGapValue01884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01884_not_prime : ¬(recordGapCenter - 303522).Prime := by
  rw [fullRecordGapTerm01884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01884_fast_pow_mod_ne_one

def fullRecordGapValue01885 : Nat := fullRecordGapCenterValue - 303412

theorem fullRecordGapTerm01885_eq_value :
    recordGapCenter - 303412 = fullRecordGapValue01885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01885 (fullRecordGapValue01885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01885_not_prime : ¬(recordGapCenter - 303412).Prime := by
  rw [fullRecordGapTerm01885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01885_fast_pow_mod_ne_one

def fullRecordGapValue01886 : Nat := fullRecordGapCenterValue - 303172

theorem fullRecordGapTerm01886_eq_value :
    recordGapCenter - 303172 = fullRecordGapValue01886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01886 (fullRecordGapValue01886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01886_not_prime : ¬(recordGapCenter - 303172).Prime := by
  rw [fullRecordGapTerm01886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01886_fast_pow_mod_ne_one

def fullRecordGapValue01887 : Nat := fullRecordGapCenterValue - 303018

theorem fullRecordGapTerm01887_eq_value :
    recordGapCenter - 303018 = fullRecordGapValue01887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01887 (fullRecordGapValue01887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01887_not_prime : ¬(recordGapCenter - 303018).Prime := by
  rw [fullRecordGapTerm01887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01887_fast_pow_mod_ne_one

def fullRecordGapValue01888 : Nat := fullRecordGapCenterValue - 302754

theorem fullRecordGapTerm01888_eq_value :
    recordGapCenter - 302754 = fullRecordGapValue01888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01888 (fullRecordGapValue01888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01888_not_prime : ¬(recordGapCenter - 302754).Prime := by
  rw [fullRecordGapTerm01888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01888_fast_pow_mod_ne_one

def fullRecordGapValue01889 : Nat := fullRecordGapCenterValue - 302308

theorem fullRecordGapTerm01889_eq_value :
    recordGapCenter - 302308 = fullRecordGapValue01889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01889 (fullRecordGapValue01889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01889_not_prime : ¬(recordGapCenter - 302308).Prime := by
  rw [fullRecordGapTerm01889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01889_fast_pow_mod_ne_one

def fullRecordGapValue01890 : Nat := fullRecordGapCenterValue - 302298

theorem fullRecordGapTerm01890_eq_value :
    recordGapCenter - 302298 = fullRecordGapValue01890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01890 (fullRecordGapValue01890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01890_not_prime : ¬(recordGapCenter - 302298).Prime := by
  rw [fullRecordGapTerm01890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01890_fast_pow_mod_ne_one

def fullRecordGapValue01891 : Nat := fullRecordGapCenterValue - 302154

theorem fullRecordGapTerm01891_eq_value :
    recordGapCenter - 302154 = fullRecordGapValue01891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01891 (fullRecordGapValue01891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01891_not_prime : ¬(recordGapCenter - 302154).Prime := by
  rw [fullRecordGapTerm01891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01891_fast_pow_mod_ne_one

def fullRecordGapValue01892 : Nat := fullRecordGapCenterValue - 301762

theorem fullRecordGapTerm01892_eq_value :
    recordGapCenter - 301762 = fullRecordGapValue01892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01892 (fullRecordGapValue01892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01892_not_prime : ¬(recordGapCenter - 301762).Prime := by
  rw [fullRecordGapTerm01892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01892_fast_pow_mod_ne_one

def fullRecordGapValue01893 : Nat := fullRecordGapCenterValue - 301612

theorem fullRecordGapTerm01893_eq_value :
    recordGapCenter - 301612 = fullRecordGapValue01893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01893 (fullRecordGapValue01893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01893_not_prime : ¬(recordGapCenter - 301612).Prime := by
  rw [fullRecordGapTerm01893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01893_fast_pow_mod_ne_one

def fullRecordGapValue01894 : Nat := fullRecordGapCenterValue - 301564

theorem fullRecordGapTerm01894_eq_value :
    recordGapCenter - 301564 = fullRecordGapValue01894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01894 (fullRecordGapValue01894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01894_not_prime : ¬(recordGapCenter - 301564).Prime := by
  rw [fullRecordGapTerm01894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01894_fast_pow_mod_ne_one

def fullRecordGapValue01895 : Nat := fullRecordGapCenterValue - 301468

theorem fullRecordGapTerm01895_eq_value :
    recordGapCenter - 301468 = fullRecordGapValue01895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01895 (fullRecordGapValue01895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01895_not_prime : ¬(recordGapCenter - 301468).Prime := by
  rw [fullRecordGapTerm01895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01895_fast_pow_mod_ne_one

def fullRecordGapValue01896 : Nat := fullRecordGapCenterValue - 301348

theorem fullRecordGapTerm01896_eq_value :
    recordGapCenter - 301348 = fullRecordGapValue01896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01896 (fullRecordGapValue01896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01896_not_prime : ¬(recordGapCenter - 301348).Prime := by
  rw [fullRecordGapTerm01896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01896_fast_pow_mod_ne_one

def fullRecordGapValue01897 : Nat := fullRecordGapCenterValue - 301234

theorem fullRecordGapTerm01897_eq_value :
    recordGapCenter - 301234 = fullRecordGapValue01897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01897 (fullRecordGapValue01897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01897_not_prime : ¬(recordGapCenter - 301234).Prime := by
  rw [fullRecordGapTerm01897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01897_fast_pow_mod_ne_one

def fullRecordGapValue01898 : Nat := fullRecordGapCenterValue - 301174

theorem fullRecordGapTerm01898_eq_value :
    recordGapCenter - 301174 = fullRecordGapValue01898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01898 (fullRecordGapValue01898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01898_not_prime : ¬(recordGapCenter - 301174).Prime := by
  rw [fullRecordGapTerm01898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01898_fast_pow_mod_ne_one

def fullRecordGapValue01899 : Nat := fullRecordGapCenterValue - 300954

theorem fullRecordGapTerm01899_eq_value :
    recordGapCenter - 300954 = fullRecordGapValue01899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01899 (fullRecordGapValue01899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01899_not_prime : ¬(recordGapCenter - 300954).Prime := by
  rw [fullRecordGapTerm01899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01899_fast_pow_mod_ne_one

def fullRecordGapValue01900 : Nat := fullRecordGapCenterValue - 300862

theorem fullRecordGapTerm01900_eq_value :
    recordGapCenter - 300862 = fullRecordGapValue01900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01900 (fullRecordGapValue01900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01900_not_prime : ¬(recordGapCenter - 300862).Prime := by
  rw [fullRecordGapTerm01900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01900_fast_pow_mod_ne_one

def fullRecordGapValue01901 : Nat := fullRecordGapCenterValue - 300774

theorem fullRecordGapTerm01901_eq_value :
    recordGapCenter - 300774 = fullRecordGapValue01901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01901 (fullRecordGapValue01901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01901_not_prime : ¬(recordGapCenter - 300774).Prime := by
  rw [fullRecordGapTerm01901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01901_fast_pow_mod_ne_one

def fullRecordGapValue01902 : Nat := fullRecordGapCenterValue - 300772

theorem fullRecordGapTerm01902_eq_value :
    recordGapCenter - 300772 = fullRecordGapValue01902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01902 (fullRecordGapValue01902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01902_not_prime : ¬(recordGapCenter - 300772).Prime := by
  rw [fullRecordGapTerm01902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01902_fast_pow_mod_ne_one

def fullRecordGapValue01903 : Nat := fullRecordGapCenterValue - 300754

theorem fullRecordGapTerm01903_eq_value :
    recordGapCenter - 300754 = fullRecordGapValue01903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01903 (fullRecordGapValue01903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01903_not_prime : ¬(recordGapCenter - 300754).Prime := by
  rw [fullRecordGapTerm01903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01903_fast_pow_mod_ne_one

def fullRecordGapValue01904 : Nat := fullRecordGapCenterValue - 300738

theorem fullRecordGapTerm01904_eq_value :
    recordGapCenter - 300738 = fullRecordGapValue01904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01904 (fullRecordGapValue01904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01904_not_prime : ¬(recordGapCenter - 300738).Prime := by
  rw [fullRecordGapTerm01904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01904_fast_pow_mod_ne_one

def fullRecordGapValue01905 : Nat := fullRecordGapCenterValue - 300522

theorem fullRecordGapTerm01905_eq_value :
    recordGapCenter - 300522 = fullRecordGapValue01905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01905 (fullRecordGapValue01905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01905_not_prime : ¬(recordGapCenter - 300522).Prime := by
  rw [fullRecordGapTerm01905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01905_fast_pow_mod_ne_one

def fullRecordGapValue01906 : Nat := fullRecordGapCenterValue - 300442

theorem fullRecordGapTerm01906_eq_value :
    recordGapCenter - 300442 = fullRecordGapValue01906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01906 (fullRecordGapValue01906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01906_not_prime : ¬(recordGapCenter - 300442).Prime := by
  rw [fullRecordGapTerm01906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01906_fast_pow_mod_ne_one

def fullRecordGapValue01907 : Nat := fullRecordGapCenterValue - 300418

theorem fullRecordGapTerm01907_eq_value :
    recordGapCenter - 300418 = fullRecordGapValue01907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01907 (fullRecordGapValue01907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01907_not_prime : ¬(recordGapCenter - 300418).Prime := by
  rw [fullRecordGapTerm01907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01907_fast_pow_mod_ne_one

def fullRecordGapValue01908 : Nat := fullRecordGapCenterValue - 300394

theorem fullRecordGapTerm01908_eq_value :
    recordGapCenter - 300394 = fullRecordGapValue01908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01908 (fullRecordGapValue01908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01908_not_prime : ¬(recordGapCenter - 300394).Prime := by
  rw [fullRecordGapTerm01908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01908_fast_pow_mod_ne_one

def fullRecordGapValue01909 : Nat := fullRecordGapCenterValue - 300178

theorem fullRecordGapTerm01909_eq_value :
    recordGapCenter - 300178 = fullRecordGapValue01909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01909 (fullRecordGapValue01909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01909_not_prime : ¬(recordGapCenter - 300178).Prime := by
  rw [fullRecordGapTerm01909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01909_fast_pow_mod_ne_one

def fullRecordGapValue01910 : Nat := fullRecordGapCenterValue - 300052

theorem fullRecordGapTerm01910_eq_value :
    recordGapCenter - 300052 = fullRecordGapValue01910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01910 (fullRecordGapValue01910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01910_not_prime : ¬(recordGapCenter - 300052).Prime := by
  rw [fullRecordGapTerm01910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01910_fast_pow_mod_ne_one

def fullRecordGapValue01911 : Nat := fullRecordGapCenterValue - 300022

theorem fullRecordGapTerm01911_eq_value :
    recordGapCenter - 300022 = fullRecordGapValue01911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01911 (fullRecordGapValue01911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01911_not_prime : ¬(recordGapCenter - 300022).Prime := by
  rw [fullRecordGapTerm01911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01911_fast_pow_mod_ne_one

def fullRecordGapValue01912 : Nat := fullRecordGapCenterValue - 299938

theorem fullRecordGapTerm01912_eq_value :
    recordGapCenter - 299938 = fullRecordGapValue01912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01912 (fullRecordGapValue01912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01912_not_prime : ¬(recordGapCenter - 299938).Prime := by
  rw [fullRecordGapTerm01912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01912_fast_pow_mod_ne_one

def fullRecordGapValue01913 : Nat := fullRecordGapCenterValue - 299878

theorem fullRecordGapTerm01913_eq_value :
    recordGapCenter - 299878 = fullRecordGapValue01913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01913 (fullRecordGapValue01913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01913_not_prime : ¬(recordGapCenter - 299878).Prime := by
  rw [fullRecordGapTerm01913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01913_fast_pow_mod_ne_one

def fullRecordGapValue01914 : Nat := fullRecordGapCenterValue - 299674

theorem fullRecordGapTerm01914_eq_value :
    recordGapCenter - 299674 = fullRecordGapValue01914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01914 (fullRecordGapValue01914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01914_not_prime : ¬(recordGapCenter - 299674).Prime := by
  rw [fullRecordGapTerm01914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01914_fast_pow_mod_ne_one

def fullRecordGapValue01915 : Nat := fullRecordGapCenterValue - 299658

theorem fullRecordGapTerm01915_eq_value :
    recordGapCenter - 299658 = fullRecordGapValue01915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01915 (fullRecordGapValue01915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01915_not_prime : ¬(recordGapCenter - 299658).Prime := by
  rw [fullRecordGapTerm01915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01915_fast_pow_mod_ne_one

def fullRecordGapValue01916 : Nat := fullRecordGapCenterValue - 299634

theorem fullRecordGapTerm01916_eq_value :
    recordGapCenter - 299634 = fullRecordGapValue01916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01916 (fullRecordGapValue01916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01916_not_prime : ¬(recordGapCenter - 299634).Prime := by
  rw [fullRecordGapTerm01916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01916_fast_pow_mod_ne_one

def fullRecordGapValue01917 : Nat := fullRecordGapCenterValue - 299542

theorem fullRecordGapTerm01917_eq_value :
    recordGapCenter - 299542 = fullRecordGapValue01917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01917 (fullRecordGapValue01917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01917_not_prime : ¬(recordGapCenter - 299542).Prime := by
  rw [fullRecordGapTerm01917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01917_fast_pow_mod_ne_one

def fullRecordGapValue01918 : Nat := fullRecordGapCenterValue - 299518

theorem fullRecordGapTerm01918_eq_value :
    recordGapCenter - 299518 = fullRecordGapValue01918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01918 (fullRecordGapValue01918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01918_not_prime : ¬(recordGapCenter - 299518).Prime := by
  rw [fullRecordGapTerm01918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01918_fast_pow_mod_ne_one

def fullRecordGapValue01919 : Nat := fullRecordGapCenterValue - 299514

theorem fullRecordGapTerm01919_eq_value :
    recordGapCenter - 299514 = fullRecordGapValue01919 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01919_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01919 (fullRecordGapValue01919 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01919_not_prime : ¬(recordGapCenter - 299514).Prime := by
  rw [fullRecordGapTerm01919_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01919, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01919_fast_pow_mod_ne_one

def fullRecordGapValue01920 : Nat := fullRecordGapCenterValue - 299458

theorem fullRecordGapTerm01920_eq_value :
    recordGapCenter - 299458 = fullRecordGapValue01920 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01920_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01920 (fullRecordGapValue01920 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01920_not_prime : ¬(recordGapCenter - 299458).Prime := by
  rw [fullRecordGapTerm01920_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01920, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01920_fast_pow_mod_ne_one

def fullRecordGapValue01921 : Nat := fullRecordGapCenterValue - 299434

theorem fullRecordGapTerm01921_eq_value :
    recordGapCenter - 299434 = fullRecordGapValue01921 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01921_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01921 (fullRecordGapValue01921 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01921_not_prime : ¬(recordGapCenter - 299434).Prime := by
  rw [fullRecordGapTerm01921_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01921, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01921_fast_pow_mod_ne_one

def fullRecordGapValue01922 : Nat := fullRecordGapCenterValue - 299428

theorem fullRecordGapTerm01922_eq_value :
    recordGapCenter - 299428 = fullRecordGapValue01922 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01922_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01922 (fullRecordGapValue01922 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01922_not_prime : ¬(recordGapCenter - 299428).Prime := by
  rw [fullRecordGapTerm01922_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01922, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01922_fast_pow_mod_ne_one

def fullRecordGapValue01923 : Nat := fullRecordGapCenterValue - 299308

theorem fullRecordGapTerm01923_eq_value :
    recordGapCenter - 299308 = fullRecordGapValue01923 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01923_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01923 (fullRecordGapValue01923 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01923_not_prime : ¬(recordGapCenter - 299308).Prime := by
  rw [fullRecordGapTerm01923_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01923, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01923_fast_pow_mod_ne_one

def fullRecordGapValue01924 : Nat := fullRecordGapCenterValue - 299058

theorem fullRecordGapTerm01924_eq_value :
    recordGapCenter - 299058 = fullRecordGapValue01924 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01924_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01924 (fullRecordGapValue01924 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01924_not_prime : ¬(recordGapCenter - 299058).Prime := by
  rw [fullRecordGapTerm01924_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01924, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01924_fast_pow_mod_ne_one

def fullRecordGapValue01925 : Nat := fullRecordGapCenterValue - 298882

theorem fullRecordGapTerm01925_eq_value :
    recordGapCenter - 298882 = fullRecordGapValue01925 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01925_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01925 (fullRecordGapValue01925 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01925_not_prime : ¬(recordGapCenter - 298882).Prime := by
  rw [fullRecordGapTerm01925_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01925, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01925_fast_pow_mod_ne_one

def fullRecordGapValue01926 : Nat := fullRecordGapCenterValue - 298834

theorem fullRecordGapTerm01926_eq_value :
    recordGapCenter - 298834 = fullRecordGapValue01926 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01926_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01926 (fullRecordGapValue01926 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01926_not_prime : ¬(recordGapCenter - 298834).Prime := by
  rw [fullRecordGapTerm01926_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01926, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01926_fast_pow_mod_ne_one

def fullRecordGapValue01927 : Nat := fullRecordGapCenterValue - 298798

theorem fullRecordGapTerm01927_eq_value :
    recordGapCenter - 298798 = fullRecordGapValue01927 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01927_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01927 (fullRecordGapValue01927 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01927_not_prime : ¬(recordGapCenter - 298798).Prime := by
  rw [fullRecordGapTerm01927_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01927, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01927_fast_pow_mod_ne_one

def fullRecordGapValue01928 : Nat := fullRecordGapCenterValue - 298762

theorem fullRecordGapTerm01928_eq_value :
    recordGapCenter - 298762 = fullRecordGapValue01928 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01928_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01928 (fullRecordGapValue01928 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01928_not_prime : ¬(recordGapCenter - 298762).Prime := by
  rw [fullRecordGapTerm01928_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01928, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01928_fast_pow_mod_ne_one

def fullRecordGapValue01929 : Nat := fullRecordGapCenterValue - 298734

theorem fullRecordGapTerm01929_eq_value :
    recordGapCenter - 298734 = fullRecordGapValue01929 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01929_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01929 (fullRecordGapValue01929 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01929_not_prime : ¬(recordGapCenter - 298734).Prime := by
  rw [fullRecordGapTerm01929_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01929, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01929_fast_pow_mod_ne_one

def fullRecordGapValue01930 : Nat := fullRecordGapCenterValue - 298618

theorem fullRecordGapTerm01930_eq_value :
    recordGapCenter - 298618 = fullRecordGapValue01930 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01930_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01930 (fullRecordGapValue01930 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01930_not_prime : ¬(recordGapCenter - 298618).Prime := by
  rw [fullRecordGapTerm01930_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01930, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01930_fast_pow_mod_ne_one

def fullRecordGapValue01931 : Nat := fullRecordGapCenterValue - 298542

theorem fullRecordGapTerm01931_eq_value :
    recordGapCenter - 298542 = fullRecordGapValue01931 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01931_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01931 (fullRecordGapValue01931 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01931_not_prime : ¬(recordGapCenter - 298542).Prime := by
  rw [fullRecordGapTerm01931_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01931, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01931_fast_pow_mod_ne_one

def fullRecordGapValue01932 : Nat := fullRecordGapCenterValue - 298492

theorem fullRecordGapTerm01932_eq_value :
    recordGapCenter - 298492 = fullRecordGapValue01932 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01932_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01932 (fullRecordGapValue01932 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01932_not_prime : ¬(recordGapCenter - 298492).Prime := by
  rw [fullRecordGapTerm01932_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01932, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01932_fast_pow_mod_ne_one

def fullRecordGapValue01933 : Nat := fullRecordGapCenterValue - 298482

theorem fullRecordGapTerm01933_eq_value :
    recordGapCenter - 298482 = fullRecordGapValue01933 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01933_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01933 (fullRecordGapValue01933 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01933_not_prime : ¬(recordGapCenter - 298482).Prime := by
  rw [fullRecordGapTerm01933_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01933, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01933_fast_pow_mod_ne_one

def fullRecordGapValue01934 : Nat := fullRecordGapCenterValue - 298318

theorem fullRecordGapTerm01934_eq_value :
    recordGapCenter - 298318 = fullRecordGapValue01934 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01934_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01934 (fullRecordGapValue01934 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01934_not_prime : ¬(recordGapCenter - 298318).Prime := by
  rw [fullRecordGapTerm01934_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01934, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01934_fast_pow_mod_ne_one

def fullRecordGapValue01935 : Nat := fullRecordGapCenterValue - 298198

theorem fullRecordGapTerm01935_eq_value :
    recordGapCenter - 298198 = fullRecordGapValue01935 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01935_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01935 (fullRecordGapValue01935 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01935_not_prime : ¬(recordGapCenter - 298198).Prime := by
  rw [fullRecordGapTerm01935_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01935, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01935_fast_pow_mod_ne_one

def fullRecordGapValue01936 : Nat := fullRecordGapCenterValue - 298084

theorem fullRecordGapTerm01936_eq_value :
    recordGapCenter - 298084 = fullRecordGapValue01936 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01936_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01936 (fullRecordGapValue01936 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01936_not_prime : ¬(recordGapCenter - 298084).Prime := by
  rw [fullRecordGapTerm01936_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01936, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01936_fast_pow_mod_ne_one

def fullRecordGapValue01937 : Nat := fullRecordGapCenterValue - 297978

theorem fullRecordGapTerm01937_eq_value :
    recordGapCenter - 297978 = fullRecordGapValue01937 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01937_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01937 (fullRecordGapValue01937 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01937_not_prime : ¬(recordGapCenter - 297978).Prime := by
  rw [fullRecordGapTerm01937_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01937, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01937_fast_pow_mod_ne_one

def fullRecordGapValue01938 : Nat := fullRecordGapCenterValue - 297922

theorem fullRecordGapTerm01938_eq_value :
    recordGapCenter - 297922 = fullRecordGapValue01938 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01938_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01938 (fullRecordGapValue01938 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01938_not_prime : ¬(recordGapCenter - 297922).Prime := by
  rw [fullRecordGapTerm01938_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01938, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01938_fast_pow_mod_ne_one

def fullRecordGapValue01939 : Nat := fullRecordGapCenterValue - 297834

theorem fullRecordGapTerm01939_eq_value :
    recordGapCenter - 297834 = fullRecordGapValue01939 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01939_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01939 (fullRecordGapValue01939 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01939_not_prime : ¬(recordGapCenter - 297834).Prime := by
  rw [fullRecordGapTerm01939_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01939, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01939_fast_pow_mod_ne_one

def fullRecordGapValue01940 : Nat := fullRecordGapCenterValue - 297658

theorem fullRecordGapTerm01940_eq_value :
    recordGapCenter - 297658 = fullRecordGapValue01940 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01940_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01940 (fullRecordGapValue01940 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01940_not_prime : ¬(recordGapCenter - 297658).Prime := by
  rw [fullRecordGapTerm01940_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01940, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01940_fast_pow_mod_ne_one

def fullRecordGapValue01941 : Nat := fullRecordGapCenterValue - 297652

theorem fullRecordGapTerm01941_eq_value :
    recordGapCenter - 297652 = fullRecordGapValue01941 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01941_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01941 (fullRecordGapValue01941 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01941_not_prime : ¬(recordGapCenter - 297652).Prime := by
  rw [fullRecordGapTerm01941_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01941, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01941_fast_pow_mod_ne_one

def fullRecordGapValue01942 : Nat := fullRecordGapCenterValue - 297618

theorem fullRecordGapTerm01942_eq_value :
    recordGapCenter - 297618 = fullRecordGapValue01942 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01942_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01942 (fullRecordGapValue01942 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01942_not_prime : ¬(recordGapCenter - 297618).Prime := by
  rw [fullRecordGapTerm01942_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01942, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01942_fast_pow_mod_ne_one

def fullRecordGapValue01943 : Nat := fullRecordGapCenterValue - 297582

theorem fullRecordGapTerm01943_eq_value :
    recordGapCenter - 297582 = fullRecordGapValue01943 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01943_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01943 (fullRecordGapValue01943 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01943_not_prime : ¬(recordGapCenter - 297582).Prime := by
  rw [fullRecordGapTerm01943_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01943, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01943_fast_pow_mod_ne_one

def fullRecordGapValue01944 : Nat := fullRecordGapCenterValue - 297442

theorem fullRecordGapTerm01944_eq_value :
    recordGapCenter - 297442 = fullRecordGapValue01944 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01944_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01944 (fullRecordGapValue01944 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01944_not_prime : ¬(recordGapCenter - 297442).Prime := by
  rw [fullRecordGapTerm01944_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01944, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01944_fast_pow_mod_ne_one

def fullRecordGapValue01945 : Nat := fullRecordGapCenterValue - 297412

theorem fullRecordGapTerm01945_eq_value :
    recordGapCenter - 297412 = fullRecordGapValue01945 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01945_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01945 (fullRecordGapValue01945 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01945_not_prime : ¬(recordGapCenter - 297412).Prime := by
  rw [fullRecordGapTerm01945_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01945, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01945_fast_pow_mod_ne_one

def fullRecordGapValue01946 : Nat := fullRecordGapCenterValue - 297294

theorem fullRecordGapTerm01946_eq_value :
    recordGapCenter - 297294 = fullRecordGapValue01946 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01946_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01946 (fullRecordGapValue01946 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01946_not_prime : ¬(recordGapCenter - 297294).Prime := by
  rw [fullRecordGapTerm01946_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01946, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01946_fast_pow_mod_ne_one

def fullRecordGapValue01947 : Nat := fullRecordGapCenterValue - 297292

theorem fullRecordGapTerm01947_eq_value :
    recordGapCenter - 297292 = fullRecordGapValue01947 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01947_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01947 (fullRecordGapValue01947 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01947_not_prime : ¬(recordGapCenter - 297292).Prime := by
  rw [fullRecordGapTerm01947_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01947, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01947_fast_pow_mod_ne_one

def fullRecordGapValue01948 : Nat := fullRecordGapCenterValue - 297282

theorem fullRecordGapTerm01948_eq_value :
    recordGapCenter - 297282 = fullRecordGapValue01948 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01948_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01948 (fullRecordGapValue01948 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01948_not_prime : ¬(recordGapCenter - 297282).Prime := by
  rw [fullRecordGapTerm01948_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01948, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01948_fast_pow_mod_ne_one

def fullRecordGapValue01949 : Nat := fullRecordGapCenterValue - 297148

theorem fullRecordGapTerm01949_eq_value :
    recordGapCenter - 297148 = fullRecordGapValue01949 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01949_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01949 (fullRecordGapValue01949 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01949_not_prime : ¬(recordGapCenter - 297148).Prime := by
  rw [fullRecordGapTerm01949_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01949, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01949_fast_pow_mod_ne_one

def fullRecordGapValue01950 : Nat := fullRecordGapCenterValue - 297138

theorem fullRecordGapTerm01950_eq_value :
    recordGapCenter - 297138 = fullRecordGapValue01950 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01950_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01950 (fullRecordGapValue01950 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01950_not_prime : ¬(recordGapCenter - 297138).Prime := by
  rw [fullRecordGapTerm01950_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01950, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01950_fast_pow_mod_ne_one

def fullRecordGapValue01951 : Nat := fullRecordGapCenterValue - 297034

theorem fullRecordGapTerm01951_eq_value :
    recordGapCenter - 297034 = fullRecordGapValue01951 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01951_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01951 (fullRecordGapValue01951 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01951_not_prime : ¬(recordGapCenter - 297034).Prime := by
  rw [fullRecordGapTerm01951_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01951, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01951_fast_pow_mod_ne_one

def fullRecordGapValue01952 : Nat := fullRecordGapCenterValue - 296778

theorem fullRecordGapTerm01952_eq_value :
    recordGapCenter - 296778 = fullRecordGapValue01952 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01952_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01952 (fullRecordGapValue01952 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01952_not_prime : ¬(recordGapCenter - 296778).Prime := by
  rw [fullRecordGapTerm01952_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01952, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01952_fast_pow_mod_ne_one

def fullRecordGapValue01953 : Nat := fullRecordGapCenterValue - 296602

theorem fullRecordGapTerm01953_eq_value :
    recordGapCenter - 296602 = fullRecordGapValue01953 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01953_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01953 (fullRecordGapValue01953 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01953_not_prime : ¬(recordGapCenter - 296602).Prime := by
  rw [fullRecordGapTerm01953_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01953, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01953_fast_pow_mod_ne_one

def fullRecordGapValue01954 : Nat := fullRecordGapCenterValue - 296524

theorem fullRecordGapTerm01954_eq_value :
    recordGapCenter - 296524 = fullRecordGapValue01954 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01954_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01954 (fullRecordGapValue01954 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01954_not_prime : ¬(recordGapCenter - 296524).Prime := by
  rw [fullRecordGapTerm01954_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01954, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01954_fast_pow_mod_ne_one

def fullRecordGapValue01955 : Nat := fullRecordGapCenterValue - 296284

theorem fullRecordGapTerm01955_eq_value :
    recordGapCenter - 296284 = fullRecordGapValue01955 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01955_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01955 (fullRecordGapValue01955 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01955_not_prime : ¬(recordGapCenter - 296284).Prime := by
  rw [fullRecordGapTerm01955_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01955, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01955_fast_pow_mod_ne_one

def fullRecordGapValue01956 : Nat := fullRecordGapCenterValue - 296214

theorem fullRecordGapTerm01956_eq_value :
    recordGapCenter - 296214 = fullRecordGapValue01956 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01956_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01956 (fullRecordGapValue01956 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01956_not_prime : ¬(recordGapCenter - 296214).Prime := by
  rw [fullRecordGapTerm01956_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01956, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01956_fast_pow_mod_ne_one

def fullRecordGapValue01957 : Nat := fullRecordGapCenterValue - 296202

theorem fullRecordGapTerm01957_eq_value :
    recordGapCenter - 296202 = fullRecordGapValue01957 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01957_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01957 (fullRecordGapValue01957 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01957_not_prime : ¬(recordGapCenter - 296202).Prime := by
  rw [fullRecordGapTerm01957_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01957, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01957_fast_pow_mod_ne_one

def fullRecordGapValue01958 : Nat := fullRecordGapCenterValue - 296158

theorem fullRecordGapTerm01958_eq_value :
    recordGapCenter - 296158 = fullRecordGapValue01958 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01958_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01958 (fullRecordGapValue01958 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01958_not_prime : ¬(recordGapCenter - 296158).Prime := by
  rw [fullRecordGapTerm01958_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01958, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01958_fast_pow_mod_ne_one

def fullRecordGapValue01959 : Nat := fullRecordGapCenterValue - 295998

theorem fullRecordGapTerm01959_eq_value :
    recordGapCenter - 295998 = fullRecordGapValue01959 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01959_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01959 (fullRecordGapValue01959 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01959_not_prime : ¬(recordGapCenter - 295998).Prime := by
  rw [fullRecordGapTerm01959_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01959, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01959_fast_pow_mod_ne_one

def fullRecordGapValue01960 : Nat := fullRecordGapCenterValue - 295680

theorem fullRecordGapTerm01960_eq_value :
    recordGapCenter - 295680 = fullRecordGapValue01960 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01960_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01960 (fullRecordGapValue01960 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01960_not_prime : ¬(recordGapCenter - 295680).Prime := by
  rw [fullRecordGapTerm01960_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01960, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01960_fast_pow_mod_ne_one

def fullRecordGapValue01961 : Nat := fullRecordGapCenterValue - 295654

theorem fullRecordGapTerm01961_eq_value :
    recordGapCenter - 295654 = fullRecordGapValue01961 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01961_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01961 (fullRecordGapValue01961 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01961_not_prime : ¬(recordGapCenter - 295654).Prime := by
  rw [fullRecordGapTerm01961_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01961, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01961_fast_pow_mod_ne_one

def fullRecordGapValue01962 : Nat := fullRecordGapCenterValue - 295588

theorem fullRecordGapTerm01962_eq_value :
    recordGapCenter - 295588 = fullRecordGapValue01962 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01962_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01962 (fullRecordGapValue01962 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01962_not_prime : ¬(recordGapCenter - 295588).Prime := by
  rw [fullRecordGapTerm01962_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01962, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01962_fast_pow_mod_ne_one

def fullRecordGapValue01963 : Nat := fullRecordGapCenterValue - 295558

theorem fullRecordGapTerm01963_eq_value :
    recordGapCenter - 295558 = fullRecordGapValue01963 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01963_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01963 (fullRecordGapValue01963 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01963_not_prime : ¬(recordGapCenter - 295558).Prime := by
  rw [fullRecordGapTerm01963_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01963, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01963_fast_pow_mod_ne_one

def fullRecordGapValue01964 : Nat := fullRecordGapCenterValue - 295468

theorem fullRecordGapTerm01964_eq_value :
    recordGapCenter - 295468 = fullRecordGapValue01964 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01964_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01964 (fullRecordGapValue01964 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01964_not_prime : ¬(recordGapCenter - 295468).Prime := by
  rw [fullRecordGapTerm01964_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01964, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01964_fast_pow_mod_ne_one

def fullRecordGapValue01965 : Nat := fullRecordGapCenterValue - 295294

theorem fullRecordGapTerm01965_eq_value :
    recordGapCenter - 295294 = fullRecordGapValue01965 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01965_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01965 (fullRecordGapValue01965 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01965_not_prime : ¬(recordGapCenter - 295294).Prime := by
  rw [fullRecordGapTerm01965_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01965, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01965_fast_pow_mod_ne_one

def fullRecordGapValue01966 : Nat := fullRecordGapCenterValue - 295258

theorem fullRecordGapTerm01966_eq_value :
    recordGapCenter - 295258 = fullRecordGapValue01966 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01966_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01966 (fullRecordGapValue01966 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01966_not_prime : ¬(recordGapCenter - 295258).Prime := by
  rw [fullRecordGapTerm01966_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01966, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01966_fast_pow_mod_ne_one

def fullRecordGapValue01967 : Nat := fullRecordGapCenterValue - 295242

theorem fullRecordGapTerm01967_eq_value :
    recordGapCenter - 295242 = fullRecordGapValue01967 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01967_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01967 (fullRecordGapValue01967 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01967_not_prime : ¬(recordGapCenter - 295242).Prime := by
  rw [fullRecordGapTerm01967_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01967, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01967_fast_pow_mod_ne_one

def fullRecordGapValue01968 : Nat := fullRecordGapCenterValue - 295234

theorem fullRecordGapTerm01968_eq_value :
    recordGapCenter - 295234 = fullRecordGapValue01968 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01968_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01968 (fullRecordGapValue01968 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01968_not_prime : ¬(recordGapCenter - 295234).Prime := by
  rw [fullRecordGapTerm01968_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01968, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01968_fast_pow_mod_ne_one

def fullRecordGapValue01969 : Nat := fullRecordGapCenterValue - 295194

theorem fullRecordGapTerm01969_eq_value :
    recordGapCenter - 295194 = fullRecordGapValue01969 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01969_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01969 (fullRecordGapValue01969 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01969_not_prime : ¬(recordGapCenter - 295194).Prime := by
  rw [fullRecordGapTerm01969_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01969, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01969_fast_pow_mod_ne_one

def fullRecordGapValue01970 : Nat := fullRecordGapCenterValue - 295132

theorem fullRecordGapTerm01970_eq_value :
    recordGapCenter - 295132 = fullRecordGapValue01970 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01970_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01970 (fullRecordGapValue01970 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01970_not_prime : ¬(recordGapCenter - 295132).Prime := by
  rw [fullRecordGapTerm01970_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01970, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01970_fast_pow_mod_ne_one

def fullRecordGapValue01971 : Nat := fullRecordGapCenterValue - 295084

theorem fullRecordGapTerm01971_eq_value :
    recordGapCenter - 295084 = fullRecordGapValue01971 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01971_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01971 (fullRecordGapValue01971 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01971_not_prime : ¬(recordGapCenter - 295084).Prime := by
  rw [fullRecordGapTerm01971_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01971, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01971_fast_pow_mod_ne_one

def fullRecordGapValue01972 : Nat := fullRecordGapCenterValue - 294912

theorem fullRecordGapTerm01972_eq_value :
    recordGapCenter - 294912 = fullRecordGapValue01972 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01972_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01972 (fullRecordGapValue01972 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01972_not_prime : ¬(recordGapCenter - 294912).Prime := by
  rw [fullRecordGapTerm01972_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01972, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01972_fast_pow_mod_ne_one

def fullRecordGapValue01973 : Nat := fullRecordGapCenterValue - 294772

theorem fullRecordGapTerm01973_eq_value :
    recordGapCenter - 294772 = fullRecordGapValue01973 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01973_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01973 (fullRecordGapValue01973 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01973_not_prime : ¬(recordGapCenter - 294772).Prime := by
  rw [fullRecordGapTerm01973_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01973, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01973_fast_pow_mod_ne_one

def fullRecordGapValue01974 : Nat := fullRecordGapCenterValue - 294754

theorem fullRecordGapTerm01974_eq_value :
    recordGapCenter - 294754 = fullRecordGapValue01974 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01974_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01974 (fullRecordGapValue01974 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01974_not_prime : ¬(recordGapCenter - 294754).Prime := by
  rw [fullRecordGapTerm01974_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01974, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01974_fast_pow_mod_ne_one

def fullRecordGapValue01975 : Nat := fullRecordGapCenterValue - 294702

theorem fullRecordGapTerm01975_eq_value :
    recordGapCenter - 294702 = fullRecordGapValue01975 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01975_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01975 (fullRecordGapValue01975 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01975_not_prime : ¬(recordGapCenter - 294702).Prime := by
  rw [fullRecordGapTerm01975_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01975, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01975_fast_pow_mod_ne_one

def fullRecordGapValue01976 : Nat := fullRecordGapCenterValue - 294682

theorem fullRecordGapTerm01976_eq_value :
    recordGapCenter - 294682 = fullRecordGapValue01976 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01976_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01976 (fullRecordGapValue01976 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01976_not_prime : ¬(recordGapCenter - 294682).Prime := by
  rw [fullRecordGapTerm01976_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01976, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01976_fast_pow_mod_ne_one

def fullRecordGapValue01977 : Nat := fullRecordGapCenterValue - 294618

theorem fullRecordGapTerm01977_eq_value :
    recordGapCenter - 294618 = fullRecordGapValue01977 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01977_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01977 (fullRecordGapValue01977 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01977_not_prime : ¬(recordGapCenter - 294618).Prime := by
  rw [fullRecordGapTerm01977_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01977, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01977_fast_pow_mod_ne_one

def fullRecordGapValue01978 : Nat := fullRecordGapCenterValue - 294394

theorem fullRecordGapTerm01978_eq_value :
    recordGapCenter - 294394 = fullRecordGapValue01978 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01978_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01978 (fullRecordGapValue01978 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01978_not_prime : ¬(recordGapCenter - 294394).Prime := by
  rw [fullRecordGapTerm01978_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01978, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01978_fast_pow_mod_ne_one

def fullRecordGapValue01979 : Nat := fullRecordGapCenterValue - 294222

theorem fullRecordGapTerm01979_eq_value :
    recordGapCenter - 294222 = fullRecordGapValue01979 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01979_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01979 (fullRecordGapValue01979 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01979_not_prime : ¬(recordGapCenter - 294222).Prime := by
  rw [fullRecordGapTerm01979_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01979, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01979_fast_pow_mod_ne_one

def fullRecordGapValue01980 : Nat := fullRecordGapCenterValue - 294214

theorem fullRecordGapTerm01980_eq_value :
    recordGapCenter - 294214 = fullRecordGapValue01980 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01980_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01980 (fullRecordGapValue01980 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01980_not_prime : ¬(recordGapCenter - 294214).Prime := by
  rw [fullRecordGapTerm01980_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01980, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01980_fast_pow_mod_ne_one

def fullRecordGapValue01981 : Nat := fullRecordGapCenterValue - 294114

theorem fullRecordGapTerm01981_eq_value :
    recordGapCenter - 294114 = fullRecordGapValue01981 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01981_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01981 (fullRecordGapValue01981 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01981_not_prime : ¬(recordGapCenter - 294114).Prime := by
  rw [fullRecordGapTerm01981_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01981, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01981_fast_pow_mod_ne_one

def fullRecordGapValue01982 : Nat := fullRecordGapCenterValue - 294058

theorem fullRecordGapTerm01982_eq_value :
    recordGapCenter - 294058 = fullRecordGapValue01982 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01982_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01982 (fullRecordGapValue01982 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01982_not_prime : ¬(recordGapCenter - 294058).Prime := by
  rw [fullRecordGapTerm01982_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01982, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01982_fast_pow_mod_ne_one

def fullRecordGapValue01983 : Nat := fullRecordGapCenterValue - 294000

theorem fullRecordGapTerm01983_eq_value :
    recordGapCenter - 294000 = fullRecordGapValue01983 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01983_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01983 (fullRecordGapValue01983 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01983_not_prime : ¬(recordGapCenter - 294000).Prime := by
  rw [fullRecordGapTerm01983_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01983, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01983_fast_pow_mod_ne_one

def fullRecordGapValue01984 : Nat := fullRecordGapCenterValue - 293932

theorem fullRecordGapTerm01984_eq_value :
    recordGapCenter - 293932 = fullRecordGapValue01984 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01984_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01984 (fullRecordGapValue01984 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01984_not_prime : ¬(recordGapCenter - 293932).Prime := by
  rw [fullRecordGapTerm01984_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01984, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01984_fast_pow_mod_ne_one

def fullRecordGapValue01985 : Nat := fullRecordGapCenterValue - 293842

theorem fullRecordGapTerm01985_eq_value :
    recordGapCenter - 293842 = fullRecordGapValue01985 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01985_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01985 (fullRecordGapValue01985 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01985_not_prime : ¬(recordGapCenter - 293842).Prime := by
  rw [fullRecordGapTerm01985_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01985, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01985_fast_pow_mod_ne_one

def fullRecordGapValue01986 : Nat := fullRecordGapCenterValue - 293838

theorem fullRecordGapTerm01986_eq_value :
    recordGapCenter - 293838 = fullRecordGapValue01986 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01986_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01986 (fullRecordGapValue01986 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01986_not_prime : ¬(recordGapCenter - 293838).Prime := by
  rw [fullRecordGapTerm01986_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01986, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01986_fast_pow_mod_ne_one

def fullRecordGapValue01987 : Nat := fullRecordGapCenterValue - 293718

theorem fullRecordGapTerm01987_eq_value :
    recordGapCenter - 293718 = fullRecordGapValue01987 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01987_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01987 (fullRecordGapValue01987 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01987_not_prime : ¬(recordGapCenter - 293718).Prime := by
  rw [fullRecordGapTerm01987_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01987, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01987_fast_pow_mod_ne_one

def fullRecordGapValue01988 : Nat := fullRecordGapCenterValue - 293668

theorem fullRecordGapTerm01988_eq_value :
    recordGapCenter - 293668 = fullRecordGapValue01988 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01988_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01988 (fullRecordGapValue01988 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01988_not_prime : ¬(recordGapCenter - 293668).Prime := by
  rw [fullRecordGapTerm01988_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01988, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01988_fast_pow_mod_ne_one

def fullRecordGapValue01989 : Nat := fullRecordGapCenterValue - 293614

theorem fullRecordGapTerm01989_eq_value :
    recordGapCenter - 293614 = fullRecordGapValue01989 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01989_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01989 (fullRecordGapValue01989 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01989_not_prime : ¬(recordGapCenter - 293614).Prime := by
  rw [fullRecordGapTerm01989_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01989, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01989_fast_pow_mod_ne_one

def fullRecordGapValue01990 : Nat := fullRecordGapCenterValue - 293452

theorem fullRecordGapTerm01990_eq_value :
    recordGapCenter - 293452 = fullRecordGapValue01990 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01990_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01990 (fullRecordGapValue01990 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01990_not_prime : ¬(recordGapCenter - 293452).Prime := by
  rw [fullRecordGapTerm01990_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01990, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01990_fast_pow_mod_ne_one

def fullRecordGapValue01991 : Nat := fullRecordGapCenterValue - 293334

theorem fullRecordGapTerm01991_eq_value :
    recordGapCenter - 293334 = fullRecordGapValue01991 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01991_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01991 (fullRecordGapValue01991 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01991_not_prime : ¬(recordGapCenter - 293334).Prime := by
  rw [fullRecordGapTerm01991_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01991, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01991_fast_pow_mod_ne_one

def fullRecordGapValue01992 : Nat := fullRecordGapCenterValue - 293298

theorem fullRecordGapTerm01992_eq_value :
    recordGapCenter - 293298 = fullRecordGapValue01992 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01992_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01992 (fullRecordGapValue01992 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01992_not_prime : ¬(recordGapCenter - 293298).Prime := by
  rw [fullRecordGapTerm01992_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01992, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01992_fast_pow_mod_ne_one

def fullRecordGapValue01993 : Nat := fullRecordGapCenterValue - 293278

theorem fullRecordGapTerm01993_eq_value :
    recordGapCenter - 293278 = fullRecordGapValue01993 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01993_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01993 (fullRecordGapValue01993 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01993_not_prime : ¬(recordGapCenter - 293278).Prime := by
  rw [fullRecordGapTerm01993_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01993, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01993_fast_pow_mod_ne_one

def fullRecordGapValue01994 : Nat := fullRecordGapCenterValue - 293218

theorem fullRecordGapTerm01994_eq_value :
    recordGapCenter - 293218 = fullRecordGapValue01994 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01994_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01994 (fullRecordGapValue01994 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01994_not_prime : ¬(recordGapCenter - 293218).Prime := by
  rw [fullRecordGapTerm01994_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01994, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01994_fast_pow_mod_ne_one

def fullRecordGapValue01995 : Nat := fullRecordGapCenterValue - 293214

theorem fullRecordGapTerm01995_eq_value :
    recordGapCenter - 293214 = fullRecordGapValue01995 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01995_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01995 (fullRecordGapValue01995 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01995_not_prime : ¬(recordGapCenter - 293214).Prime := by
  rw [fullRecordGapTerm01995_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01995, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01995_fast_pow_mod_ne_one

def fullRecordGapValue01996 : Nat := fullRecordGapCenterValue - 292542

theorem fullRecordGapTerm01996_eq_value :
    recordGapCenter - 292542 = fullRecordGapValue01996 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01996_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01996 (fullRecordGapValue01996 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01996_not_prime : ¬(recordGapCenter - 292542).Prime := by
  rw [fullRecordGapTerm01996_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01996, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01996_fast_pow_mod_ne_one

def fullRecordGapValue01997 : Nat := fullRecordGapCenterValue - 292282

theorem fullRecordGapTerm01997_eq_value :
    recordGapCenter - 292282 = fullRecordGapValue01997 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01997_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01997 (fullRecordGapValue01997 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01997_not_prime : ¬(recordGapCenter - 292282).Prime := by
  rw [fullRecordGapTerm01997_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01997, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01997_fast_pow_mod_ne_one

def fullRecordGapValue01998 : Nat := fullRecordGapCenterValue - 292074

theorem fullRecordGapTerm01998_eq_value :
    recordGapCenter - 292074 = fullRecordGapValue01998 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01998_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01998 (fullRecordGapValue01998 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01998_not_prime : ¬(recordGapCenter - 292074).Prime := by
  rw [fullRecordGapTerm01998_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01998, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01998_fast_pow_mod_ne_one

def fullRecordGapValue01999 : Nat := fullRecordGapCenterValue - 292018

theorem fullRecordGapTerm01999_eq_value :
    recordGapCenter - 292018 = fullRecordGapValue01999 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01999_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01999 (fullRecordGapValue01999 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01999_not_prime : ¬(recordGapCenter - 292018).Prime := by
  rw [fullRecordGapTerm01999_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01999, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01999_fast_pow_mod_ne_one

def fullRecordGapValue02000 : Nat := fullRecordGapCenterValue - 291748

theorem fullRecordGapTerm02000_eq_value :
    recordGapCenter - 291748 = fullRecordGapValue02000 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02000_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02000 (fullRecordGapValue02000 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02000_not_prime : ¬(recordGapCenter - 291748).Prime := by
  rw [fullRecordGapTerm02000_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02000, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02000_fast_pow_mod_ne_one

def fullRecordGapValue02001 : Nat := fullRecordGapCenterValue - 291738

theorem fullRecordGapTerm02001_eq_value :
    recordGapCenter - 291738 = fullRecordGapValue02001 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02001_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02001 (fullRecordGapValue02001 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02001_not_prime : ¬(recordGapCenter - 291738).Prime := by
  rw [fullRecordGapTerm02001_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02001, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02001_fast_pow_mod_ne_one

def fullRecordGapValue02002 : Nat := fullRecordGapCenterValue - 291598

theorem fullRecordGapTerm02002_eq_value :
    recordGapCenter - 291598 = fullRecordGapValue02002 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02002_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02002 (fullRecordGapValue02002 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02002_not_prime : ¬(recordGapCenter - 291598).Prime := by
  rw [fullRecordGapTerm02002_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02002, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02002_fast_pow_mod_ne_one

def fullRecordGapValue02003 : Nat := fullRecordGapCenterValue - 291358

theorem fullRecordGapTerm02003_eq_value :
    recordGapCenter - 291358 = fullRecordGapValue02003 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02003_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02003 (fullRecordGapValue02003 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02003_not_prime : ¬(recordGapCenter - 291358).Prime := by
  rw [fullRecordGapTerm02003_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02003, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02003_fast_pow_mod_ne_one

def fullRecordGapValue02004 : Nat := fullRecordGapCenterValue - 291322

theorem fullRecordGapTerm02004_eq_value :
    recordGapCenter - 291322 = fullRecordGapValue02004 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02004_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02004 (fullRecordGapValue02004 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02004_not_prime : ¬(recordGapCenter - 291322).Prime := by
  rw [fullRecordGapTerm02004_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02004, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02004_fast_pow_mod_ne_one

def fullRecordGapValue02005 : Nat := fullRecordGapCenterValue - 291274

theorem fullRecordGapTerm02005_eq_value :
    recordGapCenter - 291274 = fullRecordGapValue02005 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02005_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02005 (fullRecordGapValue02005 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02005_not_prime : ¬(recordGapCenter - 291274).Prime := by
  rw [fullRecordGapTerm02005_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02005, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02005_fast_pow_mod_ne_one

def fullRecordGapValue02006 : Nat := fullRecordGapCenterValue - 291268

theorem fullRecordGapTerm02006_eq_value :
    recordGapCenter - 291268 = fullRecordGapValue02006 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02006_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02006 (fullRecordGapValue02006 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02006_not_prime : ¬(recordGapCenter - 291268).Prime := by
  rw [fullRecordGapTerm02006_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02006, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02006_fast_pow_mod_ne_one

def fullRecordGapValue02007 : Nat := fullRecordGapCenterValue - 291234

theorem fullRecordGapTerm02007_eq_value :
    recordGapCenter - 291234 = fullRecordGapValue02007 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02007_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02007 (fullRecordGapValue02007 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02007_not_prime : ¬(recordGapCenter - 291234).Prime := by
  rw [fullRecordGapTerm02007_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02007, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02007_fast_pow_mod_ne_one

def fullRecordGapValue02008 : Nat := fullRecordGapCenterValue - 291202

theorem fullRecordGapTerm02008_eq_value :
    recordGapCenter - 291202 = fullRecordGapValue02008 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02008_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02008 (fullRecordGapValue02008 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02008_not_prime : ¬(recordGapCenter - 291202).Prime := by
  rw [fullRecordGapTerm02008_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02008, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02008_fast_pow_mod_ne_one

def fullRecordGapValue02009 : Nat := fullRecordGapCenterValue - 291198

theorem fullRecordGapTerm02009_eq_value :
    recordGapCenter - 291198 = fullRecordGapValue02009 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02009_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02009 (fullRecordGapValue02009 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02009_not_prime : ¬(recordGapCenter - 291198).Prime := by
  rw [fullRecordGapTerm02009_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02009, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02009_fast_pow_mod_ne_one

def fullRecordGapValue02010 : Nat := fullRecordGapCenterValue - 291178

theorem fullRecordGapTerm02010_eq_value :
    recordGapCenter - 291178 = fullRecordGapValue02010 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02010_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02010 (fullRecordGapValue02010 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02010_not_prime : ¬(recordGapCenter - 291178).Prime := by
  rw [fullRecordGapTerm02010_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02010, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02010_fast_pow_mod_ne_one

def fullRecordGapValue02011 : Nat := fullRecordGapCenterValue - 291154

theorem fullRecordGapTerm02011_eq_value :
    recordGapCenter - 291154 = fullRecordGapValue02011 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02011_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02011 (fullRecordGapValue02011 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02011_not_prime : ¬(recordGapCenter - 291154).Prime := by
  rw [fullRecordGapTerm02011_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02011, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02011_fast_pow_mod_ne_one

def fullRecordGapValue02012 : Nat := fullRecordGapCenterValue - 291052

theorem fullRecordGapTerm02012_eq_value :
    recordGapCenter - 291052 = fullRecordGapValue02012 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02012_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02012 (fullRecordGapValue02012 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02012_not_prime : ¬(recordGapCenter - 291052).Prime := by
  rw [fullRecordGapTerm02012_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02012, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02012_fast_pow_mod_ne_one

def fullRecordGapValue02013 : Nat := fullRecordGapCenterValue - 291022

theorem fullRecordGapTerm02013_eq_value :
    recordGapCenter - 291022 = fullRecordGapValue02013 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02013_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02013 (fullRecordGapValue02013 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02013_not_prime : ¬(recordGapCenter - 291022).Prime := by
  rw [fullRecordGapTerm02013_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02013, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02013_fast_pow_mod_ne_one

def fullRecordGapValue02014 : Nat := fullRecordGapCenterValue - 290922

theorem fullRecordGapTerm02014_eq_value :
    recordGapCenter - 290922 = fullRecordGapValue02014 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02014_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02014 (fullRecordGapValue02014 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02014_not_prime : ¬(recordGapCenter - 290922).Prime := by
  rw [fullRecordGapTerm02014_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02014, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02014_fast_pow_mod_ne_one

def fullRecordGapValue02015 : Nat := fullRecordGapCenterValue - 290908

theorem fullRecordGapTerm02015_eq_value :
    recordGapCenter - 290908 = fullRecordGapValue02015 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02015_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02015 (fullRecordGapValue02015 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02015_not_prime : ¬(recordGapCenter - 290908).Prime := by
  rw [fullRecordGapTerm02015_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02015, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02015_fast_pow_mod_ne_one

def fullRecordGapValue02016 : Nat := fullRecordGapCenterValue - 290694

theorem fullRecordGapTerm02016_eq_value :
    recordGapCenter - 290694 = fullRecordGapValue02016 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02016_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02016 (fullRecordGapValue02016 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02016_not_prime : ¬(recordGapCenter - 290694).Prime := by
  rw [fullRecordGapTerm02016_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02016, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02016_fast_pow_mod_ne_one

def fullRecordGapValue02017 : Nat := fullRecordGapCenterValue - 290622

theorem fullRecordGapTerm02017_eq_value :
    recordGapCenter - 290622 = fullRecordGapValue02017 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02017_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02017 (fullRecordGapValue02017 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02017_not_prime : ¬(recordGapCenter - 290622).Prime := by
  rw [fullRecordGapTerm02017_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02017, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02017_fast_pow_mod_ne_one

def fullRecordGapValue02018 : Nat := fullRecordGapCenterValue - 290614

theorem fullRecordGapTerm02018_eq_value :
    recordGapCenter - 290614 = fullRecordGapValue02018 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02018_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02018 (fullRecordGapValue02018 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02018_not_prime : ¬(recordGapCenter - 290614).Prime := by
  rw [fullRecordGapTerm02018_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02018, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02018_fast_pow_mod_ne_one

def fullRecordGapValue02019 : Nat := fullRecordGapCenterValue - 290572

theorem fullRecordGapTerm02019_eq_value :
    recordGapCenter - 290572 = fullRecordGapValue02019 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02019_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02019 (fullRecordGapValue02019 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02019_not_prime : ¬(recordGapCenter - 290572).Prime := by
  rw [fullRecordGapTerm02019_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02019, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02019_fast_pow_mod_ne_one

def fullRecordGapValue02020 : Nat := fullRecordGapCenterValue - 290518

theorem fullRecordGapTerm02020_eq_value :
    recordGapCenter - 290518 = fullRecordGapValue02020 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02020_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02020 (fullRecordGapValue02020 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02020_not_prime : ¬(recordGapCenter - 290518).Prime := by
  rw [fullRecordGapTerm02020_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02020, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02020_fast_pow_mod_ne_one

def fullRecordGapValue02021 : Nat := fullRecordGapCenterValue - 290478

theorem fullRecordGapTerm02021_eq_value :
    recordGapCenter - 290478 = fullRecordGapValue02021 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02021_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02021 (fullRecordGapValue02021 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02021_not_prime : ¬(recordGapCenter - 290478).Prime := by
  rw [fullRecordGapTerm02021_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02021, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02021_fast_pow_mod_ne_one

def fullRecordGapValue02022 : Nat := fullRecordGapCenterValue - 290454

theorem fullRecordGapTerm02022_eq_value :
    recordGapCenter - 290454 = fullRecordGapValue02022 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02022_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02022 (fullRecordGapValue02022 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02022_not_prime : ¬(recordGapCenter - 290454).Prime := by
  rw [fullRecordGapTerm02022_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02022, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02022_fast_pow_mod_ne_one

def fullRecordGapValue02023 : Nat := fullRecordGapCenterValue - 290442

theorem fullRecordGapTerm02023_eq_value :
    recordGapCenter - 290442 = fullRecordGapValue02023 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02023_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02023 (fullRecordGapValue02023 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02023_not_prime : ¬(recordGapCenter - 290442).Prime := by
  rw [fullRecordGapTerm02023_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02023, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02023_fast_pow_mod_ne_one

def fullRecordGapValue02024 : Nat := fullRecordGapCenterValue - 290400

theorem fullRecordGapTerm02024_eq_value :
    recordGapCenter - 290400 = fullRecordGapValue02024 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02024_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02024 (fullRecordGapValue02024 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02024_not_prime : ¬(recordGapCenter - 290400).Prime := by
  rw [fullRecordGapTerm02024_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02024, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02024_fast_pow_mod_ne_one

def fullRecordGapValue02025 : Nat := fullRecordGapCenterValue - 290304

theorem fullRecordGapTerm02025_eq_value :
    recordGapCenter - 290304 = fullRecordGapValue02025 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02025_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02025 (fullRecordGapValue02025 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02025_not_prime : ¬(recordGapCenter - 290304).Prime := by
  rw [fullRecordGapTerm02025_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02025, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02025_fast_pow_mod_ne_one

def fullRecordGapValue02026 : Nat := fullRecordGapCenterValue - 290218

theorem fullRecordGapTerm02026_eq_value :
    recordGapCenter - 290218 = fullRecordGapValue02026 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02026_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02026 (fullRecordGapValue02026 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02026_not_prime : ¬(recordGapCenter - 290218).Prime := by
  rw [fullRecordGapTerm02026_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02026, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02026_fast_pow_mod_ne_one

def fullRecordGapValue02027 : Nat := fullRecordGapCenterValue - 290182

theorem fullRecordGapTerm02027_eq_value :
    recordGapCenter - 290182 = fullRecordGapValue02027 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02027_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02027 (fullRecordGapValue02027 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02027_not_prime : ¬(recordGapCenter - 290182).Prime := by
  rw [fullRecordGapTerm02027_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02027, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02027_fast_pow_mod_ne_one

def fullRecordGapValue02028 : Nat := fullRecordGapCenterValue - 290062

theorem fullRecordGapTerm02028_eq_value :
    recordGapCenter - 290062 = fullRecordGapValue02028 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02028_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02028 (fullRecordGapValue02028 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02028_not_prime : ¬(recordGapCenter - 290062).Prime := by
  rw [fullRecordGapTerm02028_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02028, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02028_fast_pow_mod_ne_one

def fullRecordGapValue02029 : Nat := fullRecordGapCenterValue - 289972

theorem fullRecordGapTerm02029_eq_value :
    recordGapCenter - 289972 = fullRecordGapValue02029 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02029_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02029 (fullRecordGapValue02029 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02029_not_prime : ¬(recordGapCenter - 289972).Prime := by
  rw [fullRecordGapTerm02029_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02029, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02029_fast_pow_mod_ne_one

def fullRecordGapValue02030 : Nat := fullRecordGapCenterValue - 289834

theorem fullRecordGapTerm02030_eq_value :
    recordGapCenter - 289834 = fullRecordGapValue02030 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02030_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02030 (fullRecordGapValue02030 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02030_not_prime : ¬(recordGapCenter - 289834).Prime := by
  rw [fullRecordGapTerm02030_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02030, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02030_fast_pow_mod_ne_one

def fullRecordGapValue02031 : Nat := fullRecordGapCenterValue - 289798

theorem fullRecordGapTerm02031_eq_value :
    recordGapCenter - 289798 = fullRecordGapValue02031 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02031_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02031 (fullRecordGapValue02031 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02031_not_prime : ¬(recordGapCenter - 289798).Prime := by
  rw [fullRecordGapTerm02031_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02031, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02031_fast_pow_mod_ne_one

def fullRecordGapValue02032 : Nat := fullRecordGapCenterValue - 289684

theorem fullRecordGapTerm02032_eq_value :
    recordGapCenter - 289684 = fullRecordGapValue02032 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02032_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02032 (fullRecordGapValue02032 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02032_not_prime : ¬(recordGapCenter - 289684).Prime := by
  rw [fullRecordGapTerm02032_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02032, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02032_fast_pow_mod_ne_one

def fullRecordGapValue02033 : Nat := fullRecordGapCenterValue - 289582

theorem fullRecordGapTerm02033_eq_value :
    recordGapCenter - 289582 = fullRecordGapValue02033 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02033_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02033 (fullRecordGapValue02033 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02033_not_prime : ¬(recordGapCenter - 289582).Prime := by
  rw [fullRecordGapTerm02033_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02033, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02033_fast_pow_mod_ne_one

def fullRecordGapValue02034 : Nat := fullRecordGapCenterValue - 289558

theorem fullRecordGapTerm02034_eq_value :
    recordGapCenter - 289558 = fullRecordGapValue02034 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02034_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02034 (fullRecordGapValue02034 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02034_not_prime : ¬(recordGapCenter - 289558).Prime := by
  rw [fullRecordGapTerm02034_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02034, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02034_fast_pow_mod_ne_one

def fullRecordGapValue02035 : Nat := fullRecordGapCenterValue - 289554

theorem fullRecordGapTerm02035_eq_value :
    recordGapCenter - 289554 = fullRecordGapValue02035 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02035_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02035 (fullRecordGapValue02035 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02035_not_prime : ¬(recordGapCenter - 289554).Prime := by
  rw [fullRecordGapTerm02035_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02035, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02035_fast_pow_mod_ne_one

def fullRecordGapValue02036 : Nat := fullRecordGapCenterValue - 289482

theorem fullRecordGapTerm02036_eq_value :
    recordGapCenter - 289482 = fullRecordGapValue02036 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02036_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02036 (fullRecordGapValue02036 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02036_not_prime : ¬(recordGapCenter - 289482).Prime := by
  rw [fullRecordGapTerm02036_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02036, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02036_fast_pow_mod_ne_one

def fullRecordGapValue02037 : Nat := fullRecordGapCenterValue - 289468

theorem fullRecordGapTerm02037_eq_value :
    recordGapCenter - 289468 = fullRecordGapValue02037 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02037_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02037 (fullRecordGapValue02037 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02037_not_prime : ¬(recordGapCenter - 289468).Prime := by
  rw [fullRecordGapTerm02037_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02037, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02037_fast_pow_mod_ne_one

def fullRecordGapValue02038 : Nat := fullRecordGapCenterValue - 289462

theorem fullRecordGapTerm02038_eq_value :
    recordGapCenter - 289462 = fullRecordGapValue02038 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02038_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02038 (fullRecordGapValue02038 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02038_not_prime : ¬(recordGapCenter - 289462).Prime := by
  rw [fullRecordGapTerm02038_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02038, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02038_fast_pow_mod_ne_one

def fullRecordGapValue02039 : Nat := fullRecordGapCenterValue - 289438

theorem fullRecordGapTerm02039_eq_value :
    recordGapCenter - 289438 = fullRecordGapValue02039 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02039_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02039 (fullRecordGapValue02039 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02039_not_prime : ¬(recordGapCenter - 289438).Prime := by
  rw [fullRecordGapTerm02039_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02039, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02039_fast_pow_mod_ne_one

def fullRecordGapValue02040 : Nat := fullRecordGapCenterValue - 289434

theorem fullRecordGapTerm02040_eq_value :
    recordGapCenter - 289434 = fullRecordGapValue02040 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02040_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02040 (fullRecordGapValue02040 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02040_not_prime : ¬(recordGapCenter - 289434).Prime := by
  rw [fullRecordGapTerm02040_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02040, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02040_fast_pow_mod_ne_one

def fullRecordGapValue02041 : Nat := fullRecordGapCenterValue - 289342

theorem fullRecordGapTerm02041_eq_value :
    recordGapCenter - 289342 = fullRecordGapValue02041 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02041_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02041 (fullRecordGapValue02041 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02041_not_prime : ¬(recordGapCenter - 289342).Prime := by
  rw [fullRecordGapTerm02041_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02041, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02041_fast_pow_mod_ne_one

def fullRecordGapValue02042 : Nat := fullRecordGapCenterValue - 289252

theorem fullRecordGapTerm02042_eq_value :
    recordGapCenter - 289252 = fullRecordGapValue02042 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02042_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02042 (fullRecordGapValue02042 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02042_not_prime : ¬(recordGapCenter - 289252).Prime := by
  rw [fullRecordGapTerm02042_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02042, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02042_fast_pow_mod_ne_one

def fullRecordGapValue02043 : Nat := fullRecordGapCenterValue - 289228

theorem fullRecordGapTerm02043_eq_value :
    recordGapCenter - 289228 = fullRecordGapValue02043 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02043_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02043 (fullRecordGapValue02043 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02043_not_prime : ¬(recordGapCenter - 289228).Prime := by
  rw [fullRecordGapTerm02043_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02043, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02043_fast_pow_mod_ne_one

def fullRecordGapValue02044 : Nat := fullRecordGapCenterValue - 289222

theorem fullRecordGapTerm02044_eq_value :
    recordGapCenter - 289222 = fullRecordGapValue02044 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02044_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02044 (fullRecordGapValue02044 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02044_not_prime : ¬(recordGapCenter - 289222).Prime := by
  rw [fullRecordGapTerm02044_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02044, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02044_fast_pow_mod_ne_one

def fullRecordGapValue02045 : Nat := fullRecordGapCenterValue - 289182

theorem fullRecordGapTerm02045_eq_value :
    recordGapCenter - 289182 = fullRecordGapValue02045 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02045_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02045 (fullRecordGapValue02045 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02045_not_prime : ¬(recordGapCenter - 289182).Prime := by
  rw [fullRecordGapTerm02045_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02045, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02045_fast_pow_mod_ne_one

def fullRecordGapValue02046 : Nat := fullRecordGapCenterValue - 289158

theorem fullRecordGapTerm02046_eq_value :
    recordGapCenter - 289158 = fullRecordGapValue02046 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02046_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02046 (fullRecordGapValue02046 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02046_not_prime : ¬(recordGapCenter - 289158).Prime := by
  rw [fullRecordGapTerm02046_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02046, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02046_fast_pow_mod_ne_one

def fullRecordGapValue02047 : Nat := fullRecordGapCenterValue - 289074

theorem fullRecordGapTerm02047_eq_value :
    recordGapCenter - 289074 = fullRecordGapValue02047 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02047_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02047 (fullRecordGapValue02047 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02047_not_prime : ¬(recordGapCenter - 289074).Prime := by
  rw [fullRecordGapTerm02047_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02047, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02047_fast_pow_mod_ne_one

def fullRecordGapValue02048 : Nat := fullRecordGapCenterValue - 289012

theorem fullRecordGapTerm02048_eq_value :
    recordGapCenter - 289012 = fullRecordGapValue02048 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02048_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02048 (fullRecordGapValue02048 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02048_not_prime : ¬(recordGapCenter - 289012).Prime := by
  rw [fullRecordGapTerm02048_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02048, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02048_fast_pow_mod_ne_one

end PrimeFactorUnimodality
