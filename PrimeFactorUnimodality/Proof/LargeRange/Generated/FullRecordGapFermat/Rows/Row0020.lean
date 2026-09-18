import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue04865 : Nat := fullRecordGapCenterValue + 207938

theorem fullRecordGapTerm04865_eq_value :
    recordGapCenter + 207938 = fullRecordGapValue04865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04865 (fullRecordGapValue04865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04865_not_prime : ¬(recordGapCenter + 207938).Prime := by
  rw [fullRecordGapTerm04865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04865_fast_pow_mod_ne_one

def fullRecordGapValue04866 : Nat := fullRecordGapCenterValue + 207986

theorem fullRecordGapTerm04866_eq_value :
    recordGapCenter + 207986 = fullRecordGapValue04866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04866 (fullRecordGapValue04866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04866_not_prime : ¬(recordGapCenter + 207986).Prime := by
  rw [fullRecordGapTerm04866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04866_fast_pow_mod_ne_one

def fullRecordGapValue04867 : Nat := fullRecordGapCenterValue + 208118

theorem fullRecordGapTerm04867_eq_value :
    recordGapCenter + 208118 = fullRecordGapValue04867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04867 (fullRecordGapValue04867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04867_not_prime : ¬(recordGapCenter + 208118).Prime := by
  rw [fullRecordGapTerm04867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04867_fast_pow_mod_ne_one

def fullRecordGapValue04868 : Nat := fullRecordGapCenterValue + 208268

theorem fullRecordGapTerm04868_eq_value :
    recordGapCenter + 208268 = fullRecordGapValue04868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04868 (fullRecordGapValue04868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04868_not_prime : ¬(recordGapCenter + 208268).Prime := by
  rw [fullRecordGapTerm04868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04868_fast_pow_mod_ne_one

def fullRecordGapValue04869 : Nat := fullRecordGapCenterValue + 208346

theorem fullRecordGapTerm04869_eq_value :
    recordGapCenter + 208346 = fullRecordGapValue04869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04869 (fullRecordGapValue04869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04869_not_prime : ¬(recordGapCenter + 208346).Prime := by
  rw [fullRecordGapTerm04869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04869_fast_pow_mod_ne_one

def fullRecordGapValue04870 : Nat := fullRecordGapCenterValue + 208412

theorem fullRecordGapTerm04870_eq_value :
    recordGapCenter + 208412 = fullRecordGapValue04870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04870 (fullRecordGapValue04870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04870_not_prime : ¬(recordGapCenter + 208412).Prime := by
  rw [fullRecordGapTerm04870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04870_fast_pow_mod_ne_one

def fullRecordGapValue04871 : Nat := fullRecordGapCenterValue + 208652

theorem fullRecordGapTerm04871_eq_value :
    recordGapCenter + 208652 = fullRecordGapValue04871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04871 (fullRecordGapValue04871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04871_not_prime : ¬(recordGapCenter + 208652).Prime := by
  rw [fullRecordGapTerm04871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04871_fast_pow_mod_ne_one

def fullRecordGapValue04872 : Nat := fullRecordGapCenterValue + 208892

theorem fullRecordGapTerm04872_eq_value :
    recordGapCenter + 208892 = fullRecordGapValue04872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04872 (fullRecordGapValue04872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04872_not_prime : ¬(recordGapCenter + 208892).Prime := by
  rw [fullRecordGapTerm04872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04872_fast_pow_mod_ne_one

def fullRecordGapValue04873 : Nat := fullRecordGapCenterValue + 209088

theorem fullRecordGapTerm04873_eq_value :
    recordGapCenter + 209088 = fullRecordGapValue04873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04873 (fullRecordGapValue04873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04873_not_prime : ¬(recordGapCenter + 209088).Prime := by
  rw [fullRecordGapTerm04873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04873_fast_pow_mod_ne_one

def fullRecordGapValue04874 : Nat := fullRecordGapCenterValue + 209102

theorem fullRecordGapTerm04874_eq_value :
    recordGapCenter + 209102 = fullRecordGapValue04874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04874 (fullRecordGapValue04874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04874_not_prime : ¬(recordGapCenter + 209102).Prime := by
  rw [fullRecordGapTerm04874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04874_fast_pow_mod_ne_one

def fullRecordGapValue04875 : Nat := fullRecordGapCenterValue + 209156

theorem fullRecordGapTerm04875_eq_value :
    recordGapCenter + 209156 = fullRecordGapValue04875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04875 (fullRecordGapValue04875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04875_not_prime : ¬(recordGapCenter + 209156).Prime := by
  rw [fullRecordGapTerm04875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04875_fast_pow_mod_ne_one

def fullRecordGapValue04876 : Nat := fullRecordGapCenterValue + 209252

theorem fullRecordGapTerm04876_eq_value :
    recordGapCenter + 209252 = fullRecordGapValue04876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04876 (fullRecordGapValue04876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04876_not_prime : ¬(recordGapCenter + 209252).Prime := by
  rw [fullRecordGapTerm04876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04876_fast_pow_mod_ne_one

def fullRecordGapValue04877 : Nat := fullRecordGapCenterValue + 209318

theorem fullRecordGapTerm04877_eq_value :
    recordGapCenter + 209318 = fullRecordGapValue04877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04877 (fullRecordGapValue04877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04877_not_prime : ¬(recordGapCenter + 209318).Prime := by
  rw [fullRecordGapTerm04877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04877_fast_pow_mod_ne_one

def fullRecordGapValue04878 : Nat := fullRecordGapCenterValue + 209366

theorem fullRecordGapTerm04878_eq_value :
    recordGapCenter + 209366 = fullRecordGapValue04878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04878 (fullRecordGapValue04878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04878_not_prime : ¬(recordGapCenter + 209366).Prime := by
  rw [fullRecordGapTerm04878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04878_fast_pow_mod_ne_one

def fullRecordGapValue04879 : Nat := fullRecordGapCenterValue + 209522

theorem fullRecordGapTerm04879_eq_value :
    recordGapCenter + 209522 = fullRecordGapValue04879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04879 (fullRecordGapValue04879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04879_not_prime : ¬(recordGapCenter + 209522).Prime := by
  rw [fullRecordGapTerm04879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04879_fast_pow_mod_ne_one

def fullRecordGapValue04880 : Nat := fullRecordGapCenterValue + 209732

theorem fullRecordGapTerm04880_eq_value :
    recordGapCenter + 209732 = fullRecordGapValue04880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04880 (fullRecordGapValue04880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04880_not_prime : ¬(recordGapCenter + 209732).Prime := by
  rw [fullRecordGapTerm04880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04880_fast_pow_mod_ne_one

def fullRecordGapValue04881 : Nat := fullRecordGapCenterValue + 209822

theorem fullRecordGapTerm04881_eq_value :
    recordGapCenter + 209822 = fullRecordGapValue04881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04881 (fullRecordGapValue04881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04881_not_prime : ¬(recordGapCenter + 209822).Prime := by
  rw [fullRecordGapTerm04881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04881_fast_pow_mod_ne_one

def fullRecordGapValue04882 : Nat := fullRecordGapCenterValue + 209906

theorem fullRecordGapTerm04882_eq_value :
    recordGapCenter + 209906 = fullRecordGapValue04882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04882 (fullRecordGapValue04882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04882_not_prime : ¬(recordGapCenter + 209906).Prime := by
  rw [fullRecordGapTerm04882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04882_fast_pow_mod_ne_one

def fullRecordGapValue04883 : Nat := fullRecordGapCenterValue + 209952

theorem fullRecordGapTerm04883_eq_value :
    recordGapCenter + 209952 = fullRecordGapValue04883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04883 (fullRecordGapValue04883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04883_not_prime : ¬(recordGapCenter + 209952).Prime := by
  rw [fullRecordGapTerm04883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04883_fast_pow_mod_ne_one

def fullRecordGapValue04884 : Nat := fullRecordGapCenterValue + 210038

theorem fullRecordGapTerm04884_eq_value :
    recordGapCenter + 210038 = fullRecordGapValue04884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04884 (fullRecordGapValue04884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04884_not_prime : ¬(recordGapCenter + 210038).Prime := by
  rw [fullRecordGapTerm04884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04884_fast_pow_mod_ne_one

def fullRecordGapValue04885 : Nat := fullRecordGapCenterValue + 210068

theorem fullRecordGapTerm04885_eq_value :
    recordGapCenter + 210068 = fullRecordGapValue04885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04885 (fullRecordGapValue04885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04885_not_prime : ¬(recordGapCenter + 210068).Prime := by
  rw [fullRecordGapTerm04885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04885_fast_pow_mod_ne_one

def fullRecordGapValue04886 : Nat := fullRecordGapCenterValue + 210212

theorem fullRecordGapTerm04886_eq_value :
    recordGapCenter + 210212 = fullRecordGapValue04886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04886 (fullRecordGapValue04886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04886_not_prime : ¬(recordGapCenter + 210212).Prime := by
  rw [fullRecordGapTerm04886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04886_fast_pow_mod_ne_one

def fullRecordGapValue04887 : Nat := fullRecordGapCenterValue + 210458

theorem fullRecordGapTerm04887_eq_value :
    recordGapCenter + 210458 = fullRecordGapValue04887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04887 (fullRecordGapValue04887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04887_not_prime : ¬(recordGapCenter + 210458).Prime := by
  rw [fullRecordGapTerm04887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04887_fast_pow_mod_ne_one

def fullRecordGapValue04888 : Nat := fullRecordGapCenterValue + 210506

theorem fullRecordGapTerm04888_eq_value :
    recordGapCenter + 210506 = fullRecordGapValue04888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04888 (fullRecordGapValue04888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04888_not_prime : ¬(recordGapCenter + 210506).Prime := by
  rw [fullRecordGapTerm04888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04888_fast_pow_mod_ne_one

def fullRecordGapValue04889 : Nat := fullRecordGapCenterValue + 210662

theorem fullRecordGapTerm04889_eq_value :
    recordGapCenter + 210662 = fullRecordGapValue04889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04889 (fullRecordGapValue04889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04889_not_prime : ¬(recordGapCenter + 210662).Prime := by
  rw [fullRecordGapTerm04889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04889_fast_pow_mod_ne_one

def fullRecordGapValue04890 : Nat := fullRecordGapCenterValue + 210746

theorem fullRecordGapTerm04890_eq_value :
    recordGapCenter + 210746 = fullRecordGapValue04890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04890 (fullRecordGapValue04890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04890_not_prime : ¬(recordGapCenter + 210746).Prime := by
  rw [fullRecordGapTerm04890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04890_fast_pow_mod_ne_one

def fullRecordGapValue04891 : Nat := fullRecordGapCenterValue + 210758

theorem fullRecordGapTerm04891_eq_value :
    recordGapCenter + 210758 = fullRecordGapValue04891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04891 (fullRecordGapValue04891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04891_not_prime : ¬(recordGapCenter + 210758).Prime := by
  rw [fullRecordGapTerm04891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04891_fast_pow_mod_ne_one

def fullRecordGapValue04892 : Nat := fullRecordGapCenterValue + 210788

theorem fullRecordGapTerm04892_eq_value :
    recordGapCenter + 210788 = fullRecordGapValue04892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04892 (fullRecordGapValue04892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04892_not_prime : ¬(recordGapCenter + 210788).Prime := by
  rw [fullRecordGapTerm04892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04892_fast_pow_mod_ne_one

def fullRecordGapValue04893 : Nat := fullRecordGapCenterValue + 211082

theorem fullRecordGapTerm04893_eq_value :
    recordGapCenter + 211082 = fullRecordGapValue04893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04893 (fullRecordGapValue04893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04893_not_prime : ¬(recordGapCenter + 211082).Prime := by
  rw [fullRecordGapTerm04893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04893_fast_pow_mod_ne_one

def fullRecordGapValue04894 : Nat := fullRecordGapCenterValue + 211226

theorem fullRecordGapTerm04894_eq_value :
    recordGapCenter + 211226 = fullRecordGapValue04894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04894 (fullRecordGapValue04894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04894_not_prime : ¬(recordGapCenter + 211226).Prime := by
  rw [fullRecordGapTerm04894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04894_fast_pow_mod_ne_one

def fullRecordGapValue04895 : Nat := fullRecordGapCenterValue + 211298

theorem fullRecordGapTerm04895_eq_value :
    recordGapCenter + 211298 = fullRecordGapValue04895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04895 (fullRecordGapValue04895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04895_not_prime : ¬(recordGapCenter + 211298).Prime := by
  rw [fullRecordGapTerm04895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04895_fast_pow_mod_ne_one

def fullRecordGapValue04896 : Nat := fullRecordGapCenterValue + 211382

theorem fullRecordGapTerm04896_eq_value :
    recordGapCenter + 211382 = fullRecordGapValue04896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04896 (fullRecordGapValue04896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04896_not_prime : ¬(recordGapCenter + 211382).Prime := by
  rw [fullRecordGapTerm04896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04896_fast_pow_mod_ne_one

def fullRecordGapValue04897 : Nat := fullRecordGapCenterValue + 211538

theorem fullRecordGapTerm04897_eq_value :
    recordGapCenter + 211538 = fullRecordGapValue04897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04897 (fullRecordGapValue04897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04897_not_prime : ¬(recordGapCenter + 211538).Prime := by
  rw [fullRecordGapTerm04897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04897_fast_pow_mod_ne_one

def fullRecordGapValue04898 : Nat := fullRecordGapCenterValue + 211748

theorem fullRecordGapTerm04898_eq_value :
    recordGapCenter + 211748 = fullRecordGapValue04898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04898 (fullRecordGapValue04898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04898_not_prime : ¬(recordGapCenter + 211748).Prime := by
  rw [fullRecordGapTerm04898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04898_fast_pow_mod_ne_one

def fullRecordGapValue04899 : Nat := fullRecordGapCenterValue + 211766

theorem fullRecordGapTerm04899_eq_value :
    recordGapCenter + 211766 = fullRecordGapValue04899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04899 (fullRecordGapValue04899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04899_not_prime : ¬(recordGapCenter + 211766).Prime := by
  rw [fullRecordGapTerm04899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04899_fast_pow_mod_ne_one

def fullRecordGapValue04900 : Nat := fullRecordGapCenterValue + 211886

theorem fullRecordGapTerm04900_eq_value :
    recordGapCenter + 211886 = fullRecordGapValue04900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04900 (fullRecordGapValue04900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04900_not_prime : ¬(recordGapCenter + 211886).Prime := by
  rw [fullRecordGapTerm04900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04900_fast_pow_mod_ne_one

def fullRecordGapValue04901 : Nat := fullRecordGapCenterValue + 212066

theorem fullRecordGapTerm04901_eq_value :
    recordGapCenter + 212066 = fullRecordGapValue04901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04901 (fullRecordGapValue04901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04901_not_prime : ¬(recordGapCenter + 212066).Prime := by
  rw [fullRecordGapTerm04901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04901_fast_pow_mod_ne_one

def fullRecordGapValue04902 : Nat := fullRecordGapCenterValue + 212276

theorem fullRecordGapTerm04902_eq_value :
    recordGapCenter + 212276 = fullRecordGapValue04902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04902 (fullRecordGapValue04902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04902_not_prime : ¬(recordGapCenter + 212276).Prime := by
  rw [fullRecordGapTerm04902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04902_fast_pow_mod_ne_one

def fullRecordGapValue04903 : Nat := fullRecordGapCenterValue + 212438

theorem fullRecordGapTerm04903_eq_value :
    recordGapCenter + 212438 = fullRecordGapValue04903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04903 (fullRecordGapValue04903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04903_not_prime : ¬(recordGapCenter + 212438).Prime := by
  rw [fullRecordGapTerm04903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04903_fast_pow_mod_ne_one

def fullRecordGapValue04904 : Nat := fullRecordGapCenterValue + 212486

theorem fullRecordGapTerm04904_eq_value :
    recordGapCenter + 212486 = fullRecordGapValue04904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04904 (fullRecordGapValue04904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04904_not_prime : ¬(recordGapCenter + 212486).Prime := by
  rw [fullRecordGapTerm04904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04904_fast_pow_mod_ne_one

def fullRecordGapValue04905 : Nat := fullRecordGapCenterValue + 212522

theorem fullRecordGapTerm04905_eq_value :
    recordGapCenter + 212522 = fullRecordGapValue04905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04905 (fullRecordGapValue04905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04905_not_prime : ¬(recordGapCenter + 212522).Prime := by
  rw [fullRecordGapTerm04905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04905_fast_pow_mod_ne_one

def fullRecordGapValue04906 : Nat := fullRecordGapCenterValue + 212546

theorem fullRecordGapTerm04906_eq_value :
    recordGapCenter + 212546 = fullRecordGapValue04906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04906 (fullRecordGapValue04906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04906_not_prime : ¬(recordGapCenter + 212546).Prime := by
  rw [fullRecordGapTerm04906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04906_fast_pow_mod_ne_one

def fullRecordGapValue04907 : Nat := fullRecordGapCenterValue + 212606

theorem fullRecordGapTerm04907_eq_value :
    recordGapCenter + 212606 = fullRecordGapValue04907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04907 (fullRecordGapValue04907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04907_not_prime : ¬(recordGapCenter + 212606).Prime := by
  rw [fullRecordGapTerm04907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04907_fast_pow_mod_ne_one

def fullRecordGapValue04908 : Nat := fullRecordGapCenterValue + 212642

theorem fullRecordGapTerm04908_eq_value :
    recordGapCenter + 212642 = fullRecordGapValue04908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04908 (fullRecordGapValue04908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04908_not_prime : ¬(recordGapCenter + 212642).Prime := by
  rw [fullRecordGapTerm04908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04908_fast_pow_mod_ne_one

def fullRecordGapValue04909 : Nat := fullRecordGapCenterValue + 213062

theorem fullRecordGapTerm04909_eq_value :
    recordGapCenter + 213062 = fullRecordGapValue04909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04909 (fullRecordGapValue04909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04909_not_prime : ¬(recordGapCenter + 213062).Prime := by
  rw [fullRecordGapTerm04909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04909_fast_pow_mod_ne_one

def fullRecordGapValue04910 : Nat := fullRecordGapCenterValue + 213068

theorem fullRecordGapTerm04910_eq_value :
    recordGapCenter + 213068 = fullRecordGapValue04910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04910 (fullRecordGapValue04910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04910_not_prime : ¬(recordGapCenter + 213068).Prime := by
  rw [fullRecordGapTerm04910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04910_fast_pow_mod_ne_one

def fullRecordGapValue04911 : Nat := fullRecordGapCenterValue + 213182

theorem fullRecordGapTerm04911_eq_value :
    recordGapCenter + 213182 = fullRecordGapValue04911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04911 (fullRecordGapValue04911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04911_not_prime : ¬(recordGapCenter + 213182).Prime := by
  rw [fullRecordGapTerm04911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04911_fast_pow_mod_ne_one

def fullRecordGapValue04912 : Nat := fullRecordGapCenterValue + 213326

theorem fullRecordGapTerm04912_eq_value :
    recordGapCenter + 213326 = fullRecordGapValue04912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04912 (fullRecordGapValue04912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04912_not_prime : ¬(recordGapCenter + 213326).Prime := by
  rw [fullRecordGapTerm04912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04912_fast_pow_mod_ne_one

def fullRecordGapValue04913 : Nat := fullRecordGapCenterValue + 213362

theorem fullRecordGapTerm04913_eq_value :
    recordGapCenter + 213362 = fullRecordGapValue04913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04913 (fullRecordGapValue04913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04913_not_prime : ¬(recordGapCenter + 213362).Prime := by
  rw [fullRecordGapTerm04913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04913_fast_pow_mod_ne_one

def fullRecordGapValue04914 : Nat := fullRecordGapCenterValue + 213518

theorem fullRecordGapTerm04914_eq_value :
    recordGapCenter + 213518 = fullRecordGapValue04914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04914 (fullRecordGapValue04914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04914_not_prime : ¬(recordGapCenter + 213518).Prime := by
  rw [fullRecordGapTerm04914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04914_fast_pow_mod_ne_one

def fullRecordGapValue04915 : Nat := fullRecordGapCenterValue + 213602

theorem fullRecordGapTerm04915_eq_value :
    recordGapCenter + 213602 = fullRecordGapValue04915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04915 (fullRecordGapValue04915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04915_not_prime : ¬(recordGapCenter + 213602).Prime := by
  rw [fullRecordGapTerm04915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04915_fast_pow_mod_ne_one

def fullRecordGapValue04916 : Nat := fullRecordGapCenterValue + 213722

theorem fullRecordGapTerm04916_eq_value :
    recordGapCenter + 213722 = fullRecordGapValue04916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04916 (fullRecordGapValue04916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04916_not_prime : ¬(recordGapCenter + 213722).Prime := by
  rw [fullRecordGapTerm04916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04916_fast_pow_mod_ne_one

def fullRecordGapValue04917 : Nat := fullRecordGapCenterValue + 213806

theorem fullRecordGapTerm04917_eq_value :
    recordGapCenter + 213806 = fullRecordGapValue04917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04917 (fullRecordGapValue04917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04917_not_prime : ¬(recordGapCenter + 213806).Prime := by
  rw [fullRecordGapTerm04917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04917_fast_pow_mod_ne_one

def fullRecordGapValue04918 : Nat := fullRecordGapCenterValue + 213812

theorem fullRecordGapTerm04918_eq_value :
    recordGapCenter + 213812 = fullRecordGapValue04918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04918 (fullRecordGapValue04918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04918_not_prime : ¬(recordGapCenter + 213812).Prime := by
  rw [fullRecordGapTerm04918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04918_fast_pow_mod_ne_one

def fullRecordGapValue04919 : Nat := fullRecordGapCenterValue + 214028

theorem fullRecordGapTerm04919_eq_value :
    recordGapCenter + 214028 = fullRecordGapValue04919 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04919_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04919 (fullRecordGapValue04919 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04919_not_prime : ¬(recordGapCenter + 214028).Prime := by
  rw [fullRecordGapTerm04919_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04919, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04919_fast_pow_mod_ne_one

def fullRecordGapValue04920 : Nat := fullRecordGapCenterValue + 214142

theorem fullRecordGapTerm04920_eq_value :
    recordGapCenter + 214142 = fullRecordGapValue04920 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04920_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04920 (fullRecordGapValue04920 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04920_not_prime : ¬(recordGapCenter + 214142).Prime := by
  rw [fullRecordGapTerm04920_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04920, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04920_fast_pow_mod_ne_one

def fullRecordGapValue04921 : Nat := fullRecordGapCenterValue + 214196

theorem fullRecordGapTerm04921_eq_value :
    recordGapCenter + 214196 = fullRecordGapValue04921 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04921_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04921 (fullRecordGapValue04921 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04921_not_prime : ¬(recordGapCenter + 214196).Prime := by
  rw [fullRecordGapTerm04921_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04921, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04921_fast_pow_mod_ne_one

def fullRecordGapValue04922 : Nat := fullRecordGapCenterValue + 214202

theorem fullRecordGapTerm04922_eq_value :
    recordGapCenter + 214202 = fullRecordGapValue04922 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04922_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04922 (fullRecordGapValue04922 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04922_not_prime : ¬(recordGapCenter + 214202).Prime := by
  rw [fullRecordGapTerm04922_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04922, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04922_fast_pow_mod_ne_one

def fullRecordGapValue04923 : Nat := fullRecordGapCenterValue + 214326

theorem fullRecordGapTerm04923_eq_value :
    recordGapCenter + 214326 = fullRecordGapValue04923 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04923_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04923 (fullRecordGapValue04923 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04923_not_prime : ¬(recordGapCenter + 214326).Prime := by
  rw [fullRecordGapTerm04923_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04923, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04923_fast_pow_mod_ne_one

def fullRecordGapValue04924 : Nat := fullRecordGapCenterValue + 214532

theorem fullRecordGapTerm04924_eq_value :
    recordGapCenter + 214532 = fullRecordGapValue04924 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04924_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04924 (fullRecordGapValue04924 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04924_not_prime : ¬(recordGapCenter + 214532).Prime := by
  rw [fullRecordGapTerm04924_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04924, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04924_fast_pow_mod_ne_one

def fullRecordGapValue04925 : Nat := fullRecordGapCenterValue + 214646

theorem fullRecordGapTerm04925_eq_value :
    recordGapCenter + 214646 = fullRecordGapValue04925 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04925_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04925 (fullRecordGapValue04925 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04925_not_prime : ¬(recordGapCenter + 214646).Prime := by
  rw [fullRecordGapTerm04925_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04925, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04925_fast_pow_mod_ne_one

def fullRecordGapValue04926 : Nat := fullRecordGapCenterValue + 215132

theorem fullRecordGapTerm04926_eq_value :
    recordGapCenter + 215132 = fullRecordGapValue04926 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04926_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04926 (fullRecordGapValue04926 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04926_not_prime : ¬(recordGapCenter + 215132).Prime := by
  rw [fullRecordGapTerm04926_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04926, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04926_fast_pow_mod_ne_one

def fullRecordGapValue04927 : Nat := fullRecordGapCenterValue + 215282

theorem fullRecordGapTerm04927_eq_value :
    recordGapCenter + 215282 = fullRecordGapValue04927 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04927_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04927 (fullRecordGapValue04927 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04927_not_prime : ¬(recordGapCenter + 215282).Prime := by
  rw [fullRecordGapTerm04927_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04927, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04927_fast_pow_mod_ne_one

def fullRecordGapValue04928 : Nat := fullRecordGapCenterValue + 215342

theorem fullRecordGapTerm04928_eq_value :
    recordGapCenter + 215342 = fullRecordGapValue04928 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04928_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04928 (fullRecordGapValue04928 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04928_not_prime : ¬(recordGapCenter + 215342).Prime := by
  rw [fullRecordGapTerm04928_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04928, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04928_fast_pow_mod_ne_one

def fullRecordGapValue04929 : Nat := fullRecordGapCenterValue + 215426

theorem fullRecordGapTerm04929_eq_value :
    recordGapCenter + 215426 = fullRecordGapValue04929 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04929_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04929 (fullRecordGapValue04929 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04929_not_prime : ¬(recordGapCenter + 215426).Prime := by
  rw [fullRecordGapTerm04929_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04929, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04929_fast_pow_mod_ne_one

def fullRecordGapValue04930 : Nat := fullRecordGapCenterValue + 215546

theorem fullRecordGapTerm04930_eq_value :
    recordGapCenter + 215546 = fullRecordGapValue04930 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04930_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04930 (fullRecordGapValue04930 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04930_not_prime : ¬(recordGapCenter + 215546).Prime := by
  rw [fullRecordGapTerm04930_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04930, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04930_fast_pow_mod_ne_one

def fullRecordGapValue04931 : Nat := fullRecordGapCenterValue + 215582

theorem fullRecordGapTerm04931_eq_value :
    recordGapCenter + 215582 = fullRecordGapValue04931 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04931_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04931 (fullRecordGapValue04931 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04931_not_prime : ¬(recordGapCenter + 215582).Prime := by
  rw [fullRecordGapTerm04931_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04931, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04931_fast_pow_mod_ne_one

def fullRecordGapValue04932 : Nat := fullRecordGapCenterValue + 215588

theorem fullRecordGapTerm04932_eq_value :
    recordGapCenter + 215588 = fullRecordGapValue04932 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04932_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04932 (fullRecordGapValue04932 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04932_not_prime : ¬(recordGapCenter + 215588).Prime := by
  rw [fullRecordGapTerm04932_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04932, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04932_fast_pow_mod_ne_one

def fullRecordGapValue04933 : Nat := fullRecordGapCenterValue + 215678

theorem fullRecordGapTerm04933_eq_value :
    recordGapCenter + 215678 = fullRecordGapValue04933 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04933_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04933 (fullRecordGapValue04933 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04933_not_prime : ¬(recordGapCenter + 215678).Prime := by
  rw [fullRecordGapTerm04933_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04933, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04933_fast_pow_mod_ne_one

def fullRecordGapValue04934 : Nat := fullRecordGapCenterValue + 215756

theorem fullRecordGapTerm04934_eq_value :
    recordGapCenter + 215756 = fullRecordGapValue04934 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04934_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04934 (fullRecordGapValue04934 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04934_not_prime : ¬(recordGapCenter + 215756).Prime := by
  rw [fullRecordGapTerm04934_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04934, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04934_fast_pow_mod_ne_one

def fullRecordGapValue04935 : Nat := fullRecordGapCenterValue + 215972

theorem fullRecordGapTerm04935_eq_value :
    recordGapCenter + 215972 = fullRecordGapValue04935 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04935_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04935 (fullRecordGapValue04935 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04935_not_prime : ¬(recordGapCenter + 215972).Prime := by
  rw [fullRecordGapTerm04935_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04935, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04935_fast_pow_mod_ne_one

def fullRecordGapValue04936 : Nat := fullRecordGapCenterValue + 216158

theorem fullRecordGapTerm04936_eq_value :
    recordGapCenter + 216158 = fullRecordGapValue04936 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04936_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04936 (fullRecordGapValue04936 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04936_not_prime : ¬(recordGapCenter + 216158).Prime := by
  rw [fullRecordGapTerm04936_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04936, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04936_fast_pow_mod_ne_one

def fullRecordGapValue04937 : Nat := fullRecordGapCenterValue + 216422

theorem fullRecordGapTerm04937_eq_value :
    recordGapCenter + 216422 = fullRecordGapValue04937 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04937_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04937 (fullRecordGapValue04937 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04937_not_prime : ¬(recordGapCenter + 216422).Prime := by
  rw [fullRecordGapTerm04937_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04937, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04937_fast_pow_mod_ne_one

def fullRecordGapValue04938 : Nat := fullRecordGapCenterValue + 216602

theorem fullRecordGapTerm04938_eq_value :
    recordGapCenter + 216602 = fullRecordGapValue04938 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04938_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04938 (fullRecordGapValue04938 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04938_not_prime : ¬(recordGapCenter + 216602).Prime := by
  rw [fullRecordGapTerm04938_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04938, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04938_fast_pow_mod_ne_one

def fullRecordGapValue04939 : Nat := fullRecordGapCenterValue + 216668

theorem fullRecordGapTerm04939_eq_value :
    recordGapCenter + 216668 = fullRecordGapValue04939 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04939_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04939 (fullRecordGapValue04939 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04939_not_prime : ¬(recordGapCenter + 216668).Prime := by
  rw [fullRecordGapTerm04939_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04939, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04939_fast_pow_mod_ne_one

def fullRecordGapValue04940 : Nat := fullRecordGapCenterValue + 216758

theorem fullRecordGapTerm04940_eq_value :
    recordGapCenter + 216758 = fullRecordGapValue04940 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04940_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04940 (fullRecordGapValue04940 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04940_not_prime : ¬(recordGapCenter + 216758).Prime := by
  rw [fullRecordGapTerm04940_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04940, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04940_fast_pow_mod_ne_one

def fullRecordGapValue04941 : Nat := fullRecordGapCenterValue + 216842

theorem fullRecordGapTerm04941_eq_value :
    recordGapCenter + 216842 = fullRecordGapValue04941 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04941_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04941 (fullRecordGapValue04941 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04941_not_prime : ¬(recordGapCenter + 216842).Prime := by
  rw [fullRecordGapTerm04941_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04941, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04941_fast_pow_mod_ne_one

def fullRecordGapValue04942 : Nat := fullRecordGapCenterValue + 216926

theorem fullRecordGapTerm04942_eq_value :
    recordGapCenter + 216926 = fullRecordGapValue04942 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04942_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04942 (fullRecordGapValue04942 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04942_not_prime : ¬(recordGapCenter + 216926).Prime := by
  rw [fullRecordGapTerm04942_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04942, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04942_fast_pow_mod_ne_one

def fullRecordGapValue04943 : Nat := fullRecordGapCenterValue + 216998

theorem fullRecordGapTerm04943_eq_value :
    recordGapCenter + 216998 = fullRecordGapValue04943 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04943_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04943 (fullRecordGapValue04943 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04943_not_prime : ¬(recordGapCenter + 216998).Prime := by
  rw [fullRecordGapTerm04943_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04943, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04943_fast_pow_mod_ne_one

def fullRecordGapValue04944 : Nat := fullRecordGapCenterValue + 217082

theorem fullRecordGapTerm04944_eq_value :
    recordGapCenter + 217082 = fullRecordGapValue04944 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04944_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04944 (fullRecordGapValue04944 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04944_not_prime : ¬(recordGapCenter + 217082).Prime := by
  rw [fullRecordGapTerm04944_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04944, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04944_fast_pow_mod_ne_one

def fullRecordGapValue04945 : Nat := fullRecordGapCenterValue + 217106

theorem fullRecordGapTerm04945_eq_value :
    recordGapCenter + 217106 = fullRecordGapValue04945 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04945_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04945 (fullRecordGapValue04945 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04945_not_prime : ¬(recordGapCenter + 217106).Prime := by
  rw [fullRecordGapTerm04945_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04945, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04945_fast_pow_mod_ne_one

def fullRecordGapValue04946 : Nat := fullRecordGapCenterValue + 217148

theorem fullRecordGapTerm04946_eq_value :
    recordGapCenter + 217148 = fullRecordGapValue04946 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04946_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04946 (fullRecordGapValue04946 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04946_not_prime : ¬(recordGapCenter + 217148).Prime := by
  rw [fullRecordGapTerm04946_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04946, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04946_fast_pow_mod_ne_one

def fullRecordGapValue04947 : Nat := fullRecordGapCenterValue + 217262

theorem fullRecordGapTerm04947_eq_value :
    recordGapCenter + 217262 = fullRecordGapValue04947 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04947_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04947 (fullRecordGapValue04947 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04947_not_prime : ¬(recordGapCenter + 217262).Prime := by
  rw [fullRecordGapTerm04947_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04947, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04947_fast_pow_mod_ne_one

def fullRecordGapValue04948 : Nat := fullRecordGapCenterValue + 217292

theorem fullRecordGapTerm04948_eq_value :
    recordGapCenter + 217292 = fullRecordGapValue04948 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04948_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04948 (fullRecordGapValue04948 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04948_not_prime : ¬(recordGapCenter + 217292).Prime := by
  rw [fullRecordGapTerm04948_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04948, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04948_fast_pow_mod_ne_one

def fullRecordGapValue04949 : Nat := fullRecordGapCenterValue + 217298

theorem fullRecordGapTerm04949_eq_value :
    recordGapCenter + 217298 = fullRecordGapValue04949 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04949_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04949 (fullRecordGapValue04949 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04949_not_prime : ¬(recordGapCenter + 217298).Prime := by
  rw [fullRecordGapTerm04949_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04949, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04949_fast_pow_mod_ne_one

def fullRecordGapValue04950 : Nat := fullRecordGapCenterValue + 217388

theorem fullRecordGapTerm04950_eq_value :
    recordGapCenter + 217388 = fullRecordGapValue04950 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04950_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04950 (fullRecordGapValue04950 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04950_not_prime : ¬(recordGapCenter + 217388).Prime := by
  rw [fullRecordGapTerm04950_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04950, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04950_fast_pow_mod_ne_one

def fullRecordGapValue04951 : Nat := fullRecordGapCenterValue + 217418

theorem fullRecordGapTerm04951_eq_value :
    recordGapCenter + 217418 = fullRecordGapValue04951 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04951_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04951 (fullRecordGapValue04951 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04951_not_prime : ¬(recordGapCenter + 217418).Prime := by
  rw [fullRecordGapTerm04951_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04951, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04951_fast_pow_mod_ne_one

def fullRecordGapValue04952 : Nat := fullRecordGapCenterValue + 217502

theorem fullRecordGapTerm04952_eq_value :
    recordGapCenter + 217502 = fullRecordGapValue04952 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04952_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04952 (fullRecordGapValue04952 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04952_not_prime : ¬(recordGapCenter + 217502).Prime := by
  rw [fullRecordGapTerm04952_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04952, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04952_fast_pow_mod_ne_one

def fullRecordGapValue04953 : Nat := fullRecordGapCenterValue + 217886

theorem fullRecordGapTerm04953_eq_value :
    recordGapCenter + 217886 = fullRecordGapValue04953 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04953_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04953 (fullRecordGapValue04953 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04953_not_prime : ¬(recordGapCenter + 217886).Prime := by
  rw [fullRecordGapTerm04953_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04953, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04953_fast_pow_mod_ne_one

def fullRecordGapValue04954 : Nat := fullRecordGapCenterValue + 217922

theorem fullRecordGapTerm04954_eq_value :
    recordGapCenter + 217922 = fullRecordGapValue04954 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04954_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04954 (fullRecordGapValue04954 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04954_not_prime : ¬(recordGapCenter + 217922).Prime := by
  rw [fullRecordGapTerm04954_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04954, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04954_fast_pow_mod_ne_one

def fullRecordGapValue04955 : Nat := fullRecordGapCenterValue + 217982

theorem fullRecordGapTerm04955_eq_value :
    recordGapCenter + 217982 = fullRecordGapValue04955 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04955_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04955 (fullRecordGapValue04955 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04955_not_prime : ¬(recordGapCenter + 217982).Prime := by
  rw [fullRecordGapTerm04955_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04955, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04955_fast_pow_mod_ne_one

def fullRecordGapValue04956 : Nat := fullRecordGapCenterValue + 217988

theorem fullRecordGapTerm04956_eq_value :
    recordGapCenter + 217988 = fullRecordGapValue04956 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04956_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04956 (fullRecordGapValue04956 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04956_not_prime : ¬(recordGapCenter + 217988).Prime := by
  rw [fullRecordGapTerm04956_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04956, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04956_fast_pow_mod_ne_one

def fullRecordGapValue04957 : Nat := fullRecordGapCenterValue + 218468

theorem fullRecordGapTerm04957_eq_value :
    recordGapCenter + 218468 = fullRecordGapValue04957 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04957_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04957 (fullRecordGapValue04957 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04957_not_prime : ¬(recordGapCenter + 218468).Prime := by
  rw [fullRecordGapTerm04957_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04957, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04957_fast_pow_mod_ne_one

def fullRecordGapValue04958 : Nat := fullRecordGapCenterValue + 218516

theorem fullRecordGapTerm04958_eq_value :
    recordGapCenter + 218516 = fullRecordGapValue04958 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04958_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04958 (fullRecordGapValue04958 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04958_not_prime : ¬(recordGapCenter + 218516).Prime := by
  rw [fullRecordGapTerm04958_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04958, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04958_fast_pow_mod_ne_one

def fullRecordGapValue04959 : Nat := fullRecordGapCenterValue + 218642

theorem fullRecordGapTerm04959_eq_value :
    recordGapCenter + 218642 = fullRecordGapValue04959 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04959_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04959 (fullRecordGapValue04959 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04959_not_prime : ¬(recordGapCenter + 218642).Prime := by
  rw [fullRecordGapTerm04959_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04959, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04959_fast_pow_mod_ne_one

def fullRecordGapValue04960 : Nat := fullRecordGapCenterValue + 218726

theorem fullRecordGapTerm04960_eq_value :
    recordGapCenter + 218726 = fullRecordGapValue04960 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04960_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04960 (fullRecordGapValue04960 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04960_not_prime : ¬(recordGapCenter + 218726).Prime := by
  rw [fullRecordGapTerm04960_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04960, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04960_fast_pow_mod_ne_one

def fullRecordGapValue04961 : Nat := fullRecordGapCenterValue + 218750

theorem fullRecordGapTerm04961_eq_value :
    recordGapCenter + 218750 = fullRecordGapValue04961 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04961_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04961 (fullRecordGapValue04961 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04961_not_prime : ¬(recordGapCenter + 218750).Prime := by
  rw [fullRecordGapTerm04961_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04961, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04961_fast_pow_mod_ne_one

def fullRecordGapValue04962 : Nat := fullRecordGapCenterValue + 218906

theorem fullRecordGapTerm04962_eq_value :
    recordGapCenter + 218906 = fullRecordGapValue04962 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04962_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04962 (fullRecordGapValue04962 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04962_not_prime : ¬(recordGapCenter + 218906).Prime := by
  rw [fullRecordGapTerm04962_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04962, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04962_fast_pow_mod_ne_one

def fullRecordGapValue04963 : Nat := fullRecordGapCenterValue + 219068

theorem fullRecordGapTerm04963_eq_value :
    recordGapCenter + 219068 = fullRecordGapValue04963 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04963_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04963 (fullRecordGapValue04963 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04963_not_prime : ¬(recordGapCenter + 219068).Prime := by
  rw [fullRecordGapTerm04963_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04963, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04963_fast_pow_mod_ne_one

def fullRecordGapValue04964 : Nat := fullRecordGapCenterValue + 219278

theorem fullRecordGapTerm04964_eq_value :
    recordGapCenter + 219278 = fullRecordGapValue04964 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04964_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04964 (fullRecordGapValue04964 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04964_not_prime : ¬(recordGapCenter + 219278).Prime := by
  rw [fullRecordGapTerm04964_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04964, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04964_fast_pow_mod_ne_one

def fullRecordGapValue04965 : Nat := fullRecordGapCenterValue + 219662

theorem fullRecordGapTerm04965_eq_value :
    recordGapCenter + 219662 = fullRecordGapValue04965 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04965_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04965 (fullRecordGapValue04965 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04965_not_prime : ¬(recordGapCenter + 219662).Prime := by
  rw [fullRecordGapTerm04965_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04965, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04965_fast_pow_mod_ne_one

def fullRecordGapValue04966 : Nat := fullRecordGapCenterValue + 219698

theorem fullRecordGapTerm04966_eq_value :
    recordGapCenter + 219698 = fullRecordGapValue04966 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04966_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04966 (fullRecordGapValue04966 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04966_not_prime : ¬(recordGapCenter + 219698).Prime := by
  rw [fullRecordGapTerm04966_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04966, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04966_fast_pow_mod_ne_one

def fullRecordGapValue04967 : Nat := fullRecordGapCenterValue + 220118

theorem fullRecordGapTerm04967_eq_value :
    recordGapCenter + 220118 = fullRecordGapValue04967 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04967_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04967 (fullRecordGapValue04967 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04967_not_prime : ¬(recordGapCenter + 220118).Prime := by
  rw [fullRecordGapTerm04967_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04967, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04967_fast_pow_mod_ne_one

def fullRecordGapValue04968 : Nat := fullRecordGapCenterValue + 220316

theorem fullRecordGapTerm04968_eq_value :
    recordGapCenter + 220316 = fullRecordGapValue04968 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04968_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04968 (fullRecordGapValue04968 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04968_not_prime : ¬(recordGapCenter + 220316).Prime := by
  rw [fullRecordGapTerm04968_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04968, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04968_fast_pow_mod_ne_one

def fullRecordGapValue04969 : Nat := fullRecordGapCenterValue + 220322

theorem fullRecordGapTerm04969_eq_value :
    recordGapCenter + 220322 = fullRecordGapValue04969 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04969_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04969 (fullRecordGapValue04969 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04969_not_prime : ¬(recordGapCenter + 220322).Prime := by
  rw [fullRecordGapTerm04969_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04969, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04969_fast_pow_mod_ne_one

def fullRecordGapValue04970 : Nat := fullRecordGapCenterValue + 220412

theorem fullRecordGapTerm04970_eq_value :
    recordGapCenter + 220412 = fullRecordGapValue04970 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04970_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04970 (fullRecordGapValue04970 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04970_not_prime : ¬(recordGapCenter + 220412).Prime := by
  rw [fullRecordGapTerm04970_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04970, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04970_fast_pow_mod_ne_one

def fullRecordGapValue04971 : Nat := fullRecordGapCenterValue + 220538

theorem fullRecordGapTerm04971_eq_value :
    recordGapCenter + 220538 = fullRecordGapValue04971 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04971_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04971 (fullRecordGapValue04971 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04971_not_prime : ¬(recordGapCenter + 220538).Prime := by
  rw [fullRecordGapTerm04971_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04971, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04971_fast_pow_mod_ne_one

def fullRecordGapValue04972 : Nat := fullRecordGapCenterValue + 220622

theorem fullRecordGapTerm04972_eq_value :
    recordGapCenter + 220622 = fullRecordGapValue04972 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04972_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04972 (fullRecordGapValue04972 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04972_not_prime : ¬(recordGapCenter + 220622).Prime := by
  rw [fullRecordGapTerm04972_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04972, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04972_fast_pow_mod_ne_one

def fullRecordGapValue04973 : Nat := fullRecordGapCenterValue + 220652

theorem fullRecordGapTerm04973_eq_value :
    recordGapCenter + 220652 = fullRecordGapValue04973 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04973_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04973 (fullRecordGapValue04973 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04973_not_prime : ¬(recordGapCenter + 220652).Prime := by
  rw [fullRecordGapTerm04973_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04973, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04973_fast_pow_mod_ne_one

def fullRecordGapValue04974 : Nat := fullRecordGapCenterValue + 220862

theorem fullRecordGapTerm04974_eq_value :
    recordGapCenter + 220862 = fullRecordGapValue04974 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04974_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04974 (fullRecordGapValue04974 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04974_not_prime : ¬(recordGapCenter + 220862).Prime := by
  rw [fullRecordGapTerm04974_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04974, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04974_fast_pow_mod_ne_one

def fullRecordGapValue04975 : Nat := fullRecordGapCenterValue + 220958

theorem fullRecordGapTerm04975_eq_value :
    recordGapCenter + 220958 = fullRecordGapValue04975 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04975_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04975 (fullRecordGapValue04975 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04975_not_prime : ¬(recordGapCenter + 220958).Prime := by
  rw [fullRecordGapTerm04975_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04975, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04975_fast_pow_mod_ne_one

def fullRecordGapValue04976 : Nat := fullRecordGapCenterValue + 221006

theorem fullRecordGapTerm04976_eq_value :
    recordGapCenter + 221006 = fullRecordGapValue04976 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04976_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04976 (fullRecordGapValue04976 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04976_not_prime : ¬(recordGapCenter + 221006).Prime := by
  rw [fullRecordGapTerm04976_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04976, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04976_fast_pow_mod_ne_one

def fullRecordGapValue04977 : Nat := fullRecordGapCenterValue + 221036

theorem fullRecordGapTerm04977_eq_value :
    recordGapCenter + 221036 = fullRecordGapValue04977 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04977_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04977 (fullRecordGapValue04977 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04977_not_prime : ¬(recordGapCenter + 221036).Prime := by
  rw [fullRecordGapTerm04977_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04977, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04977_fast_pow_mod_ne_one

def fullRecordGapValue04978 : Nat := fullRecordGapCenterValue + 221126

theorem fullRecordGapTerm04978_eq_value :
    recordGapCenter + 221126 = fullRecordGapValue04978 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04978_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04978 (fullRecordGapValue04978 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04978_not_prime : ¬(recordGapCenter + 221126).Prime := by
  rw [fullRecordGapTerm04978_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04978, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04978_fast_pow_mod_ne_one

def fullRecordGapValue04979 : Nat := fullRecordGapCenterValue + 221138

theorem fullRecordGapTerm04979_eq_value :
    recordGapCenter + 221138 = fullRecordGapValue04979 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04979_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04979 (fullRecordGapValue04979 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04979_not_prime : ¬(recordGapCenter + 221138).Prime := by
  rw [fullRecordGapTerm04979_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04979, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04979_fast_pow_mod_ne_one

def fullRecordGapValue04980 : Nat := fullRecordGapCenterValue + 221252

theorem fullRecordGapTerm04980_eq_value :
    recordGapCenter + 221252 = fullRecordGapValue04980 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04980_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04980 (fullRecordGapValue04980 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04980_not_prime : ¬(recordGapCenter + 221252).Prime := by
  rw [fullRecordGapTerm04980_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04980, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04980_fast_pow_mod_ne_one

def fullRecordGapValue04981 : Nat := fullRecordGapCenterValue + 221258

theorem fullRecordGapTerm04981_eq_value :
    recordGapCenter + 221258 = fullRecordGapValue04981 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04981_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04981 (fullRecordGapValue04981 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04981_not_prime : ¬(recordGapCenter + 221258).Prime := by
  rw [fullRecordGapTerm04981_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04981, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04981_fast_pow_mod_ne_one

def fullRecordGapValue04982 : Nat := fullRecordGapCenterValue + 221348

theorem fullRecordGapTerm04982_eq_value :
    recordGapCenter + 221348 = fullRecordGapValue04982 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04982_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04982 (fullRecordGapValue04982 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04982_not_prime : ¬(recordGapCenter + 221348).Prime := by
  rw [fullRecordGapTerm04982_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04982, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04982_fast_pow_mod_ne_one

def fullRecordGapValue04983 : Nat := fullRecordGapCenterValue + 221498

theorem fullRecordGapTerm04983_eq_value :
    recordGapCenter + 221498 = fullRecordGapValue04983 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04983_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04983 (fullRecordGapValue04983 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04983_not_prime : ¬(recordGapCenter + 221498).Prime := by
  rw [fullRecordGapTerm04983_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04983, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04983_fast_pow_mod_ne_one

def fullRecordGapValue04984 : Nat := fullRecordGapCenterValue + 221642

theorem fullRecordGapTerm04984_eq_value :
    recordGapCenter + 221642 = fullRecordGapValue04984 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04984_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04984 (fullRecordGapValue04984 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04984_not_prime : ¬(recordGapCenter + 221642).Prime := by
  rw [fullRecordGapTerm04984_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04984, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04984_fast_pow_mod_ne_one

def fullRecordGapValue04985 : Nat := fullRecordGapCenterValue + 221726

theorem fullRecordGapTerm04985_eq_value :
    recordGapCenter + 221726 = fullRecordGapValue04985 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04985_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04985 (fullRecordGapValue04985 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04985_not_prime : ¬(recordGapCenter + 221726).Prime := by
  rw [fullRecordGapTerm04985_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04985, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04985_fast_pow_mod_ne_one

def fullRecordGapValue04986 : Nat := fullRecordGapCenterValue + 221978

theorem fullRecordGapTerm04986_eq_value :
    recordGapCenter + 221978 = fullRecordGapValue04986 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04986_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04986 (fullRecordGapValue04986 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04986_not_prime : ¬(recordGapCenter + 221978).Prime := by
  rw [fullRecordGapTerm04986_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04986, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04986_fast_pow_mod_ne_one

def fullRecordGapValue04987 : Nat := fullRecordGapCenterValue + 222098

theorem fullRecordGapTerm04987_eq_value :
    recordGapCenter + 222098 = fullRecordGapValue04987 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04987_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04987 (fullRecordGapValue04987 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04987_not_prime : ¬(recordGapCenter + 222098).Prime := by
  rw [fullRecordGapTerm04987_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04987, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04987_fast_pow_mod_ne_one

def fullRecordGapValue04988 : Nat := fullRecordGapCenterValue + 222188

theorem fullRecordGapTerm04988_eq_value :
    recordGapCenter + 222188 = fullRecordGapValue04988 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04988_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04988 (fullRecordGapValue04988 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04988_not_prime : ¬(recordGapCenter + 222188).Prime := by
  rw [fullRecordGapTerm04988_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04988, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04988_fast_pow_mod_ne_one

def fullRecordGapValue04989 : Nat := fullRecordGapCenterValue + 222206

theorem fullRecordGapTerm04989_eq_value :
    recordGapCenter + 222206 = fullRecordGapValue04989 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04989_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04989 (fullRecordGapValue04989 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04989_not_prime : ¬(recordGapCenter + 222206).Prime := by
  rw [fullRecordGapTerm04989_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04989, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04989_fast_pow_mod_ne_one

def fullRecordGapValue04990 : Nat := fullRecordGapCenterValue + 222458

theorem fullRecordGapTerm04990_eq_value :
    recordGapCenter + 222458 = fullRecordGapValue04990 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04990_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04990 (fullRecordGapValue04990 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04990_not_prime : ¬(recordGapCenter + 222458).Prime := by
  rw [fullRecordGapTerm04990_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04990, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04990_fast_pow_mod_ne_one

def fullRecordGapValue04991 : Nat := fullRecordGapCenterValue + 222476

theorem fullRecordGapTerm04991_eq_value :
    recordGapCenter + 222476 = fullRecordGapValue04991 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04991_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04991 (fullRecordGapValue04991 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04991_not_prime : ¬(recordGapCenter + 222476).Prime := by
  rw [fullRecordGapTerm04991_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04991, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04991_fast_pow_mod_ne_one

def fullRecordGapValue04992 : Nat := fullRecordGapCenterValue + 222506

theorem fullRecordGapTerm04992_eq_value :
    recordGapCenter + 222506 = fullRecordGapValue04992 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04992_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04992 (fullRecordGapValue04992 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04992_not_prime : ¬(recordGapCenter + 222506).Prime := by
  rw [fullRecordGapTerm04992_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04992, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04992_fast_pow_mod_ne_one

def fullRecordGapValue04993 : Nat := fullRecordGapCenterValue + 222542

theorem fullRecordGapTerm04993_eq_value :
    recordGapCenter + 222542 = fullRecordGapValue04993 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04993_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04993 (fullRecordGapValue04993 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04993_not_prime : ¬(recordGapCenter + 222542).Prime := by
  rw [fullRecordGapTerm04993_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04993, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04993_fast_pow_mod_ne_one

def fullRecordGapValue04994 : Nat := fullRecordGapCenterValue + 222668

theorem fullRecordGapTerm04994_eq_value :
    recordGapCenter + 222668 = fullRecordGapValue04994 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04994_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04994 (fullRecordGapValue04994 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04994_not_prime : ¬(recordGapCenter + 222668).Prime := by
  rw [fullRecordGapTerm04994_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04994, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04994_fast_pow_mod_ne_one

def fullRecordGapValue04995 : Nat := fullRecordGapCenterValue + 222818

theorem fullRecordGapTerm04995_eq_value :
    recordGapCenter + 222818 = fullRecordGapValue04995 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04995_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04995 (fullRecordGapValue04995 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04995_not_prime : ¬(recordGapCenter + 222818).Prime := by
  rw [fullRecordGapTerm04995_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04995, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04995_fast_pow_mod_ne_one

def fullRecordGapValue04996 : Nat := fullRecordGapCenterValue + 222986

theorem fullRecordGapTerm04996_eq_value :
    recordGapCenter + 222986 = fullRecordGapValue04996 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04996_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04996 (fullRecordGapValue04996 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04996_not_prime : ¬(recordGapCenter + 222986).Prime := by
  rw [fullRecordGapTerm04996_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04996, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04996_fast_pow_mod_ne_one

def fullRecordGapValue04997 : Nat := fullRecordGapCenterValue + 223052

theorem fullRecordGapTerm04997_eq_value :
    recordGapCenter + 223052 = fullRecordGapValue04997 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04997_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04997 (fullRecordGapValue04997 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04997_not_prime : ¬(recordGapCenter + 223052).Prime := by
  rw [fullRecordGapTerm04997_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04997, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04997_fast_pow_mod_ne_one

def fullRecordGapValue04998 : Nat := fullRecordGapCenterValue + 223148

theorem fullRecordGapTerm04998_eq_value :
    recordGapCenter + 223148 = fullRecordGapValue04998 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04998_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04998 (fullRecordGapValue04998 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04998_not_prime : ¬(recordGapCenter + 223148).Prime := by
  rw [fullRecordGapTerm04998_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04998, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04998_fast_pow_mod_ne_one

def fullRecordGapValue04999 : Nat := fullRecordGapCenterValue + 223316

theorem fullRecordGapTerm04999_eq_value :
    recordGapCenter + 223316 = fullRecordGapValue04999 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04999_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04999 (fullRecordGapValue04999 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04999_not_prime : ¬(recordGapCenter + 223316).Prime := by
  rw [fullRecordGapTerm04999_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04999, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04999_fast_pow_mod_ne_one

def fullRecordGapValue05000 : Nat := fullRecordGapCenterValue + 223562

theorem fullRecordGapTerm05000_eq_value :
    recordGapCenter + 223562 = fullRecordGapValue05000 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05000_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05000 (fullRecordGapValue05000 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05000_not_prime : ¬(recordGapCenter + 223562).Prime := by
  rw [fullRecordGapTerm05000_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05000, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05000_fast_pow_mod_ne_one

def fullRecordGapValue05001 : Nat := fullRecordGapCenterValue + 223742

theorem fullRecordGapTerm05001_eq_value :
    recordGapCenter + 223742 = fullRecordGapValue05001 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05001_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05001 (fullRecordGapValue05001 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05001_not_prime : ¬(recordGapCenter + 223742).Prime := by
  rw [fullRecordGapTerm05001_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05001, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05001_fast_pow_mod_ne_one

def fullRecordGapValue05002 : Nat := fullRecordGapCenterValue + 223946

theorem fullRecordGapTerm05002_eq_value :
    recordGapCenter + 223946 = fullRecordGapValue05002 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05002_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05002 (fullRecordGapValue05002 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05002_not_prime : ¬(recordGapCenter + 223946).Prime := by
  rw [fullRecordGapTerm05002_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05002, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05002_fast_pow_mod_ne_one

def fullRecordGapValue05003 : Nat := fullRecordGapCenterValue + 224036

theorem fullRecordGapTerm05003_eq_value :
    recordGapCenter + 224036 = fullRecordGapValue05003 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05003_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05003 (fullRecordGapValue05003 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05003_not_prime : ¬(recordGapCenter + 224036).Prime := by
  rw [fullRecordGapTerm05003_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05003, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05003_fast_pow_mod_ne_one

def fullRecordGapValue05004 : Nat := fullRecordGapCenterValue + 224138

theorem fullRecordGapTerm05004_eq_value :
    recordGapCenter + 224138 = fullRecordGapValue05004 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05004_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05004 (fullRecordGapValue05004 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05004_not_prime : ¬(recordGapCenter + 224138).Prime := by
  rw [fullRecordGapTerm05004_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05004, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05004_fast_pow_mod_ne_one

def fullRecordGapValue05005 : Nat := fullRecordGapCenterValue + 224156

theorem fullRecordGapTerm05005_eq_value :
    recordGapCenter + 224156 = fullRecordGapValue05005 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05005_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05005 (fullRecordGapValue05005 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05005_not_prime : ¬(recordGapCenter + 224156).Prime := by
  rw [fullRecordGapTerm05005_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05005, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05005_fast_pow_mod_ne_one

def fullRecordGapValue05006 : Nat := fullRecordGapCenterValue + 224222

theorem fullRecordGapTerm05006_eq_value :
    recordGapCenter + 224222 = fullRecordGapValue05006 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05006_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05006 (fullRecordGapValue05006 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05006_not_prime : ¬(recordGapCenter + 224222).Prime := by
  rw [fullRecordGapTerm05006_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05006, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05006_fast_pow_mod_ne_one

def fullRecordGapValue05007 : Nat := fullRecordGapCenterValue + 224348

theorem fullRecordGapTerm05007_eq_value :
    recordGapCenter + 224348 = fullRecordGapValue05007 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05007_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05007 (fullRecordGapValue05007 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05007_not_prime : ¬(recordGapCenter + 224348).Prime := by
  rw [fullRecordGapTerm05007_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05007, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05007_fast_pow_mod_ne_one

def fullRecordGapValue05008 : Nat := fullRecordGapCenterValue + 224372

theorem fullRecordGapTerm05008_eq_value :
    recordGapCenter + 224372 = fullRecordGapValue05008 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05008_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05008 (fullRecordGapValue05008 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05008_not_prime : ¬(recordGapCenter + 224372).Prime := by
  rw [fullRecordGapTerm05008_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05008, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05008_fast_pow_mod_ne_one

def fullRecordGapValue05009 : Nat := fullRecordGapCenterValue + 224492

theorem fullRecordGapTerm05009_eq_value :
    recordGapCenter + 224492 = fullRecordGapValue05009 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05009_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05009 (fullRecordGapValue05009 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05009_not_prime : ¬(recordGapCenter + 224492).Prime := by
  rw [fullRecordGapTerm05009_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05009, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05009_fast_pow_mod_ne_one

def fullRecordGapValue05010 : Nat := fullRecordGapCenterValue + 224522

theorem fullRecordGapTerm05010_eq_value :
    recordGapCenter + 224522 = fullRecordGapValue05010 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05010_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05010 (fullRecordGapValue05010 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05010_not_prime : ¬(recordGapCenter + 224522).Prime := by
  rw [fullRecordGapTerm05010_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05010, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05010_fast_pow_mod_ne_one

def fullRecordGapValue05011 : Nat := fullRecordGapCenterValue + 224558

theorem fullRecordGapTerm05011_eq_value :
    recordGapCenter + 224558 = fullRecordGapValue05011 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05011_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05011 (fullRecordGapValue05011 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05011_not_prime : ¬(recordGapCenter + 224558).Prime := by
  rw [fullRecordGapTerm05011_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05011, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05011_fast_pow_mod_ne_one

def fullRecordGapValue05012 : Nat := fullRecordGapCenterValue + 224582

theorem fullRecordGapTerm05012_eq_value :
    recordGapCenter + 224582 = fullRecordGapValue05012 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05012_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05012 (fullRecordGapValue05012 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05012_not_prime : ¬(recordGapCenter + 224582).Prime := by
  rw [fullRecordGapTerm05012_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05012, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05012_fast_pow_mod_ne_one

def fullRecordGapValue05013 : Nat := fullRecordGapCenterValue + 224828

theorem fullRecordGapTerm05013_eq_value :
    recordGapCenter + 224828 = fullRecordGapValue05013 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05013_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05013 (fullRecordGapValue05013 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05013_not_prime : ¬(recordGapCenter + 224828).Prime := by
  rw [fullRecordGapTerm05013_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05013, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05013_fast_pow_mod_ne_one

def fullRecordGapValue05014 : Nat := fullRecordGapCenterValue + 224996

theorem fullRecordGapTerm05014_eq_value :
    recordGapCenter + 224996 = fullRecordGapValue05014 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05014_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05014 (fullRecordGapValue05014 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05014_not_prime : ¬(recordGapCenter + 224996).Prime := by
  rw [fullRecordGapTerm05014_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05014, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05014_fast_pow_mod_ne_one

def fullRecordGapValue05015 : Nat := fullRecordGapCenterValue + 225002

theorem fullRecordGapTerm05015_eq_value :
    recordGapCenter + 225002 = fullRecordGapValue05015 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05015_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05015 (fullRecordGapValue05015 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05015_not_prime : ¬(recordGapCenter + 225002).Prime := by
  rw [fullRecordGapTerm05015_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05015, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05015_fast_pow_mod_ne_one

def fullRecordGapValue05016 : Nat := fullRecordGapCenterValue + 225086

theorem fullRecordGapTerm05016_eq_value :
    recordGapCenter + 225086 = fullRecordGapValue05016 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05016_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05016 (fullRecordGapValue05016 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05016_not_prime : ¬(recordGapCenter + 225086).Prime := by
  rw [fullRecordGapTerm05016_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05016, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05016_fast_pow_mod_ne_one

def fullRecordGapValue05017 : Nat := fullRecordGapCenterValue + 225326

theorem fullRecordGapTerm05017_eq_value :
    recordGapCenter + 225326 = fullRecordGapValue05017 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05017_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05017 (fullRecordGapValue05017 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05017_not_prime : ¬(recordGapCenter + 225326).Prime := by
  rw [fullRecordGapTerm05017_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05017, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05017_fast_pow_mod_ne_one

def fullRecordGapValue05018 : Nat := fullRecordGapCenterValue + 225332

theorem fullRecordGapTerm05018_eq_value :
    recordGapCenter + 225332 = fullRecordGapValue05018 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05018_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05018 (fullRecordGapValue05018 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05018_not_prime : ¬(recordGapCenter + 225332).Prime := by
  rw [fullRecordGapTerm05018_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05018, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05018_fast_pow_mod_ne_one

def fullRecordGapValue05019 : Nat := fullRecordGapCenterValue + 225572

theorem fullRecordGapTerm05019_eq_value :
    recordGapCenter + 225572 = fullRecordGapValue05019 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05019_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05019 (fullRecordGapValue05019 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05019_not_prime : ¬(recordGapCenter + 225572).Prime := by
  rw [fullRecordGapTerm05019_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05019, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05019_fast_pow_mod_ne_one

def fullRecordGapValue05020 : Nat := fullRecordGapCenterValue + 225668

theorem fullRecordGapTerm05020_eq_value :
    recordGapCenter + 225668 = fullRecordGapValue05020 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05020_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05020 (fullRecordGapValue05020 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05020_not_prime : ¬(recordGapCenter + 225668).Prime := by
  rw [fullRecordGapTerm05020_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05020, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05020_fast_pow_mod_ne_one

def fullRecordGapValue05021 : Nat := fullRecordGapCenterValue + 225818

theorem fullRecordGapTerm05021_eq_value :
    recordGapCenter + 225818 = fullRecordGapValue05021 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05021_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05021 (fullRecordGapValue05021 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05021_not_prime : ¬(recordGapCenter + 225818).Prime := by
  rw [fullRecordGapTerm05021_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05021, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05021_fast_pow_mod_ne_one

def fullRecordGapValue05022 : Nat := fullRecordGapCenterValue + 225842

theorem fullRecordGapTerm05022_eq_value :
    recordGapCenter + 225842 = fullRecordGapValue05022 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05022_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05022 (fullRecordGapValue05022 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05022_not_prime : ¬(recordGapCenter + 225842).Prime := by
  rw [fullRecordGapTerm05022_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05022, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05022_fast_pow_mod_ne_one

def fullRecordGapValue05023 : Nat := fullRecordGapCenterValue + 225878

theorem fullRecordGapTerm05023_eq_value :
    recordGapCenter + 225878 = fullRecordGapValue05023 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05023_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05023 (fullRecordGapValue05023 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05023_not_prime : ¬(recordGapCenter + 225878).Prime := by
  rw [fullRecordGapTerm05023_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05023, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05023_fast_pow_mod_ne_one

def fullRecordGapValue05024 : Nat := fullRecordGapCenterValue + 225908

theorem fullRecordGapTerm05024_eq_value :
    recordGapCenter + 225908 = fullRecordGapValue05024 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05024_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05024 (fullRecordGapValue05024 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05024_not_prime : ¬(recordGapCenter + 225908).Prime := by
  rw [fullRecordGapTerm05024_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05024, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05024_fast_pow_mod_ne_one

def fullRecordGapValue05025 : Nat := fullRecordGapCenterValue + 226076

theorem fullRecordGapTerm05025_eq_value :
    recordGapCenter + 226076 = fullRecordGapValue05025 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05025_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05025 (fullRecordGapValue05025 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05025_not_prime : ¬(recordGapCenter + 226076).Prime := by
  rw [fullRecordGapTerm05025_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05025, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05025_fast_pow_mod_ne_one

def fullRecordGapValue05026 : Nat := fullRecordGapCenterValue + 226166

theorem fullRecordGapTerm05026_eq_value :
    recordGapCenter + 226166 = fullRecordGapValue05026 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05026_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05026 (fullRecordGapValue05026 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05026_not_prime : ¬(recordGapCenter + 226166).Prime := by
  rw [fullRecordGapTerm05026_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05026, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05026_fast_pow_mod_ne_one

def fullRecordGapValue05027 : Nat := fullRecordGapCenterValue + 226172

theorem fullRecordGapTerm05027_eq_value :
    recordGapCenter + 226172 = fullRecordGapValue05027 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05027_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05027 (fullRecordGapValue05027 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05027_not_prime : ¬(recordGapCenter + 226172).Prime := by
  rw [fullRecordGapTerm05027_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05027, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05027_fast_pow_mod_ne_one

def fullRecordGapValue05028 : Nat := fullRecordGapCenterValue + 226298

theorem fullRecordGapTerm05028_eq_value :
    recordGapCenter + 226298 = fullRecordGapValue05028 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05028_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05028 (fullRecordGapValue05028 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05028_not_prime : ¬(recordGapCenter + 226298).Prime := by
  rw [fullRecordGapTerm05028_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05028, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05028_fast_pow_mod_ne_one

def fullRecordGapValue05029 : Nat := fullRecordGapCenterValue + 226346

theorem fullRecordGapTerm05029_eq_value :
    recordGapCenter + 226346 = fullRecordGapValue05029 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05029_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05029 (fullRecordGapValue05029 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05029_not_prime : ¬(recordGapCenter + 226346).Prime := by
  rw [fullRecordGapTerm05029_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05029, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05029_fast_pow_mod_ne_one

def fullRecordGapValue05030 : Nat := fullRecordGapCenterValue + 226418

theorem fullRecordGapTerm05030_eq_value :
    recordGapCenter + 226418 = fullRecordGapValue05030 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05030_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05030 (fullRecordGapValue05030 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05030_not_prime : ¬(recordGapCenter + 226418).Prime := by
  rw [fullRecordGapTerm05030_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05030, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05030_fast_pow_mod_ne_one

def fullRecordGapValue05031 : Nat := fullRecordGapCenterValue + 226532

theorem fullRecordGapTerm05031_eq_value :
    recordGapCenter + 226532 = fullRecordGapValue05031 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05031_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05031 (fullRecordGapValue05031 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05031_not_prime : ¬(recordGapCenter + 226532).Prime := by
  rw [fullRecordGapTerm05031_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05031, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05031_fast_pow_mod_ne_one

def fullRecordGapValue05032 : Nat := fullRecordGapCenterValue + 226658

theorem fullRecordGapTerm05032_eq_value :
    recordGapCenter + 226658 = fullRecordGapValue05032 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05032_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05032 (fullRecordGapValue05032 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05032_not_prime : ¬(recordGapCenter + 226658).Prime := by
  rw [fullRecordGapTerm05032_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05032, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05032_fast_pow_mod_ne_one

def fullRecordGapValue05033 : Nat := fullRecordGapCenterValue + 226718

theorem fullRecordGapTerm05033_eq_value :
    recordGapCenter + 226718 = fullRecordGapValue05033 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05033_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05033 (fullRecordGapValue05033 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05033_not_prime : ¬(recordGapCenter + 226718).Prime := by
  rw [fullRecordGapTerm05033_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05033, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05033_fast_pow_mod_ne_one

def fullRecordGapValue05034 : Nat := fullRecordGapCenterValue + 226748

theorem fullRecordGapTerm05034_eq_value :
    recordGapCenter + 226748 = fullRecordGapValue05034 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05034_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05034 (fullRecordGapValue05034 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05034_not_prime : ¬(recordGapCenter + 226748).Prime := by
  rw [fullRecordGapTerm05034_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05034, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05034_fast_pow_mod_ne_one

def fullRecordGapValue05035 : Nat := fullRecordGapCenterValue + 226766

theorem fullRecordGapTerm05035_eq_value :
    recordGapCenter + 226766 = fullRecordGapValue05035 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05035_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05035 (fullRecordGapValue05035 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05035_not_prime : ¬(recordGapCenter + 226766).Prime := by
  rw [fullRecordGapTerm05035_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05035, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05035_fast_pow_mod_ne_one

def fullRecordGapValue05036 : Nat := fullRecordGapCenterValue + 227132

theorem fullRecordGapTerm05036_eq_value :
    recordGapCenter + 227132 = fullRecordGapValue05036 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05036_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05036 (fullRecordGapValue05036 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05036_not_prime : ¬(recordGapCenter + 227132).Prime := by
  rw [fullRecordGapTerm05036_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05036, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05036_fast_pow_mod_ne_one

def fullRecordGapValue05037 : Nat := fullRecordGapCenterValue + 227462

theorem fullRecordGapTerm05037_eq_value :
    recordGapCenter + 227462 = fullRecordGapValue05037 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05037_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05037 (fullRecordGapValue05037 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05037_not_prime : ¬(recordGapCenter + 227462).Prime := by
  rw [fullRecordGapTerm05037_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05037, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05037_fast_pow_mod_ne_one

def fullRecordGapValue05038 : Nat := fullRecordGapCenterValue + 227522

theorem fullRecordGapTerm05038_eq_value :
    recordGapCenter + 227522 = fullRecordGapValue05038 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05038_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05038 (fullRecordGapValue05038 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05038_not_prime : ¬(recordGapCenter + 227522).Prime := by
  rw [fullRecordGapTerm05038_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05038, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05038_fast_pow_mod_ne_one

def fullRecordGapValue05039 : Nat := fullRecordGapCenterValue + 227588

theorem fullRecordGapTerm05039_eq_value :
    recordGapCenter + 227588 = fullRecordGapValue05039 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05039_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05039 (fullRecordGapValue05039 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05039_not_prime : ¬(recordGapCenter + 227588).Prime := by
  rw [fullRecordGapTerm05039_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05039, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05039_fast_pow_mod_ne_one

def fullRecordGapValue05040 : Nat := fullRecordGapCenterValue + 227852

theorem fullRecordGapTerm05040_eq_value :
    recordGapCenter + 227852 = fullRecordGapValue05040 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05040_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05040 (fullRecordGapValue05040 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05040_not_prime : ¬(recordGapCenter + 227852).Prime := by
  rw [fullRecordGapTerm05040_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05040, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05040_fast_pow_mod_ne_one

def fullRecordGapValue05041 : Nat := fullRecordGapCenterValue + 227972

theorem fullRecordGapTerm05041_eq_value :
    recordGapCenter + 227972 = fullRecordGapValue05041 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05041_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05041 (fullRecordGapValue05041 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05041_not_prime : ¬(recordGapCenter + 227972).Prime := by
  rw [fullRecordGapTerm05041_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05041, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05041_fast_pow_mod_ne_one

def fullRecordGapValue05042 : Nat := fullRecordGapCenterValue + 227978

theorem fullRecordGapTerm05042_eq_value :
    recordGapCenter + 227978 = fullRecordGapValue05042 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05042_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05042 (fullRecordGapValue05042 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05042_not_prime : ¬(recordGapCenter + 227978).Prime := by
  rw [fullRecordGapTerm05042_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05042, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05042_fast_pow_mod_ne_one

def fullRecordGapValue05043 : Nat := fullRecordGapCenterValue + 228086

theorem fullRecordGapTerm05043_eq_value :
    recordGapCenter + 228086 = fullRecordGapValue05043 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05043_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05043 (fullRecordGapValue05043 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05043_not_prime : ¬(recordGapCenter + 228086).Prime := by
  rw [fullRecordGapTerm05043_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05043, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05043_fast_pow_mod_ne_one

def fullRecordGapValue05044 : Nat := fullRecordGapCenterValue + 228096

theorem fullRecordGapTerm05044_eq_value :
    recordGapCenter + 228096 = fullRecordGapValue05044 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05044_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05044 (fullRecordGapValue05044 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05044_not_prime : ¬(recordGapCenter + 228096).Prime := by
  rw [fullRecordGapTerm05044_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05044, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05044_fast_pow_mod_ne_one

def fullRecordGapValue05045 : Nat := fullRecordGapCenterValue + 228146

theorem fullRecordGapTerm05045_eq_value :
    recordGapCenter + 228146 = fullRecordGapValue05045 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05045_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05045 (fullRecordGapValue05045 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05045_not_prime : ¬(recordGapCenter + 228146).Prime := by
  rw [fullRecordGapTerm05045_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05045, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05045_fast_pow_mod_ne_one

def fullRecordGapValue05046 : Nat := fullRecordGapCenterValue + 228236

theorem fullRecordGapTerm05046_eq_value :
    recordGapCenter + 228236 = fullRecordGapValue05046 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05046_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05046 (fullRecordGapValue05046 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05046_not_prime : ¬(recordGapCenter + 228236).Prime := by
  rw [fullRecordGapTerm05046_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05046, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05046_fast_pow_mod_ne_one

def fullRecordGapValue05047 : Nat := fullRecordGapCenterValue + 228308

theorem fullRecordGapTerm05047_eq_value :
    recordGapCenter + 228308 = fullRecordGapValue05047 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05047_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05047 (fullRecordGapValue05047 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05047_not_prime : ¬(recordGapCenter + 228308).Prime := by
  rw [fullRecordGapTerm05047_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05047, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05047_fast_pow_mod_ne_one

def fullRecordGapValue05048 : Nat := fullRecordGapCenterValue + 228386

theorem fullRecordGapTerm05048_eq_value :
    recordGapCenter + 228386 = fullRecordGapValue05048 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05048_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05048 (fullRecordGapValue05048 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05048_not_prime : ¬(recordGapCenter + 228386).Prime := by
  rw [fullRecordGapTerm05048_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05048, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05048_fast_pow_mod_ne_one

def fullRecordGapValue05049 : Nat := fullRecordGapCenterValue + 228398

theorem fullRecordGapTerm05049_eq_value :
    recordGapCenter + 228398 = fullRecordGapValue05049 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05049_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05049 (fullRecordGapValue05049 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05049_not_prime : ¬(recordGapCenter + 228398).Prime := by
  rw [fullRecordGapTerm05049_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05049, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05049_fast_pow_mod_ne_one

def fullRecordGapValue05050 : Nat := fullRecordGapCenterValue + 228476

theorem fullRecordGapTerm05050_eq_value :
    recordGapCenter + 228476 = fullRecordGapValue05050 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05050_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05050 (fullRecordGapValue05050 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05050_not_prime : ¬(recordGapCenter + 228476).Prime := by
  rw [fullRecordGapTerm05050_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05050, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05050_fast_pow_mod_ne_one

def fullRecordGapValue05051 : Nat := fullRecordGapCenterValue + 228518

theorem fullRecordGapTerm05051_eq_value :
    recordGapCenter + 228518 = fullRecordGapValue05051 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05051_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05051 (fullRecordGapValue05051 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05051_not_prime : ¬(recordGapCenter + 228518).Prime := by
  rw [fullRecordGapTerm05051_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05051, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05051_fast_pow_mod_ne_one

def fullRecordGapValue05052 : Nat := fullRecordGapCenterValue + 228638

theorem fullRecordGapTerm05052_eq_value :
    recordGapCenter + 228638 = fullRecordGapValue05052 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05052_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05052 (fullRecordGapValue05052 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05052_not_prime : ¬(recordGapCenter + 228638).Prime := by
  rw [fullRecordGapTerm05052_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05052, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05052_fast_pow_mod_ne_one

def fullRecordGapValue05053 : Nat := fullRecordGapCenterValue + 228690

theorem fullRecordGapTerm05053_eq_value :
    recordGapCenter + 228690 = fullRecordGapValue05053 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05053_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05053 (fullRecordGapValue05053 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05053_not_prime : ¬(recordGapCenter + 228690).Prime := by
  rw [fullRecordGapTerm05053_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05053, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05053_fast_pow_mod_ne_one

def fullRecordGapValue05054 : Nat := fullRecordGapCenterValue + 228692

theorem fullRecordGapTerm05054_eq_value :
    recordGapCenter + 228692 = fullRecordGapValue05054 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05054_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05054 (fullRecordGapValue05054 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05054_not_prime : ¬(recordGapCenter + 228692).Prime := by
  rw [fullRecordGapTerm05054_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05054, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05054_fast_pow_mod_ne_one

def fullRecordGapValue05055 : Nat := fullRecordGapCenterValue + 228716

theorem fullRecordGapTerm05055_eq_value :
    recordGapCenter + 228716 = fullRecordGapValue05055 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05055_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05055 (fullRecordGapValue05055 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05055_not_prime : ¬(recordGapCenter + 228716).Prime := by
  rw [fullRecordGapTerm05055_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05055, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05055_fast_pow_mod_ne_one

def fullRecordGapValue05056 : Nat := fullRecordGapCenterValue + 228902

theorem fullRecordGapTerm05056_eq_value :
    recordGapCenter + 228902 = fullRecordGapValue05056 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05056_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05056 (fullRecordGapValue05056 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05056_not_prime : ¬(recordGapCenter + 228902).Prime := by
  rw [fullRecordGapTerm05056_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05056, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05056_fast_pow_mod_ne_one

def fullRecordGapValue05057 : Nat := fullRecordGapCenterValue + 229286

theorem fullRecordGapTerm05057_eq_value :
    recordGapCenter + 229286 = fullRecordGapValue05057 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05057_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05057 (fullRecordGapValue05057 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05057_not_prime : ¬(recordGapCenter + 229286).Prime := by
  rw [fullRecordGapTerm05057_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05057, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05057_fast_pow_mod_ne_one

def fullRecordGapValue05058 : Nat := fullRecordGapCenterValue + 229322

theorem fullRecordGapTerm05058_eq_value :
    recordGapCenter + 229322 = fullRecordGapValue05058 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05058_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05058 (fullRecordGapValue05058 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05058_not_prime : ¬(recordGapCenter + 229322).Prime := by
  rw [fullRecordGapTerm05058_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05058, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05058_fast_pow_mod_ne_one

def fullRecordGapValue05059 : Nat := fullRecordGapCenterValue + 229358

theorem fullRecordGapTerm05059_eq_value :
    recordGapCenter + 229358 = fullRecordGapValue05059 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05059_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05059 (fullRecordGapValue05059 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05059_not_prime : ¬(recordGapCenter + 229358).Prime := by
  rw [fullRecordGapTerm05059_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05059, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05059_fast_pow_mod_ne_one

def fullRecordGapValue05060 : Nat := fullRecordGapCenterValue + 229388

theorem fullRecordGapTerm05060_eq_value :
    recordGapCenter + 229388 = fullRecordGapValue05060 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05060_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05060 (fullRecordGapValue05060 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05060_not_prime : ¬(recordGapCenter + 229388).Prime := by
  rw [fullRecordGapTerm05060_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05060, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05060_fast_pow_mod_ne_one

def fullRecordGapValue05061 : Nat := fullRecordGapCenterValue + 229652

theorem fullRecordGapTerm05061_eq_value :
    recordGapCenter + 229652 = fullRecordGapValue05061 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05061_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05061 (fullRecordGapValue05061 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05061_not_prime : ¬(recordGapCenter + 229652).Prime := by
  rw [fullRecordGapTerm05061_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05061, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05061_fast_pow_mod_ne_one

def fullRecordGapValue05062 : Nat := fullRecordGapCenterValue + 229826

theorem fullRecordGapTerm05062_eq_value :
    recordGapCenter + 229826 = fullRecordGapValue05062 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05062_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05062 (fullRecordGapValue05062 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05062_not_prime : ¬(recordGapCenter + 229826).Prime := by
  rw [fullRecordGapTerm05062_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05062, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05062_fast_pow_mod_ne_one

def fullRecordGapValue05063 : Nat := fullRecordGapCenterValue + 230042

theorem fullRecordGapTerm05063_eq_value :
    recordGapCenter + 230042 = fullRecordGapValue05063 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05063_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05063 (fullRecordGapValue05063 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05063_not_prime : ¬(recordGapCenter + 230042).Prime := by
  rw [fullRecordGapTerm05063_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05063, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05063_fast_pow_mod_ne_one

def fullRecordGapValue05064 : Nat := fullRecordGapCenterValue + 230108

theorem fullRecordGapTerm05064_eq_value :
    recordGapCenter + 230108 = fullRecordGapValue05064 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05064_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05064 (fullRecordGapValue05064 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05064_not_prime : ¬(recordGapCenter + 230108).Prime := by
  rw [fullRecordGapTerm05064_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05064, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05064_fast_pow_mod_ne_one

def fullRecordGapValue05065 : Nat := fullRecordGapCenterValue + 230366

theorem fullRecordGapTerm05065_eq_value :
    recordGapCenter + 230366 = fullRecordGapValue05065 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05065_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05065 (fullRecordGapValue05065 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05065_not_prime : ¬(recordGapCenter + 230366).Prime := by
  rw [fullRecordGapTerm05065_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05065, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05065_fast_pow_mod_ne_one

def fullRecordGapValue05066 : Nat := fullRecordGapCenterValue + 230496

theorem fullRecordGapTerm05066_eq_value :
    recordGapCenter + 230496 = fullRecordGapValue05066 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05066_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05066 (fullRecordGapValue05066 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05066_not_prime : ¬(recordGapCenter + 230496).Prime := by
  rw [fullRecordGapTerm05066_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05066, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05066_fast_pow_mod_ne_one

def fullRecordGapValue05067 : Nat := fullRecordGapCenterValue + 230606

theorem fullRecordGapTerm05067_eq_value :
    recordGapCenter + 230606 = fullRecordGapValue05067 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05067_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05067 (fullRecordGapValue05067 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05067_not_prime : ¬(recordGapCenter + 230606).Prime := by
  rw [fullRecordGapTerm05067_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05067, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05067_fast_pow_mod_ne_one

def fullRecordGapValue05068 : Nat := fullRecordGapCenterValue + 230618

theorem fullRecordGapTerm05068_eq_value :
    recordGapCenter + 230618 = fullRecordGapValue05068 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05068_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05068 (fullRecordGapValue05068 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05068_not_prime : ¬(recordGapCenter + 230618).Prime := by
  rw [fullRecordGapTerm05068_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05068, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05068_fast_pow_mod_ne_one

def fullRecordGapValue05069 : Nat := fullRecordGapCenterValue + 230942

theorem fullRecordGapTerm05069_eq_value :
    recordGapCenter + 230942 = fullRecordGapValue05069 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05069_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05069 (fullRecordGapValue05069 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05069_not_prime : ¬(recordGapCenter + 230942).Prime := by
  rw [fullRecordGapTerm05069_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05069, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05069_fast_pow_mod_ne_one

def fullRecordGapValue05070 : Nat := fullRecordGapCenterValue + 231026

theorem fullRecordGapTerm05070_eq_value :
    recordGapCenter + 231026 = fullRecordGapValue05070 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05070_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05070 (fullRecordGapValue05070 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05070_not_prime : ¬(recordGapCenter + 231026).Prime := by
  rw [fullRecordGapTerm05070_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05070, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05070_fast_pow_mod_ne_one

def fullRecordGapValue05071 : Nat := fullRecordGapCenterValue + 231092

theorem fullRecordGapTerm05071_eq_value :
    recordGapCenter + 231092 = fullRecordGapValue05071 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05071_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05071 (fullRecordGapValue05071 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05071_not_prime : ¬(recordGapCenter + 231092).Prime := by
  rw [fullRecordGapTerm05071_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05071, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05071_fast_pow_mod_ne_one

def fullRecordGapValue05072 : Nat := fullRecordGapCenterValue + 231122

theorem fullRecordGapTerm05072_eq_value :
    recordGapCenter + 231122 = fullRecordGapValue05072 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05072_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05072 (fullRecordGapValue05072 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05072_not_prime : ¬(recordGapCenter + 231122).Prime := by
  rw [fullRecordGapTerm05072_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05072, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05072_fast_pow_mod_ne_one

def fullRecordGapValue05073 : Nat := fullRecordGapCenterValue + 231596

theorem fullRecordGapTerm05073_eq_value :
    recordGapCenter + 231596 = fullRecordGapValue05073 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05073_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05073 (fullRecordGapValue05073 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05073_not_prime : ¬(recordGapCenter + 231596).Prime := by
  rw [fullRecordGapTerm05073_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05073, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05073_fast_pow_mod_ne_one

def fullRecordGapValue05074 : Nat := fullRecordGapCenterValue + 231662

theorem fullRecordGapTerm05074_eq_value :
    recordGapCenter + 231662 = fullRecordGapValue05074 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05074_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05074 (fullRecordGapValue05074 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05074_not_prime : ¬(recordGapCenter + 231662).Prime := by
  rw [fullRecordGapTerm05074_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05074, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05074_fast_pow_mod_ne_one

def fullRecordGapValue05075 : Nat := fullRecordGapCenterValue + 231698

theorem fullRecordGapTerm05075_eq_value :
    recordGapCenter + 231698 = fullRecordGapValue05075 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05075_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05075 (fullRecordGapValue05075 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05075_not_prime : ¬(recordGapCenter + 231698).Prime := by
  rw [fullRecordGapTerm05075_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05075, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05075_fast_pow_mod_ne_one

def fullRecordGapValue05076 : Nat := fullRecordGapCenterValue + 231758

theorem fullRecordGapTerm05076_eq_value :
    recordGapCenter + 231758 = fullRecordGapValue05076 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05076_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05076 (fullRecordGapValue05076 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05076_not_prime : ¬(recordGapCenter + 231758).Prime := by
  rw [fullRecordGapTerm05076_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05076, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05076_fast_pow_mod_ne_one

def fullRecordGapValue05077 : Nat := fullRecordGapCenterValue + 231866

theorem fullRecordGapTerm05077_eq_value :
    recordGapCenter + 231866 = fullRecordGapValue05077 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05077_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05077 (fullRecordGapValue05077 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05077_not_prime : ¬(recordGapCenter + 231866).Prime := by
  rw [fullRecordGapTerm05077_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05077, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05077_fast_pow_mod_ne_one

def fullRecordGapValue05078 : Nat := fullRecordGapCenterValue + 231908

theorem fullRecordGapTerm05078_eq_value :
    recordGapCenter + 231908 = fullRecordGapValue05078 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05078_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05078 (fullRecordGapValue05078 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05078_not_prime : ¬(recordGapCenter + 231908).Prime := by
  rw [fullRecordGapTerm05078_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05078, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05078_fast_pow_mod_ne_one

def fullRecordGapValue05079 : Nat := fullRecordGapCenterValue + 232178

theorem fullRecordGapTerm05079_eq_value :
    recordGapCenter + 232178 = fullRecordGapValue05079 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05079_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05079 (fullRecordGapValue05079 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05079_not_prime : ¬(recordGapCenter + 232178).Prime := by
  rw [fullRecordGapTerm05079_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05079, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05079_fast_pow_mod_ne_one

def fullRecordGapValue05080 : Nat := fullRecordGapCenterValue + 232226

theorem fullRecordGapTerm05080_eq_value :
    recordGapCenter + 232226 = fullRecordGapValue05080 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05080_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05080 (fullRecordGapValue05080 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05080_not_prime : ¬(recordGapCenter + 232226).Prime := by
  rw [fullRecordGapTerm05080_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05080, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05080_fast_pow_mod_ne_one

def fullRecordGapValue05081 : Nat := fullRecordGapCenterValue + 232262

theorem fullRecordGapTerm05081_eq_value :
    recordGapCenter + 232262 = fullRecordGapValue05081 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05081_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05081 (fullRecordGapValue05081 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05081_not_prime : ¬(recordGapCenter + 232262).Prime := by
  rw [fullRecordGapTerm05081_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05081, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05081_fast_pow_mod_ne_one

def fullRecordGapValue05082 : Nat := fullRecordGapCenterValue + 232268

theorem fullRecordGapTerm05082_eq_value :
    recordGapCenter + 232268 = fullRecordGapValue05082 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05082_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05082 (fullRecordGapValue05082 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05082_not_prime : ¬(recordGapCenter + 232268).Prime := by
  rw [fullRecordGapTerm05082_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05082, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05082_fast_pow_mod_ne_one

def fullRecordGapValue05083 : Nat := fullRecordGapCenterValue + 232292

theorem fullRecordGapTerm05083_eq_value :
    recordGapCenter + 232292 = fullRecordGapValue05083 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05083_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05083 (fullRecordGapValue05083 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05083_not_prime : ¬(recordGapCenter + 232292).Prime := by
  rw [fullRecordGapTerm05083_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05083, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05083_fast_pow_mod_ne_one

def fullRecordGapValue05084 : Nat := fullRecordGapCenterValue + 232320

theorem fullRecordGapTerm05084_eq_value :
    recordGapCenter + 232320 = fullRecordGapValue05084 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05084_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05084 (fullRecordGapValue05084 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05084_not_prime : ¬(recordGapCenter + 232320).Prime := by
  rw [fullRecordGapTerm05084_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05084, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05084_fast_pow_mod_ne_one

def fullRecordGapValue05085 : Nat := fullRecordGapCenterValue + 232682

theorem fullRecordGapTerm05085_eq_value :
    recordGapCenter + 232682 = fullRecordGapValue05085 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05085_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05085 (fullRecordGapValue05085 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05085_not_prime : ¬(recordGapCenter + 232682).Prime := by
  rw [fullRecordGapTerm05085_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05085, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05085_fast_pow_mod_ne_one

def fullRecordGapValue05086 : Nat := fullRecordGapCenterValue + 232796

theorem fullRecordGapTerm05086_eq_value :
    recordGapCenter + 232796 = fullRecordGapValue05086 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05086_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05086 (fullRecordGapValue05086 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05086_not_prime : ¬(recordGapCenter + 232796).Prime := by
  rw [fullRecordGapTerm05086_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05086, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05086_fast_pow_mod_ne_one

def fullRecordGapValue05087 : Nat := fullRecordGapCenterValue + 232916

theorem fullRecordGapTerm05087_eq_value :
    recordGapCenter + 232916 = fullRecordGapValue05087 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05087_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05087 (fullRecordGapValue05087 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05087_not_prime : ¬(recordGapCenter + 232916).Prime := by
  rw [fullRecordGapTerm05087_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05087, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05087_fast_pow_mod_ne_one

def fullRecordGapValue05088 : Nat := fullRecordGapCenterValue + 233186

theorem fullRecordGapTerm05088_eq_value :
    recordGapCenter + 233186 = fullRecordGapValue05088 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05088_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05088 (fullRecordGapValue05088 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05088_not_prime : ¬(recordGapCenter + 233186).Prime := by
  rw [fullRecordGapTerm05088_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05088, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05088_fast_pow_mod_ne_one

def fullRecordGapValue05089 : Nat := fullRecordGapCenterValue + 233348

theorem fullRecordGapTerm05089_eq_value :
    recordGapCenter + 233348 = fullRecordGapValue05089 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05089_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05089 (fullRecordGapValue05089 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05089_not_prime : ¬(recordGapCenter + 233348).Prime := by
  rw [fullRecordGapTerm05089_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05089, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05089_fast_pow_mod_ne_one

def fullRecordGapValue05090 : Nat := fullRecordGapCenterValue + 233378

theorem fullRecordGapTerm05090_eq_value :
    recordGapCenter + 233378 = fullRecordGapValue05090 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05090_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05090 (fullRecordGapValue05090 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05090_not_prime : ¬(recordGapCenter + 233378).Prime := by
  rw [fullRecordGapTerm05090_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05090, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05090_fast_pow_mod_ne_one

def fullRecordGapValue05091 : Nat := fullRecordGapCenterValue + 233462

theorem fullRecordGapTerm05091_eq_value :
    recordGapCenter + 233462 = fullRecordGapValue05091 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05091_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05091 (fullRecordGapValue05091 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05091_not_prime : ¬(recordGapCenter + 233462).Prime := by
  rw [fullRecordGapTerm05091_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05091, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05091_fast_pow_mod_ne_one

def fullRecordGapValue05092 : Nat := fullRecordGapCenterValue + 233756

theorem fullRecordGapTerm05092_eq_value :
    recordGapCenter + 233756 = fullRecordGapValue05092 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05092_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05092 (fullRecordGapValue05092 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05092_not_prime : ¬(recordGapCenter + 233756).Prime := by
  rw [fullRecordGapTerm05092_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05092, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05092_fast_pow_mod_ne_one

def fullRecordGapValue05093 : Nat := fullRecordGapCenterValue + 233822

theorem fullRecordGapTerm05093_eq_value :
    recordGapCenter + 233822 = fullRecordGapValue05093 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05093_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05093 (fullRecordGapValue05093 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05093_not_prime : ¬(recordGapCenter + 233822).Prime := by
  rw [fullRecordGapTerm05093_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05093, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05093_fast_pow_mod_ne_one

def fullRecordGapValue05094 : Nat := fullRecordGapCenterValue + 233858

theorem fullRecordGapTerm05094_eq_value :
    recordGapCenter + 233858 = fullRecordGapValue05094 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05094_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05094 (fullRecordGapValue05094 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05094_not_prime : ¬(recordGapCenter + 233858).Prime := by
  rw [fullRecordGapTerm05094_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05094, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05094_fast_pow_mod_ne_one

def fullRecordGapValue05095 : Nat := fullRecordGapCenterValue + 234326

theorem fullRecordGapTerm05095_eq_value :
    recordGapCenter + 234326 = fullRecordGapValue05095 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05095_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05095 (fullRecordGapValue05095 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05095_not_prime : ¬(recordGapCenter + 234326).Prime := by
  rw [fullRecordGapTerm05095_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05095, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05095_fast_pow_mod_ne_one

def fullRecordGapValue05096 : Nat := fullRecordGapCenterValue + 234386

theorem fullRecordGapTerm05096_eq_value :
    recordGapCenter + 234386 = fullRecordGapValue05096 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05096_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05096 (fullRecordGapValue05096 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05096_not_prime : ¬(recordGapCenter + 234386).Prime := by
  rw [fullRecordGapTerm05096_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05096, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05096_fast_pow_mod_ne_one

def fullRecordGapValue05097 : Nat := fullRecordGapCenterValue + 234518

theorem fullRecordGapTerm05097_eq_value :
    recordGapCenter + 234518 = fullRecordGapValue05097 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05097_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05097 (fullRecordGapValue05097 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05097_not_prime : ¬(recordGapCenter + 234518).Prime := by
  rw [fullRecordGapTerm05097_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05097, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05097_fast_pow_mod_ne_one

def fullRecordGapValue05098 : Nat := fullRecordGapCenterValue + 234722

theorem fullRecordGapTerm05098_eq_value :
    recordGapCenter + 234722 = fullRecordGapValue05098 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05098_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05098 (fullRecordGapValue05098 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05098_not_prime : ¬(recordGapCenter + 234722).Prime := by
  rw [fullRecordGapTerm05098_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05098, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05098_fast_pow_mod_ne_one

def fullRecordGapValue05099 : Nat := fullRecordGapCenterValue + 234932

theorem fullRecordGapTerm05099_eq_value :
    recordGapCenter + 234932 = fullRecordGapValue05099 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05099_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05099 (fullRecordGapValue05099 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05099_not_prime : ¬(recordGapCenter + 234932).Prime := by
  rw [fullRecordGapTerm05099_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05099, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05099_fast_pow_mod_ne_one

def fullRecordGapValue05100 : Nat := fullRecordGapCenterValue + 234998

theorem fullRecordGapTerm05100_eq_value :
    recordGapCenter + 234998 = fullRecordGapValue05100 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05100_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05100 (fullRecordGapValue05100 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05100_not_prime : ¬(recordGapCenter + 234998).Prime := by
  rw [fullRecordGapTerm05100_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05100, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05100_fast_pow_mod_ne_one

def fullRecordGapValue05101 : Nat := fullRecordGapCenterValue + 235028

theorem fullRecordGapTerm05101_eq_value :
    recordGapCenter + 235028 = fullRecordGapValue05101 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05101_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05101 (fullRecordGapValue05101 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05101_not_prime : ¬(recordGapCenter + 235028).Prime := by
  rw [fullRecordGapTerm05101_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05101, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05101_fast_pow_mod_ne_one

def fullRecordGapValue05102 : Nat := fullRecordGapCenterValue + 235406

theorem fullRecordGapTerm05102_eq_value :
    recordGapCenter + 235406 = fullRecordGapValue05102 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05102_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05102 (fullRecordGapValue05102 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05102_not_prime : ¬(recordGapCenter + 235406).Prime := by
  rw [fullRecordGapTerm05102_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05102, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05102_fast_pow_mod_ne_one

def fullRecordGapValue05103 : Nat := fullRecordGapCenterValue + 235442

theorem fullRecordGapTerm05103_eq_value :
    recordGapCenter + 235442 = fullRecordGapValue05103 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05103_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05103 (fullRecordGapValue05103 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05103_not_prime : ¬(recordGapCenter + 235442).Prime := by
  rw [fullRecordGapTerm05103_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05103, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05103_fast_pow_mod_ne_one

def fullRecordGapValue05104 : Nat := fullRecordGapCenterValue + 235526

theorem fullRecordGapTerm05104_eq_value :
    recordGapCenter + 235526 = fullRecordGapValue05104 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05104_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05104 (fullRecordGapValue05104 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05104_not_prime : ¬(recordGapCenter + 235526).Prime := by
  rw [fullRecordGapTerm05104_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05104, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05104_fast_pow_mod_ne_one

def fullRecordGapValue05105 : Nat := fullRecordGapCenterValue + 235652

theorem fullRecordGapTerm05105_eq_value :
    recordGapCenter + 235652 = fullRecordGapValue05105 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05105_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05105 (fullRecordGapValue05105 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05105_not_prime : ¬(recordGapCenter + 235652).Prime := by
  rw [fullRecordGapTerm05105_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05105, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05105_fast_pow_mod_ne_one

def fullRecordGapValue05106 : Nat := fullRecordGapCenterValue + 235778

theorem fullRecordGapTerm05106_eq_value :
    recordGapCenter + 235778 = fullRecordGapValue05106 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05106_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05106 (fullRecordGapValue05106 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05106_not_prime : ¬(recordGapCenter + 235778).Prime := by
  rw [fullRecordGapTerm05106_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05106, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05106_fast_pow_mod_ne_one

def fullRecordGapValue05107 : Nat := fullRecordGapCenterValue + 235982

theorem fullRecordGapTerm05107_eq_value :
    recordGapCenter + 235982 = fullRecordGapValue05107 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05107_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05107 (fullRecordGapValue05107 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05107_not_prime : ¬(recordGapCenter + 235982).Prime := by
  rw [fullRecordGapTerm05107_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05107, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05107_fast_pow_mod_ne_one

def fullRecordGapValue05108 : Nat := fullRecordGapCenterValue + 235988

theorem fullRecordGapTerm05108_eq_value :
    recordGapCenter + 235988 = fullRecordGapValue05108 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05108_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05108 (fullRecordGapValue05108 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05108_not_prime : ¬(recordGapCenter + 235988).Prime := by
  rw [fullRecordGapTerm05108_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05108, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05108_fast_pow_mod_ne_one

def fullRecordGapValue05109 : Nat := fullRecordGapCenterValue + 236066

theorem fullRecordGapTerm05109_eq_value :
    recordGapCenter + 236066 = fullRecordGapValue05109 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05109_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05109 (fullRecordGapValue05109 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05109_not_prime : ¬(recordGapCenter + 236066).Prime := by
  rw [fullRecordGapTerm05109_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05109, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05109_fast_pow_mod_ne_one

def fullRecordGapValue05110 : Nat := fullRecordGapCenterValue + 236196

theorem fullRecordGapTerm05110_eq_value :
    recordGapCenter + 236196 = fullRecordGapValue05110 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05110_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05110 (fullRecordGapValue05110 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05110_not_prime : ¬(recordGapCenter + 236196).Prime := by
  rw [fullRecordGapTerm05110_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05110, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05110_fast_pow_mod_ne_one

def fullRecordGapValue05111 : Nat := fullRecordGapCenterValue + 236250

theorem fullRecordGapTerm05111_eq_value :
    recordGapCenter + 236250 = fullRecordGapValue05111 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05111_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05111 (fullRecordGapValue05111 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05111_not_prime : ¬(recordGapCenter + 236250).Prime := by
  rw [fullRecordGapTerm05111_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05111, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05111_fast_pow_mod_ne_one

def fullRecordGapValue05112 : Nat := fullRecordGapCenterValue + 236378

theorem fullRecordGapTerm05112_eq_value :
    recordGapCenter + 236378 = fullRecordGapValue05112 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05112_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05112 (fullRecordGapValue05112 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05112_not_prime : ¬(recordGapCenter + 236378).Prime := by
  rw [fullRecordGapTerm05112_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05112, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05112_fast_pow_mod_ne_one

def fullRecordGapValue05113 : Nat := fullRecordGapCenterValue + 236426

theorem fullRecordGapTerm05113_eq_value :
    recordGapCenter + 236426 = fullRecordGapValue05113 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05113_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05113 (fullRecordGapValue05113 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05113_not_prime : ¬(recordGapCenter + 236426).Prime := by
  rw [fullRecordGapTerm05113_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05113, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05113_fast_pow_mod_ne_one

def fullRecordGapValue05114 : Nat := fullRecordGapCenterValue + 236636

theorem fullRecordGapTerm05114_eq_value :
    recordGapCenter + 236636 = fullRecordGapValue05114 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05114_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05114 (fullRecordGapValue05114 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05114_not_prime : ¬(recordGapCenter + 236636).Prime := by
  rw [fullRecordGapTerm05114_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05114, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05114_fast_pow_mod_ne_one

def fullRecordGapValue05115 : Nat := fullRecordGapCenterValue + 236798

theorem fullRecordGapTerm05115_eq_value :
    recordGapCenter + 236798 = fullRecordGapValue05115 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05115_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05115 (fullRecordGapValue05115 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05115_not_prime : ¬(recordGapCenter + 236798).Prime := by
  rw [fullRecordGapTerm05115_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05115, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05115_fast_pow_mod_ne_one

def fullRecordGapValue05116 : Nat := fullRecordGapCenterValue + 236822

theorem fullRecordGapTerm05116_eq_value :
    recordGapCenter + 236822 = fullRecordGapValue05116 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05116_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05116 (fullRecordGapValue05116 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05116_not_prime : ¬(recordGapCenter + 236822).Prime := by
  rw [fullRecordGapTerm05116_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05116, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05116_fast_pow_mod_ne_one

def fullRecordGapValue05117 : Nat := fullRecordGapCenterValue + 236828

theorem fullRecordGapTerm05117_eq_value :
    recordGapCenter + 236828 = fullRecordGapValue05117 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05117_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05117 (fullRecordGapValue05117 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05117_not_prime : ¬(recordGapCenter + 236828).Prime := by
  rw [fullRecordGapTerm05117_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05117, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05117_fast_pow_mod_ne_one

def fullRecordGapValue05118 : Nat := fullRecordGapCenterValue + 236846

theorem fullRecordGapTerm05118_eq_value :
    recordGapCenter + 236846 = fullRecordGapValue05118 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05118_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05118 (fullRecordGapValue05118 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05118_not_prime : ¬(recordGapCenter + 236846).Prime := by
  rw [fullRecordGapTerm05118_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05118, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05118_fast_pow_mod_ne_one

def fullRecordGapValue05119 : Nat := fullRecordGapCenterValue + 236906

theorem fullRecordGapTerm05119_eq_value :
    recordGapCenter + 236906 = fullRecordGapValue05119 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05119_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05119 (fullRecordGapValue05119 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05119_not_prime : ¬(recordGapCenter + 236906).Prime := by
  rw [fullRecordGapTerm05119_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05119, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05119_fast_pow_mod_ne_one

def fullRecordGapValue05120 : Nat := fullRecordGapCenterValue + 236972

theorem fullRecordGapTerm05120_eq_value :
    recordGapCenter + 236972 = fullRecordGapValue05120 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05120_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05120 (fullRecordGapValue05120 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05120_not_prime : ¬(recordGapCenter + 236972).Prime := by
  rw [fullRecordGapTerm05120_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05120, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05120_fast_pow_mod_ne_one

end PrimeFactorUnimodality
