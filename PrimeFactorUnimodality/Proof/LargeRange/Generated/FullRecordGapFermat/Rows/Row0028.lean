import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue06913 : Nat := fullRecordGapCenterValue + 387462

theorem fullRecordGapTerm06913_eq_value :
    recordGapCenter + 387462 = fullRecordGapValue06913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06913 (fullRecordGapValue06913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06913_not_prime : ¬(recordGapCenter + 387462).Prime := by
  rw [fullRecordGapTerm06913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06913_fast_pow_mod_ne_one

def fullRecordGapValue06914 : Nat := fullRecordGapCenterValue + 387546

theorem fullRecordGapTerm06914_eq_value :
    recordGapCenter + 387546 = fullRecordGapValue06914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06914 (fullRecordGapValue06914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06914_not_prime : ¬(recordGapCenter + 387546).Prime := by
  rw [fullRecordGapTerm06914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06914_fast_pow_mod_ne_one

def fullRecordGapValue06915 : Nat := fullRecordGapCenterValue + 387578

theorem fullRecordGapTerm06915_eq_value :
    recordGapCenter + 387578 = fullRecordGapValue06915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06915 (fullRecordGapValue06915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06915_not_prime : ¬(recordGapCenter + 387578).Prime := by
  rw [fullRecordGapTerm06915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06915_fast_pow_mod_ne_one

def fullRecordGapValue06916 : Nat := fullRecordGapCenterValue + 387606

theorem fullRecordGapTerm06916_eq_value :
    recordGapCenter + 387606 = fullRecordGapValue06916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06916 (fullRecordGapValue06916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06916_not_prime : ¬(recordGapCenter + 387606).Prime := by
  rw [fullRecordGapTerm06916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06916_fast_pow_mod_ne_one

def fullRecordGapValue06917 : Nat := fullRecordGapCenterValue + 387626

theorem fullRecordGapTerm06917_eq_value :
    recordGapCenter + 387626 = fullRecordGapValue06917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06917 (fullRecordGapValue06917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06917_not_prime : ¬(recordGapCenter + 387626).Prime := by
  rw [fullRecordGapTerm06917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06917_fast_pow_mod_ne_one

def fullRecordGapValue06918 : Nat := fullRecordGapCenterValue + 387836

theorem fullRecordGapTerm06918_eq_value :
    recordGapCenter + 387836 = fullRecordGapValue06918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06918 (fullRecordGapValue06918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06918_not_prime : ¬(recordGapCenter + 387836).Prime := by
  rw [fullRecordGapTerm06918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06918_fast_pow_mod_ne_one

def fullRecordGapValue06919 : Nat := fullRecordGapCenterValue + 387896

theorem fullRecordGapTerm06919_eq_value :
    recordGapCenter + 387896 = fullRecordGapValue06919 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06919_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06919 (fullRecordGapValue06919 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06919_not_prime : ¬(recordGapCenter + 387896).Prime := by
  rw [fullRecordGapTerm06919_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06919, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06919_fast_pow_mod_ne_one

def fullRecordGapValue06920 : Nat := fullRecordGapCenterValue + 387978

theorem fullRecordGapTerm06920_eq_value :
    recordGapCenter + 387978 = fullRecordGapValue06920 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06920_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06920 (fullRecordGapValue06920 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06920_not_prime : ¬(recordGapCenter + 387978).Prime := by
  rw [fullRecordGapTerm06920_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06920, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06920_fast_pow_mod_ne_one

def fullRecordGapValue06921 : Nat := fullRecordGapCenterValue + 388028

theorem fullRecordGapTerm06921_eq_value :
    recordGapCenter + 388028 = fullRecordGapValue06921 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06921_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06921 (fullRecordGapValue06921 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06921_not_prime : ¬(recordGapCenter + 388028).Prime := by
  rw [fullRecordGapTerm06921_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06921, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06921_fast_pow_mod_ne_one

def fullRecordGapValue06922 : Nat := fullRecordGapCenterValue + 388080

theorem fullRecordGapTerm06922_eq_value :
    recordGapCenter + 388080 = fullRecordGapValue06922 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06922_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06922 (fullRecordGapValue06922 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06922_not_prime : ¬(recordGapCenter + 388080).Prime := by
  rw [fullRecordGapTerm06922_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06922, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06922_fast_pow_mod_ne_one

def fullRecordGapValue06923 : Nat := fullRecordGapCenterValue + 388158

theorem fullRecordGapTerm06923_eq_value :
    recordGapCenter + 388158 = fullRecordGapValue06923 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06923_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06923 (fullRecordGapValue06923 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06923_not_prime : ¬(recordGapCenter + 388158).Prime := by
  rw [fullRecordGapTerm06923_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06923, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06923_fast_pow_mod_ne_one

def fullRecordGapValue06924 : Nat := fullRecordGapCenterValue + 388166

theorem fullRecordGapTerm06924_eq_value :
    recordGapCenter + 388166 = fullRecordGapValue06924 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06924_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06924 (fullRecordGapValue06924 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06924_not_prime : ¬(recordGapCenter + 388166).Prime := by
  rw [fullRecordGapTerm06924_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06924, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06924_fast_pow_mod_ne_one

def fullRecordGapValue06925 : Nat := fullRecordGapCenterValue + 388202

theorem fullRecordGapTerm06925_eq_value :
    recordGapCenter + 388202 = fullRecordGapValue06925 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06925_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06925 (fullRecordGapValue06925 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06925_not_prime : ¬(recordGapCenter + 388202).Prime := by
  rw [fullRecordGapTerm06925_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06925, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06925_fast_pow_mod_ne_one

def fullRecordGapValue06926 : Nat := fullRecordGapCenterValue + 388238

theorem fullRecordGapTerm06926_eq_value :
    recordGapCenter + 388238 = fullRecordGapValue06926 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06926_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06926 (fullRecordGapValue06926 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06926_not_prime : ¬(recordGapCenter + 388238).Prime := by
  rw [fullRecordGapTerm06926_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06926, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06926_fast_pow_mod_ne_one

def fullRecordGapValue06927 : Nat := fullRecordGapCenterValue + 388298

theorem fullRecordGapTerm06927_eq_value :
    recordGapCenter + 388298 = fullRecordGapValue06927 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06927_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06927 (fullRecordGapValue06927 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06927_not_prime : ¬(recordGapCenter + 388298).Prime := by
  rw [fullRecordGapTerm06927_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06927, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06927_fast_pow_mod_ne_one

def fullRecordGapValue06928 : Nat := fullRecordGapCenterValue + 388328

theorem fullRecordGapTerm06928_eq_value :
    recordGapCenter + 388328 = fullRecordGapValue06928 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06928_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06928 (fullRecordGapValue06928 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06928_not_prime : ¬(recordGapCenter + 388328).Prime := by
  rw [fullRecordGapTerm06928_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06928, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06928_fast_pow_mod_ne_one

def fullRecordGapValue06929 : Nat := fullRecordGapCenterValue + 388412

theorem fullRecordGapTerm06929_eq_value :
    recordGapCenter + 388412 = fullRecordGapValue06929 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06929_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06929 (fullRecordGapValue06929 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06929_not_prime : ¬(recordGapCenter + 388412).Prime := by
  rw [fullRecordGapTerm06929_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06929, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06929_fast_pow_mod_ne_one

def fullRecordGapValue06930 : Nat := fullRecordGapCenterValue + 388568

theorem fullRecordGapTerm06930_eq_value :
    recordGapCenter + 388568 = fullRecordGapValue06930 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06930_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06930 (fullRecordGapValue06930 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06930_not_prime : ¬(recordGapCenter + 388568).Prime := by
  rw [fullRecordGapTerm06930_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06930, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06930_fast_pow_mod_ne_one

def fullRecordGapValue06931 : Nat := fullRecordGapCenterValue + 388686

theorem fullRecordGapTerm06931_eq_value :
    recordGapCenter + 388686 = fullRecordGapValue06931 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06931_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06931 (fullRecordGapValue06931 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06931_not_prime : ¬(recordGapCenter + 388686).Prime := by
  rw [fullRecordGapTerm06931_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06931, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06931_fast_pow_mod_ne_one

def fullRecordGapValue06932 : Nat := fullRecordGapCenterValue + 388742

theorem fullRecordGapTerm06932_eq_value :
    recordGapCenter + 388742 = fullRecordGapValue06932 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06932_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06932 (fullRecordGapValue06932 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06932_not_prime : ¬(recordGapCenter + 388742).Prime := by
  rw [fullRecordGapTerm06932_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06932, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06932_fast_pow_mod_ne_one

def fullRecordGapValue06933 : Nat := fullRecordGapCenterValue + 388748

theorem fullRecordGapTerm06933_eq_value :
    recordGapCenter + 388748 = fullRecordGapValue06933 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06933_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06933 (fullRecordGapValue06933 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06933_not_prime : ¬(recordGapCenter + 388748).Prime := by
  rw [fullRecordGapTerm06933_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06933, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06933_fast_pow_mod_ne_one

def fullRecordGapValue06934 : Nat := fullRecordGapCenterValue + 388826

theorem fullRecordGapTerm06934_eq_value :
    recordGapCenter + 388826 = fullRecordGapValue06934 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06934_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06934 (fullRecordGapValue06934 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06934_not_prime : ¬(recordGapCenter + 388826).Prime := by
  rw [fullRecordGapTerm06934_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06934, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06934_fast_pow_mod_ne_one

def fullRecordGapValue06935 : Nat := fullRecordGapCenterValue + 388862

theorem fullRecordGapTerm06935_eq_value :
    recordGapCenter + 388862 = fullRecordGapValue06935 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06935_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06935 (fullRecordGapValue06935 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06935_not_prime : ¬(recordGapCenter + 388862).Prime := by
  rw [fullRecordGapTerm06935_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06935, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06935_fast_pow_mod_ne_one

def fullRecordGapValue06936 : Nat := fullRecordGapCenterValue + 388866

theorem fullRecordGapTerm06936_eq_value :
    recordGapCenter + 388866 = fullRecordGapValue06936 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06936_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06936 (fullRecordGapValue06936 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06936_not_prime : ¬(recordGapCenter + 388866).Prime := by
  rw [fullRecordGapTerm06936_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06936, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06936_fast_pow_mod_ne_one

def fullRecordGapValue06937 : Nat := fullRecordGapCenterValue + 388902

theorem fullRecordGapTerm06937_eq_value :
    recordGapCenter + 388902 = fullRecordGapValue06937 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06937_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06937 (fullRecordGapValue06937 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06937_not_prime : ¬(recordGapCenter + 388902).Prime := by
  rw [fullRecordGapTerm06937_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06937, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06937_fast_pow_mod_ne_one

def fullRecordGapValue06938 : Nat := fullRecordGapCenterValue + 388958

theorem fullRecordGapTerm06938_eq_value :
    recordGapCenter + 388958 = fullRecordGapValue06938 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06938_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06938 (fullRecordGapValue06938 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06938_not_prime : ¬(recordGapCenter + 388958).Prime := by
  rw [fullRecordGapTerm06938_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06938, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06938_fast_pow_mod_ne_one

def fullRecordGapValue06939 : Nat := fullRecordGapCenterValue + 389042

theorem fullRecordGapTerm06939_eq_value :
    recordGapCenter + 389042 = fullRecordGapValue06939 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06939_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06939 (fullRecordGapValue06939 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06939_not_prime : ¬(recordGapCenter + 389042).Prime := by
  rw [fullRecordGapTerm06939_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06939, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06939_fast_pow_mod_ne_one

def fullRecordGapValue06940 : Nat := fullRecordGapCenterValue + 389118

theorem fullRecordGapTerm06940_eq_value :
    recordGapCenter + 389118 = fullRecordGapValue06940 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06940_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06940 (fullRecordGapValue06940 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06940_not_prime : ¬(recordGapCenter + 389118).Prime := by
  rw [fullRecordGapTerm06940_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06940, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06940_fast_pow_mod_ne_one

def fullRecordGapValue06941 : Nat := fullRecordGapCenterValue + 389432

theorem fullRecordGapTerm06941_eq_value :
    recordGapCenter + 389432 = fullRecordGapValue06941 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06941_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06941 (fullRecordGapValue06941 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06941_not_prime : ¬(recordGapCenter + 389432).Prime := by
  rw [fullRecordGapTerm06941_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06941, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06941_fast_pow_mod_ne_one

def fullRecordGapValue06942 : Nat := fullRecordGapCenterValue + 389492

theorem fullRecordGapTerm06942_eq_value :
    recordGapCenter + 389492 = fullRecordGapValue06942 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06942_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06942 (fullRecordGapValue06942 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06942_not_prime : ¬(recordGapCenter + 389492).Prime := by
  rw [fullRecordGapTerm06942_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06942, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06942_fast_pow_mod_ne_one

def fullRecordGapValue06943 : Nat := fullRecordGapCenterValue + 389526

theorem fullRecordGapTerm06943_eq_value :
    recordGapCenter + 389526 = fullRecordGapValue06943 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06943_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06943 (fullRecordGapValue06943 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06943_not_prime : ¬(recordGapCenter + 389526).Prime := by
  rw [fullRecordGapTerm06943_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06943, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06943_fast_pow_mod_ne_one

def fullRecordGapValue06944 : Nat := fullRecordGapCenterValue + 389562

theorem fullRecordGapTerm06944_eq_value :
    recordGapCenter + 389562 = fullRecordGapValue06944 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06944_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06944 (fullRecordGapValue06944 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06944_not_prime : ¬(recordGapCenter + 389562).Prime := by
  rw [fullRecordGapTerm06944_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06944, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06944_fast_pow_mod_ne_one

def fullRecordGapValue06945 : Nat := fullRecordGapCenterValue + 389678

theorem fullRecordGapTerm06945_eq_value :
    recordGapCenter + 389678 = fullRecordGapValue06945 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06945_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06945 (fullRecordGapValue06945 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06945_not_prime : ¬(recordGapCenter + 389678).Prime := by
  rw [fullRecordGapTerm06945_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06945, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06945_fast_pow_mod_ne_one

def fullRecordGapValue06946 : Nat := fullRecordGapCenterValue + 389706

theorem fullRecordGapTerm06946_eq_value :
    recordGapCenter + 389706 = fullRecordGapValue06946 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06946_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06946 (fullRecordGapValue06946 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06946_not_prime : ¬(recordGapCenter + 389706).Prime := by
  rw [fullRecordGapTerm06946_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06946, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06946_fast_pow_mod_ne_one

def fullRecordGapValue06947 : Nat := fullRecordGapCenterValue + 389798

theorem fullRecordGapTerm06947_eq_value :
    recordGapCenter + 389798 = fullRecordGapValue06947 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06947_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06947 (fullRecordGapValue06947 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06947_not_prime : ¬(recordGapCenter + 389798).Prime := by
  rw [fullRecordGapTerm06947_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06947, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06947_fast_pow_mod_ne_one

def fullRecordGapValue06948 : Nat := fullRecordGapCenterValue + 389996

theorem fullRecordGapTerm06948_eq_value :
    recordGapCenter + 389996 = fullRecordGapValue06948 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06948_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06948 (fullRecordGapValue06948 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06948_not_prime : ¬(recordGapCenter + 389996).Prime := by
  rw [fullRecordGapTerm06948_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06948, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06948_fast_pow_mod_ne_one

def fullRecordGapValue06949 : Nat := fullRecordGapCenterValue + 390086

theorem fullRecordGapTerm06949_eq_value :
    recordGapCenter + 390086 = fullRecordGapValue06949 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06949_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06949 (fullRecordGapValue06949 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06949_not_prime : ¬(recordGapCenter + 390086).Prime := by
  rw [fullRecordGapTerm06949_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06949, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06949_fast_pow_mod_ne_one

def fullRecordGapValue06950 : Nat := fullRecordGapCenterValue + 390092

theorem fullRecordGapTerm06950_eq_value :
    recordGapCenter + 390092 = fullRecordGapValue06950 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06950_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06950 (fullRecordGapValue06950 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06950_not_prime : ¬(recordGapCenter + 390092).Prime := by
  rw [fullRecordGapTerm06950_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06950, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06950_fast_pow_mod_ne_one

def fullRecordGapValue06951 : Nat := fullRecordGapCenterValue + 390098

theorem fullRecordGapTerm06951_eq_value :
    recordGapCenter + 390098 = fullRecordGapValue06951 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06951_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06951 (fullRecordGapValue06951 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06951_not_prime : ¬(recordGapCenter + 390098).Prime := by
  rw [fullRecordGapTerm06951_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06951, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06951_fast_pow_mod_ne_one

def fullRecordGapValue06952 : Nat := fullRecordGapCenterValue + 390162

theorem fullRecordGapTerm06952_eq_value :
    recordGapCenter + 390162 = fullRecordGapValue06952 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06952_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06952 (fullRecordGapValue06952 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06952_not_prime : ¬(recordGapCenter + 390162).Prime := by
  rw [fullRecordGapTerm06952_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06952, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06952_fast_pow_mod_ne_one

def fullRecordGapValue06953 : Nat := fullRecordGapCenterValue + 390206

theorem fullRecordGapTerm06953_eq_value :
    recordGapCenter + 390206 = fullRecordGapValue06953 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06953_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06953 (fullRecordGapValue06953 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06953_not_prime : ¬(recordGapCenter + 390206).Prime := by
  rw [fullRecordGapTerm06953_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06953, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06953_fast_pow_mod_ne_one

def fullRecordGapValue06954 : Nat := fullRecordGapCenterValue + 390296

theorem fullRecordGapTerm06954_eq_value :
    recordGapCenter + 390296 = fullRecordGapValue06954 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06954_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06954 (fullRecordGapValue06954 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06954_not_prime : ¬(recordGapCenter + 390296).Prime := by
  rw [fullRecordGapTerm06954_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06954, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06954_fast_pow_mod_ne_one

def fullRecordGapValue06955 : Nat := fullRecordGapCenterValue + 390308

theorem fullRecordGapTerm06955_eq_value :
    recordGapCenter + 390308 = fullRecordGapValue06955 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06955_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06955 (fullRecordGapValue06955 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06955_not_prime : ¬(recordGapCenter + 390308).Prime := by
  rw [fullRecordGapTerm06955_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06955, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06955_fast_pow_mod_ne_one

def fullRecordGapValue06956 : Nat := fullRecordGapCenterValue + 390332

theorem fullRecordGapTerm06956_eq_value :
    recordGapCenter + 390332 = fullRecordGapValue06956 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06956_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06956 (fullRecordGapValue06956 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06956_not_prime : ¬(recordGapCenter + 390332).Prime := by
  rw [fullRecordGapTerm06956_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06956, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06956_fast_pow_mod_ne_one

def fullRecordGapValue06957 : Nat := fullRecordGapCenterValue + 390506

theorem fullRecordGapTerm06957_eq_value :
    recordGapCenter + 390506 = fullRecordGapValue06957 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06957_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06957 (fullRecordGapValue06957 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06957_not_prime : ¬(recordGapCenter + 390506).Prime := by
  rw [fullRecordGapTerm06957_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06957, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06957_fast_pow_mod_ne_one

def fullRecordGapValue06958 : Nat := fullRecordGapCenterValue + 390542

theorem fullRecordGapTerm06958_eq_value :
    recordGapCenter + 390542 = fullRecordGapValue06958 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06958_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06958 (fullRecordGapValue06958 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06958_not_prime : ¬(recordGapCenter + 390542).Prime := by
  rw [fullRecordGapTerm06958_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06958, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06958_fast_pow_mod_ne_one

def fullRecordGapValue06959 : Nat := fullRecordGapCenterValue + 390596

theorem fullRecordGapTerm06959_eq_value :
    recordGapCenter + 390596 = fullRecordGapValue06959 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06959_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06959 (fullRecordGapValue06959 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06959_not_prime : ¬(recordGapCenter + 390596).Prime := by
  rw [fullRecordGapTerm06959_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06959, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06959_fast_pow_mod_ne_one

def fullRecordGapValue06960 : Nat := fullRecordGapCenterValue + 390666

theorem fullRecordGapTerm06960_eq_value :
    recordGapCenter + 390666 = fullRecordGapValue06960 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06960_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06960 (fullRecordGapValue06960 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06960_not_prime : ¬(recordGapCenter + 390666).Prime := by
  rw [fullRecordGapTerm06960_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06960, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06960_fast_pow_mod_ne_one

def fullRecordGapValue06961 : Nat := fullRecordGapCenterValue + 390686

theorem fullRecordGapTerm06961_eq_value :
    recordGapCenter + 390686 = fullRecordGapValue06961 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06961_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06961 (fullRecordGapValue06961 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06961_not_prime : ¬(recordGapCenter + 390686).Prime := by
  rw [fullRecordGapTerm06961_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06961, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06961_fast_pow_mod_ne_one

def fullRecordGapValue06962 : Nat := fullRecordGapCenterValue + 390692

theorem fullRecordGapTerm06962_eq_value :
    recordGapCenter + 390692 = fullRecordGapValue06962 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06962_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06962 (fullRecordGapValue06962 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06962_not_prime : ¬(recordGapCenter + 390692).Prime := by
  rw [fullRecordGapTerm06962_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06962, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06962_fast_pow_mod_ne_one

def fullRecordGapValue06963 : Nat := fullRecordGapCenterValue + 390938

theorem fullRecordGapTerm06963_eq_value :
    recordGapCenter + 390938 = fullRecordGapValue06963 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06963_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06963 (fullRecordGapValue06963 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06963_not_prime : ¬(recordGapCenter + 390938).Prime := by
  rw [fullRecordGapTerm06963_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06963, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06963_fast_pow_mod_ne_one

def fullRecordGapValue06964 : Nat := fullRecordGapCenterValue + 390968

theorem fullRecordGapTerm06964_eq_value :
    recordGapCenter + 390968 = fullRecordGapValue06964 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06964_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06964 (fullRecordGapValue06964 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06964_not_prime : ¬(recordGapCenter + 390968).Prime := by
  rw [fullRecordGapTerm06964_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06964, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06964_fast_pow_mod_ne_one

def fullRecordGapValue06965 : Nat := fullRecordGapCenterValue + 390986

theorem fullRecordGapTerm06965_eq_value :
    recordGapCenter + 390986 = fullRecordGapValue06965 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06965_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06965 (fullRecordGapValue06965 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06965_not_prime : ¬(recordGapCenter + 390986).Prime := by
  rw [fullRecordGapTerm06965_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06965, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06965_fast_pow_mod_ne_one

def fullRecordGapValue06966 : Nat := fullRecordGapCenterValue + 391038

theorem fullRecordGapTerm06966_eq_value :
    recordGapCenter + 391038 = fullRecordGapValue06966 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06966_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06966 (fullRecordGapValue06966 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06966_not_prime : ¬(recordGapCenter + 391038).Prime := by
  rw [fullRecordGapTerm06966_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06966, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06966_fast_pow_mod_ne_one

def fullRecordGapValue06967 : Nat := fullRecordGapCenterValue + 391098

theorem fullRecordGapTerm06967_eq_value :
    recordGapCenter + 391098 = fullRecordGapValue06967 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06967_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06967 (fullRecordGapValue06967 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06967_not_prime : ¬(recordGapCenter + 391098).Prime := by
  rw [fullRecordGapTerm06967_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06967, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06967_fast_pow_mod_ne_one

def fullRecordGapValue06968 : Nat := fullRecordGapCenterValue + 391148

theorem fullRecordGapTerm06968_eq_value :
    recordGapCenter + 391148 = fullRecordGapValue06968 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06968_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06968 (fullRecordGapValue06968 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06968_not_prime : ¬(recordGapCenter + 391148).Prime := by
  rw [fullRecordGapTerm06968_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06968, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06968_fast_pow_mod_ne_one

def fullRecordGapValue06969 : Nat := fullRecordGapCenterValue + 391218

theorem fullRecordGapTerm06969_eq_value :
    recordGapCenter + 391218 = fullRecordGapValue06969 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06969_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06969 (fullRecordGapValue06969 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06969_not_prime : ¬(recordGapCenter + 391218).Prime := by
  rw [fullRecordGapTerm06969_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06969, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06969_fast_pow_mod_ne_one

def fullRecordGapValue06970 : Nat := fullRecordGapCenterValue + 391316

theorem fullRecordGapTerm06970_eq_value :
    recordGapCenter + 391316 = fullRecordGapValue06970 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06970_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06970 (fullRecordGapValue06970 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06970_not_prime : ¬(recordGapCenter + 391316).Prime := by
  rw [fullRecordGapTerm06970_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06970, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06970_fast_pow_mod_ne_one

def fullRecordGapValue06971 : Nat := fullRecordGapCenterValue + 391436

theorem fullRecordGapTerm06971_eq_value :
    recordGapCenter + 391436 = fullRecordGapValue06971 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06971_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06971 (fullRecordGapValue06971 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06971_not_prime : ¬(recordGapCenter + 391436).Prime := by
  rw [fullRecordGapTerm06971_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06971, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06971_fast_pow_mod_ne_one

def fullRecordGapValue06972 : Nat := fullRecordGapCenterValue + 391542

theorem fullRecordGapTerm06972_eq_value :
    recordGapCenter + 391542 = fullRecordGapValue06972 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06972_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06972 (fullRecordGapValue06972 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06972_not_prime : ¬(recordGapCenter + 391542).Prime := by
  rw [fullRecordGapTerm06972_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06972, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06972_fast_pow_mod_ne_one

def fullRecordGapValue06973 : Nat := fullRecordGapCenterValue + 391602

theorem fullRecordGapTerm06973_eq_value :
    recordGapCenter + 391602 = fullRecordGapValue06973 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06973_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06973 (fullRecordGapValue06973 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06973_not_prime : ¬(recordGapCenter + 391602).Prime := by
  rw [fullRecordGapTerm06973_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06973, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06973_fast_pow_mod_ne_one

def fullRecordGapValue06974 : Nat := fullRecordGapCenterValue + 391862

theorem fullRecordGapTerm06974_eq_value :
    recordGapCenter + 391862 = fullRecordGapValue06974 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06974_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06974 (fullRecordGapValue06974 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06974_not_prime : ¬(recordGapCenter + 391862).Prime := by
  rw [fullRecordGapTerm06974_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06974, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06974_fast_pow_mod_ne_one

def fullRecordGapValue06975 : Nat := fullRecordGapCenterValue + 391868

theorem fullRecordGapTerm06975_eq_value :
    recordGapCenter + 391868 = fullRecordGapValue06975 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06975_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06975 (fullRecordGapValue06975 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06975_not_prime : ¬(recordGapCenter + 391868).Prime := by
  rw [fullRecordGapTerm06975_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06975, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06975_fast_pow_mod_ne_one

def fullRecordGapValue06976 : Nat := fullRecordGapCenterValue + 391892

theorem fullRecordGapTerm06976_eq_value :
    recordGapCenter + 391892 = fullRecordGapValue06976 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06976_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06976 (fullRecordGapValue06976 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06976_not_prime : ¬(recordGapCenter + 391892).Prime := by
  rw [fullRecordGapTerm06976_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06976, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06976_fast_pow_mod_ne_one

def fullRecordGapValue06977 : Nat := fullRecordGapCenterValue + 391946

theorem fullRecordGapTerm06977_eq_value :
    recordGapCenter + 391946 = fullRecordGapValue06977 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06977_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06977 (fullRecordGapValue06977 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06977_not_prime : ¬(recordGapCenter + 391946).Prime := by
  rw [fullRecordGapTerm06977_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06977, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06977_fast_pow_mod_ne_one

def fullRecordGapValue06978 : Nat := fullRecordGapCenterValue + 391962

theorem fullRecordGapTerm06978_eq_value :
    recordGapCenter + 391962 = fullRecordGapValue06978 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06978_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06978 (fullRecordGapValue06978 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06978_not_prime : ¬(recordGapCenter + 391962).Prime := by
  rw [fullRecordGapTerm06978_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06978, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06978_fast_pow_mod_ne_one

def fullRecordGapValue06979 : Nat := fullRecordGapCenterValue + 392040

theorem fullRecordGapTerm06979_eq_value :
    recordGapCenter + 392040 = fullRecordGapValue06979 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06979_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06979 (fullRecordGapValue06979 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06979_not_prime : ¬(recordGapCenter + 392040).Prime := by
  rw [fullRecordGapTerm06979_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06979, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06979_fast_pow_mod_ne_one

def fullRecordGapValue06980 : Nat := fullRecordGapCenterValue + 392142

theorem fullRecordGapTerm06980_eq_value :
    recordGapCenter + 392142 = fullRecordGapValue06980 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06980_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06980 (fullRecordGapValue06980 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06980_not_prime : ¬(recordGapCenter + 392142).Prime := by
  rw [fullRecordGapTerm06980_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06980, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06980_fast_pow_mod_ne_one

def fullRecordGapValue06981 : Nat := fullRecordGapCenterValue + 392222

theorem fullRecordGapTerm06981_eq_value :
    recordGapCenter + 392222 = fullRecordGapValue06981 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06981_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06981 (fullRecordGapValue06981 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06981_not_prime : ¬(recordGapCenter + 392222).Prime := by
  rw [fullRecordGapTerm06981_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06981, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06981_fast_pow_mod_ne_one

def fullRecordGapValue06982 : Nat := fullRecordGapCenterValue + 392226

theorem fullRecordGapTerm06982_eq_value :
    recordGapCenter + 392226 = fullRecordGapValue06982 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06982_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06982 (fullRecordGapValue06982 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06982_not_prime : ¬(recordGapCenter + 392226).Prime := by
  rw [fullRecordGapTerm06982_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06982, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06982_fast_pow_mod_ne_one

def fullRecordGapValue06983 : Nat := fullRecordGapCenterValue + 392358

theorem fullRecordGapTerm06983_eq_value :
    recordGapCenter + 392358 = fullRecordGapValue06983 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06983_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06983 (fullRecordGapValue06983 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06983_not_prime : ¬(recordGapCenter + 392358).Prime := by
  rw [fullRecordGapTerm06983_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06983, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06983_fast_pow_mod_ne_one

def fullRecordGapValue06984 : Nat := fullRecordGapCenterValue + 392582

theorem fullRecordGapTerm06984_eq_value :
    recordGapCenter + 392582 = fullRecordGapValue06984 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06984_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06984 (fullRecordGapValue06984 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06984_not_prime : ¬(recordGapCenter + 392582).Prime := by
  rw [fullRecordGapTerm06984_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06984, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06984_fast_pow_mod_ne_one

def fullRecordGapValue06985 : Nat := fullRecordGapCenterValue + 392648

theorem fullRecordGapTerm06985_eq_value :
    recordGapCenter + 392648 = fullRecordGapValue06985 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06985_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06985 (fullRecordGapValue06985 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06985_not_prime : ¬(recordGapCenter + 392648).Prime := by
  rw [fullRecordGapTerm06985_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06985, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06985_fast_pow_mod_ne_one

def fullRecordGapValue06986 : Nat := fullRecordGapCenterValue + 392682

theorem fullRecordGapTerm06986_eq_value :
    recordGapCenter + 392682 = fullRecordGapValue06986 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06986_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06986 (fullRecordGapValue06986 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06986_not_prime : ¬(recordGapCenter + 392682).Prime := by
  rw [fullRecordGapTerm06986_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06986, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06986_fast_pow_mod_ne_one

def fullRecordGapValue06987 : Nat := fullRecordGapCenterValue + 392858

theorem fullRecordGapTerm06987_eq_value :
    recordGapCenter + 392858 = fullRecordGapValue06987 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06987_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06987 (fullRecordGapValue06987 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06987_not_prime : ¬(recordGapCenter + 392858).Prime := by
  rw [fullRecordGapTerm06987_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06987, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06987_fast_pow_mod_ne_one

def fullRecordGapValue06988 : Nat := fullRecordGapCenterValue + 392936

theorem fullRecordGapTerm06988_eq_value :
    recordGapCenter + 392936 = fullRecordGapValue06988 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06988_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06988 (fullRecordGapValue06988 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06988_not_prime : ¬(recordGapCenter + 392936).Prime := by
  rw [fullRecordGapTerm06988_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06988, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06988_fast_pow_mod_ne_one

def fullRecordGapValue06989 : Nat := fullRecordGapCenterValue + 393086

theorem fullRecordGapTerm06989_eq_value :
    recordGapCenter + 393086 = fullRecordGapValue06989 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06989_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06989 (fullRecordGapValue06989 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06989_not_prime : ¬(recordGapCenter + 393086).Prime := by
  rw [fullRecordGapTerm06989_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06989, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06989_fast_pow_mod_ne_one

def fullRecordGapValue06990 : Nat := fullRecordGapCenterValue + 393188

theorem fullRecordGapTerm06990_eq_value :
    recordGapCenter + 393188 = fullRecordGapValue06990 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06990_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06990 (fullRecordGapValue06990 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06990_not_prime : ¬(recordGapCenter + 393188).Prime := by
  rw [fullRecordGapTerm06990_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06990, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06990_fast_pow_mod_ne_one

def fullRecordGapValue06991 : Nat := fullRecordGapCenterValue + 393258

theorem fullRecordGapTerm06991_eq_value :
    recordGapCenter + 393258 = fullRecordGapValue06991 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06991_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06991 (fullRecordGapValue06991 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06991_not_prime : ¬(recordGapCenter + 393258).Prime := by
  rw [fullRecordGapTerm06991_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06991, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06991_fast_pow_mod_ne_one

def fullRecordGapValue06992 : Nat := fullRecordGapCenterValue + 393306

theorem fullRecordGapTerm06992_eq_value :
    recordGapCenter + 393306 = fullRecordGapValue06992 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06992_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06992 (fullRecordGapValue06992 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06992_not_prime : ¬(recordGapCenter + 393306).Prime := by
  rw [fullRecordGapTerm06992_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06992, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06992_fast_pow_mod_ne_one

def fullRecordGapValue06993 : Nat := fullRecordGapCenterValue + 393416

theorem fullRecordGapTerm06993_eq_value :
    recordGapCenter + 393416 = fullRecordGapValue06993 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06993_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06993 (fullRecordGapValue06993 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06993_not_prime : ¬(recordGapCenter + 393416).Prime := by
  rw [fullRecordGapTerm06993_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06993, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06993_fast_pow_mod_ne_one

def fullRecordGapValue06994 : Nat := fullRecordGapCenterValue + 393522

theorem fullRecordGapTerm06994_eq_value :
    recordGapCenter + 393522 = fullRecordGapValue06994 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06994_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06994 (fullRecordGapValue06994 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06994_not_prime : ¬(recordGapCenter + 393522).Prime := by
  rw [fullRecordGapTerm06994_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06994, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06994_fast_pow_mod_ne_one

def fullRecordGapValue06995 : Nat := fullRecordGapCenterValue + 393702

theorem fullRecordGapTerm06995_eq_value :
    recordGapCenter + 393702 = fullRecordGapValue06995 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06995_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06995 (fullRecordGapValue06995 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06995_not_prime : ¬(recordGapCenter + 393702).Prime := by
  rw [fullRecordGapTerm06995_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06995, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06995_fast_pow_mod_ne_one

def fullRecordGapValue06996 : Nat := fullRecordGapCenterValue + 393716

theorem fullRecordGapTerm06996_eq_value :
    recordGapCenter + 393716 = fullRecordGapValue06996 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06996_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06996 (fullRecordGapValue06996 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06996_not_prime : ¬(recordGapCenter + 393716).Prime := by
  rw [fullRecordGapTerm06996_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06996, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06996_fast_pow_mod_ne_one

def fullRecordGapValue06997 : Nat := fullRecordGapCenterValue + 393746

theorem fullRecordGapTerm06997_eq_value :
    recordGapCenter + 393746 = fullRecordGapValue06997 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06997_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06997 (fullRecordGapValue06997 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06997_not_prime : ¬(recordGapCenter + 393746).Prime := by
  rw [fullRecordGapTerm06997_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06997, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06997_fast_pow_mod_ne_one

def fullRecordGapValue06998 : Nat := fullRecordGapCenterValue + 394062

theorem fullRecordGapTerm06998_eq_value :
    recordGapCenter + 394062 = fullRecordGapValue06998 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06998_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06998 (fullRecordGapValue06998 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06998_not_prime : ¬(recordGapCenter + 394062).Prime := by
  rw [fullRecordGapTerm06998_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06998, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06998_fast_pow_mod_ne_one

def fullRecordGapValue06999 : Nat := fullRecordGapCenterValue + 394076

theorem fullRecordGapTerm06999_eq_value :
    recordGapCenter + 394076 = fullRecordGapValue06999 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06999_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06999 (fullRecordGapValue06999 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06999_not_prime : ¬(recordGapCenter + 394076).Prime := by
  rw [fullRecordGapTerm06999_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06999, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06999_fast_pow_mod_ne_one

def fullRecordGapValue07000 : Nat := fullRecordGapCenterValue + 394088

theorem fullRecordGapTerm07000_eq_value :
    recordGapCenter + 394088 = fullRecordGapValue07000 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07000_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07000 (fullRecordGapValue07000 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07000_not_prime : ¬(recordGapCenter + 394088).Prime := by
  rw [fullRecordGapTerm07000_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07000, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07000_fast_pow_mod_ne_one

def fullRecordGapValue07001 : Nat := fullRecordGapCenterValue + 394172

theorem fullRecordGapTerm07001_eq_value :
    recordGapCenter + 394172 = fullRecordGapValue07001 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07001_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07001 (fullRecordGapValue07001 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07001_not_prime : ¬(recordGapCenter + 394172).Prime := by
  rw [fullRecordGapTerm07001_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07001, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07001_fast_pow_mod_ne_one

def fullRecordGapValue07002 : Nat := fullRecordGapCenterValue + 394178

theorem fullRecordGapTerm07002_eq_value :
    recordGapCenter + 394178 = fullRecordGapValue07002 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07002_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07002 (fullRecordGapValue07002 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07002_not_prime : ¬(recordGapCenter + 394178).Prime := by
  rw [fullRecordGapTerm07002_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07002, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07002_fast_pow_mod_ne_one

def fullRecordGapValue07003 : Nat := fullRecordGapCenterValue + 394206

theorem fullRecordGapTerm07003_eq_value :
    recordGapCenter + 394206 = fullRecordGapValue07003 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07003_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07003 (fullRecordGapValue07003 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07003_not_prime : ¬(recordGapCenter + 394206).Prime := by
  rw [fullRecordGapTerm07003_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07003, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07003_fast_pow_mod_ne_one

def fullRecordGapValue07004 : Nat := fullRecordGapCenterValue + 394242

theorem fullRecordGapTerm07004_eq_value :
    recordGapCenter + 394242 = fullRecordGapValue07004 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07004_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07004 (fullRecordGapValue07004 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07004_not_prime : ¬(recordGapCenter + 394242).Prime := by
  rw [fullRecordGapTerm07004_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07004, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07004_fast_pow_mod_ne_one

def fullRecordGapValue07005 : Nat := fullRecordGapCenterValue + 394278

theorem fullRecordGapTerm07005_eq_value :
    recordGapCenter + 394278 = fullRecordGapValue07005 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07005_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07005 (fullRecordGapValue07005 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07005_not_prime : ¬(recordGapCenter + 394278).Prime := by
  rw [fullRecordGapTerm07005_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07005, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07005_fast_pow_mod_ne_one

def fullRecordGapValue07006 : Nat := fullRecordGapCenterValue + 394292

theorem fullRecordGapTerm07006_eq_value :
    recordGapCenter + 394292 = fullRecordGapValue07006 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07006_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07006 (fullRecordGapValue07006 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07006_not_prime : ¬(recordGapCenter + 394292).Prime := by
  rw [fullRecordGapTerm07006_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07006, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07006_fast_pow_mod_ne_one

def fullRecordGapValue07007 : Nat := fullRecordGapCenterValue + 394322

theorem fullRecordGapTerm07007_eq_value :
    recordGapCenter + 394322 = fullRecordGapValue07007 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07007_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07007 (fullRecordGapValue07007 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07007_not_prime : ¬(recordGapCenter + 394322).Prime := by
  rw [fullRecordGapTerm07007_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07007, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07007_fast_pow_mod_ne_one

def fullRecordGapValue07008 : Nat := fullRecordGapCenterValue + 394556

theorem fullRecordGapTerm07008_eq_value :
    recordGapCenter + 394556 = fullRecordGapValue07008 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07008_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07008 (fullRecordGapValue07008 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07008_not_prime : ¬(recordGapCenter + 394556).Prime := by
  rw [fullRecordGapTerm07008_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07008, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07008_fast_pow_mod_ne_one

def fullRecordGapValue07009 : Nat := fullRecordGapCenterValue + 394586

theorem fullRecordGapTerm07009_eq_value :
    recordGapCenter + 394586 = fullRecordGapValue07009 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07009_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07009 (fullRecordGapValue07009 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07009_not_prime : ¬(recordGapCenter + 394586).Prime := by
  rw [fullRecordGapTerm07009_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07009, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07009_fast_pow_mod_ne_one

def fullRecordGapValue07010 : Nat := fullRecordGapCenterValue + 394622

theorem fullRecordGapTerm07010_eq_value :
    recordGapCenter + 394622 = fullRecordGapValue07010 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07010_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07010 (fullRecordGapValue07010 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07010_not_prime : ¬(recordGapCenter + 394622).Prime := by
  rw [fullRecordGapTerm07010_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07010, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07010_fast_pow_mod_ne_one

def fullRecordGapValue07011 : Nat := fullRecordGapCenterValue + 394662

theorem fullRecordGapTerm07011_eq_value :
    recordGapCenter + 394662 = fullRecordGapValue07011 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07011_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07011 (fullRecordGapValue07011 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07011_not_prime : ¬(recordGapCenter + 394662).Prime := by
  rw [fullRecordGapTerm07011_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07011, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07011_fast_pow_mod_ne_one

def fullRecordGapValue07012 : Nat := fullRecordGapCenterValue + 394682

theorem fullRecordGapTerm07012_eq_value :
    recordGapCenter + 394682 = fullRecordGapValue07012 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07012_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07012 (fullRecordGapValue07012 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07012_not_prime : ¬(recordGapCenter + 394682).Prime := by
  rw [fullRecordGapTerm07012_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07012, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07012_fast_pow_mod_ne_one

def fullRecordGapValue07013 : Nat := fullRecordGapCenterValue + 394712

theorem fullRecordGapTerm07013_eq_value :
    recordGapCenter + 394712 = fullRecordGapValue07013 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07013_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07013 (fullRecordGapValue07013 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07013_not_prime : ¬(recordGapCenter + 394712).Prime := by
  rw [fullRecordGapTerm07013_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07013, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07013_fast_pow_mod_ne_one

def fullRecordGapValue07014 : Nat := fullRecordGapCenterValue + 394718

theorem fullRecordGapTerm07014_eq_value :
    recordGapCenter + 394718 = fullRecordGapValue07014 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07014_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07014 (fullRecordGapValue07014 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07014_not_prime : ¬(recordGapCenter + 394718).Prime := by
  rw [fullRecordGapTerm07014_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07014, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07014_fast_pow_mod_ne_one

def fullRecordGapValue07015 : Nat := fullRecordGapCenterValue + 394766

theorem fullRecordGapTerm07015_eq_value :
    recordGapCenter + 394766 = fullRecordGapValue07015 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07015_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07015 (fullRecordGapValue07015 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07015_not_prime : ¬(recordGapCenter + 394766).Prime := by
  rw [fullRecordGapTerm07015_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07015, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07015_fast_pow_mod_ne_one

def fullRecordGapValue07016 : Nat := fullRecordGapCenterValue + 394868

theorem fullRecordGapTerm07016_eq_value :
    recordGapCenter + 394868 = fullRecordGapValue07016 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07016_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07016 (fullRecordGapValue07016 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07016_not_prime : ¬(recordGapCenter + 394868).Prime := by
  rw [fullRecordGapTerm07016_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07016, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07016_fast_pow_mod_ne_one

def fullRecordGapValue07017 : Nat := fullRecordGapCenterValue + 394916

theorem fullRecordGapTerm07017_eq_value :
    recordGapCenter + 394916 = fullRecordGapValue07017 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07017_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07017 (fullRecordGapValue07017 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07017_not_prime : ¬(recordGapCenter + 394916).Prime := by
  rw [fullRecordGapTerm07017_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07017, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07017_fast_pow_mod_ne_one

def fullRecordGapValue07018 : Nat := fullRecordGapCenterValue + 394952

theorem fullRecordGapTerm07018_eq_value :
    recordGapCenter + 394952 = fullRecordGapValue07018 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07018_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07018 (fullRecordGapValue07018 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07018_not_prime : ¬(recordGapCenter + 394952).Prime := by
  rw [fullRecordGapTerm07018_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07018, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07018_fast_pow_mod_ne_one

def fullRecordGapValue07019 : Nat := fullRecordGapCenterValue + 394986

theorem fullRecordGapTerm07019_eq_value :
    recordGapCenter + 394986 = fullRecordGapValue07019 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07019_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07019 (fullRecordGapValue07019 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07019_not_prime : ¬(recordGapCenter + 394986).Prime := by
  rw [fullRecordGapTerm07019_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07019, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07019_fast_pow_mod_ne_one

def fullRecordGapValue07020 : Nat := fullRecordGapCenterValue + 395022

theorem fullRecordGapTerm07020_eq_value :
    recordGapCenter + 395022 = fullRecordGapValue07020 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07020_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07020 (fullRecordGapValue07020 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07020_not_prime : ¬(recordGapCenter + 395022).Prime := by
  rw [fullRecordGapTerm07020_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07020, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07020_fast_pow_mod_ne_one

def fullRecordGapValue07021 : Nat := fullRecordGapCenterValue + 395078

theorem fullRecordGapTerm07021_eq_value :
    recordGapCenter + 395078 = fullRecordGapValue07021 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07021_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07021 (fullRecordGapValue07021 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07021_not_prime : ¬(recordGapCenter + 395078).Prime := by
  rw [fullRecordGapTerm07021_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07021, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07021_fast_pow_mod_ne_one

def fullRecordGapValue07022 : Nat := fullRecordGapCenterValue + 395106

theorem fullRecordGapTerm07022_eq_value :
    recordGapCenter + 395106 = fullRecordGapValue07022 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07022_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07022 (fullRecordGapValue07022 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07022_not_prime : ¬(recordGapCenter + 395106).Prime := by
  rw [fullRecordGapTerm07022_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07022, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07022_fast_pow_mod_ne_one

def fullRecordGapValue07023 : Nat := fullRecordGapCenterValue + 395202

theorem fullRecordGapTerm07023_eq_value :
    recordGapCenter + 395202 = fullRecordGapValue07023 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07023_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07023 (fullRecordGapValue07023 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07023_not_prime : ¬(recordGapCenter + 395202).Prime := by
  rw [fullRecordGapTerm07023_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07023, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07023_fast_pow_mod_ne_one

def fullRecordGapValue07024 : Nat := fullRecordGapCenterValue + 395286

theorem fullRecordGapTerm07024_eq_value :
    recordGapCenter + 395286 = fullRecordGapValue07024 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07024_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07024 (fullRecordGapValue07024 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07024_not_prime : ¬(recordGapCenter + 395286).Prime := by
  rw [fullRecordGapTerm07024_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07024, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07024_fast_pow_mod_ne_one

def fullRecordGapValue07025 : Nat := fullRecordGapCenterValue + 395288

theorem fullRecordGapTerm07025_eq_value :
    recordGapCenter + 395288 = fullRecordGapValue07025 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07025_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07025 (fullRecordGapValue07025 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07025_not_prime : ¬(recordGapCenter + 395288).Prime := by
  rw [fullRecordGapTerm07025_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07025, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07025_fast_pow_mod_ne_one

def fullRecordGapValue07026 : Nat := fullRecordGapCenterValue + 395378

theorem fullRecordGapTerm07026_eq_value :
    recordGapCenter + 395378 = fullRecordGapValue07026 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07026_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07026 (fullRecordGapValue07026 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07026_not_prime : ¬(recordGapCenter + 395378).Prime := by
  rw [fullRecordGapTerm07026_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07026, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07026_fast_pow_mod_ne_one

def fullRecordGapValue07027 : Nat := fullRecordGapCenterValue + 395526

theorem fullRecordGapTerm07027_eq_value :
    recordGapCenter + 395526 = fullRecordGapValue07027 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07027_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07027 (fullRecordGapValue07027 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07027_not_prime : ¬(recordGapCenter + 395526).Prime := by
  rw [fullRecordGapTerm07027_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07027, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07027_fast_pow_mod_ne_one

def fullRecordGapValue07028 : Nat := fullRecordGapCenterValue + 395636

theorem fullRecordGapTerm07028_eq_value :
    recordGapCenter + 395636 = fullRecordGapValue07028 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07028_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07028 (fullRecordGapValue07028 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07028_not_prime : ¬(recordGapCenter + 395636).Prime := by
  rw [fullRecordGapTerm07028_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07028, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07028_fast_pow_mod_ne_one

def fullRecordGapValue07029 : Nat := fullRecordGapCenterValue + 395816

theorem fullRecordGapTerm07029_eq_value :
    recordGapCenter + 395816 = fullRecordGapValue07029 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07029_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07029 (fullRecordGapValue07029 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07029_not_prime : ¬(recordGapCenter + 395816).Prime := by
  rw [fullRecordGapTerm07029_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07029, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07029_fast_pow_mod_ne_one

def fullRecordGapValue07030 : Nat := fullRecordGapCenterValue + 395852

theorem fullRecordGapTerm07030_eq_value :
    recordGapCenter + 395852 = fullRecordGapValue07030 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07030_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07030 (fullRecordGapValue07030 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07030_not_prime : ¬(recordGapCenter + 395852).Prime := by
  rw [fullRecordGapTerm07030_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07030, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07030_fast_pow_mod_ne_one

def fullRecordGapValue07031 : Nat := fullRecordGapCenterValue + 395942

theorem fullRecordGapTerm07031_eq_value :
    recordGapCenter + 395942 = fullRecordGapValue07031 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07031_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07031 (fullRecordGapValue07031 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07031_not_prime : ¬(recordGapCenter + 395942).Prime := by
  rw [fullRecordGapTerm07031_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07031, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07031_fast_pow_mod_ne_one

def fullRecordGapValue07032 : Nat := fullRecordGapCenterValue + 395958

theorem fullRecordGapTerm07032_eq_value :
    recordGapCenter + 395958 = fullRecordGapValue07032 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07032_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07032 (fullRecordGapValue07032 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07032_not_prime : ¬(recordGapCenter + 395958).Prime := by
  rw [fullRecordGapTerm07032_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07032, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07032_fast_pow_mod_ne_one

def fullRecordGapValue07033 : Nat := fullRecordGapCenterValue + 396000

theorem fullRecordGapTerm07033_eq_value :
    recordGapCenter + 396000 = fullRecordGapValue07033 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07033_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07033 (fullRecordGapValue07033 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07033_not_prime : ¬(recordGapCenter + 396000).Prime := by
  rw [fullRecordGapTerm07033_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07033, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07033_fast_pow_mod_ne_one

def fullRecordGapValue07034 : Nat := fullRecordGapCenterValue + 396026

theorem fullRecordGapTerm07034_eq_value :
    recordGapCenter + 396026 = fullRecordGapValue07034 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07034_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07034 (fullRecordGapValue07034 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07034_not_prime : ¬(recordGapCenter + 396026).Prime := by
  rw [fullRecordGapTerm07034_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07034, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07034_fast_pow_mod_ne_one

def fullRecordGapValue07035 : Nat := fullRecordGapCenterValue + 396068

theorem fullRecordGapTerm07035_eq_value :
    recordGapCenter + 396068 = fullRecordGapValue07035 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07035_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07035 (fullRecordGapValue07035 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07035_not_prime : ¬(recordGapCenter + 396068).Prime := by
  rw [fullRecordGapTerm07035_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07035, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07035_fast_pow_mod_ne_one

def fullRecordGapValue07036 : Nat := fullRecordGapCenterValue + 396086

theorem fullRecordGapTerm07036_eq_value :
    recordGapCenter + 396086 = fullRecordGapValue07036 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07036_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07036 (fullRecordGapValue07036 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07036_not_prime : ¬(recordGapCenter + 396086).Prime := by
  rw [fullRecordGapTerm07036_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07036, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07036_fast_pow_mod_ne_one

def fullRecordGapValue07037 : Nat := fullRecordGapCenterValue + 396212

theorem fullRecordGapTerm07037_eq_value :
    recordGapCenter + 396212 = fullRecordGapValue07037 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07037_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07037 (fullRecordGapValue07037 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07037_not_prime : ¬(recordGapCenter + 396212).Prime := by
  rw [fullRecordGapTerm07037_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07037, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07037_fast_pow_mod_ne_one

def fullRecordGapValue07038 : Nat := fullRecordGapCenterValue + 396218

theorem fullRecordGapTerm07038_eq_value :
    recordGapCenter + 396218 = fullRecordGapValue07038 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07038_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07038 (fullRecordGapValue07038 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07038_not_prime : ¬(recordGapCenter + 396218).Prime := by
  rw [fullRecordGapTerm07038_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07038, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07038_fast_pow_mod_ne_one

def fullRecordGapValue07039 : Nat := fullRecordGapCenterValue + 396246

theorem fullRecordGapTerm07039_eq_value :
    recordGapCenter + 396246 = fullRecordGapValue07039 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07039_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07039 (fullRecordGapValue07039 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07039_not_prime : ¬(recordGapCenter + 396246).Prime := by
  rw [fullRecordGapTerm07039_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07039, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07039_fast_pow_mod_ne_one

def fullRecordGapValue07040 : Nat := fullRecordGapCenterValue + 396278

theorem fullRecordGapTerm07040_eq_value :
    recordGapCenter + 396278 = fullRecordGapValue07040 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07040_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07040 (fullRecordGapValue07040 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07040_not_prime : ¬(recordGapCenter + 396278).Prime := by
  rw [fullRecordGapTerm07040_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07040, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07040_fast_pow_mod_ne_one

def fullRecordGapValue07041 : Nat := fullRecordGapCenterValue + 396386

theorem fullRecordGapTerm07041_eq_value :
    recordGapCenter + 396386 = fullRecordGapValue07041 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07041_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07041 (fullRecordGapValue07041 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07041_not_prime : ¬(recordGapCenter + 396386).Prime := by
  rw [fullRecordGapTerm07041_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07041, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07041_fast_pow_mod_ne_one

def fullRecordGapValue07042 : Nat := fullRecordGapCenterValue + 396426

theorem fullRecordGapTerm07042_eq_value :
    recordGapCenter + 396426 = fullRecordGapValue07042 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07042_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07042 (fullRecordGapValue07042 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07042_not_prime : ¬(recordGapCenter + 396426).Prime := by
  rw [fullRecordGapTerm07042_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07042, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07042_fast_pow_mod_ne_one

def fullRecordGapValue07043 : Nat := fullRecordGapCenterValue + 396498

theorem fullRecordGapTerm07043_eq_value :
    recordGapCenter + 396498 = fullRecordGapValue07043 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07043_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07043 (fullRecordGapValue07043 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07043_not_prime : ¬(recordGapCenter + 396498).Prime := by
  rw [fullRecordGapTerm07043_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07043, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07043_fast_pow_mod_ne_one

def fullRecordGapValue07044 : Nat := fullRecordGapCenterValue + 396692

theorem fullRecordGapTerm07044_eq_value :
    recordGapCenter + 396692 = fullRecordGapValue07044 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07044_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07044 (fullRecordGapValue07044 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07044_not_prime : ¬(recordGapCenter + 396692).Prime := by
  rw [fullRecordGapTerm07044_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07044, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07044_fast_pow_mod_ne_one

def fullRecordGapValue07045 : Nat := fullRecordGapCenterValue + 396782

theorem fullRecordGapTerm07045_eq_value :
    recordGapCenter + 396782 = fullRecordGapValue07045 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07045_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07045 (fullRecordGapValue07045 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07045_not_prime : ¬(recordGapCenter + 396782).Prime := by
  rw [fullRecordGapTerm07045_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07045, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07045_fast_pow_mod_ne_one

def fullRecordGapValue07046 : Nat := fullRecordGapCenterValue + 397058

theorem fullRecordGapTerm07046_eq_value :
    recordGapCenter + 397058 = fullRecordGapValue07046 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07046_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07046 (fullRecordGapValue07046 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07046_not_prime : ¬(recordGapCenter + 397058).Prime := by
  rw [fullRecordGapTerm07046_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07046, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07046_fast_pow_mod_ne_one

def fullRecordGapValue07047 : Nat := fullRecordGapCenterValue + 397226

theorem fullRecordGapTerm07047_eq_value :
    recordGapCenter + 397226 = fullRecordGapValue07047 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07047_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07047 (fullRecordGapValue07047 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07047_not_prime : ¬(recordGapCenter + 397226).Prime := by
  rw [fullRecordGapTerm07047_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07047, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07047_fast_pow_mod_ne_one

def fullRecordGapValue07048 : Nat := fullRecordGapCenterValue + 397346

theorem fullRecordGapTerm07048_eq_value :
    recordGapCenter + 397346 = fullRecordGapValue07048 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07048_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07048 (fullRecordGapValue07048 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07048_not_prime : ¬(recordGapCenter + 397346).Prime := by
  rw [fullRecordGapTerm07048_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07048, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07048_fast_pow_mod_ne_one

def fullRecordGapValue07049 : Nat := fullRecordGapCenterValue + 397388

theorem fullRecordGapTerm07049_eq_value :
    recordGapCenter + 397388 = fullRecordGapValue07049 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07049_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07049 (fullRecordGapValue07049 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07049_not_prime : ¬(recordGapCenter + 397388).Prime := by
  rw [fullRecordGapTerm07049_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07049, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07049_fast_pow_mod_ne_one

def fullRecordGapValue07050 : Nat := fullRecordGapCenterValue + 397622

theorem fullRecordGapTerm07050_eq_value :
    recordGapCenter + 397622 = fullRecordGapValue07050 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07050_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07050 (fullRecordGapValue07050 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07050_not_prime : ¬(recordGapCenter + 397622).Prime := by
  rw [fullRecordGapTerm07050_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07050, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07050_fast_pow_mod_ne_one

def fullRecordGapValue07051 : Nat := fullRecordGapCenterValue + 397682

theorem fullRecordGapTerm07051_eq_value :
    recordGapCenter + 397682 = fullRecordGapValue07051 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07051_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07051 (fullRecordGapValue07051 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07051_not_prime : ¬(recordGapCenter + 397682).Prime := by
  rw [fullRecordGapTerm07051_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07051, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07051_fast_pow_mod_ne_one

def fullRecordGapValue07052 : Nat := fullRecordGapCenterValue + 397688

theorem fullRecordGapTerm07052_eq_value :
    recordGapCenter + 397688 = fullRecordGapValue07052 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07052_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07052 (fullRecordGapValue07052 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07052_not_prime : ¬(recordGapCenter + 397688).Prime := by
  rw [fullRecordGapTerm07052_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07052, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07052_fast_pow_mod_ne_one

def fullRecordGapValue07053 : Nat := fullRecordGapCenterValue + 397806

theorem fullRecordGapTerm07053_eq_value :
    recordGapCenter + 397806 = fullRecordGapValue07053 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07053_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07053 (fullRecordGapValue07053 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07053_not_prime : ¬(recordGapCenter + 397806).Prime := by
  rw [fullRecordGapTerm07053_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07053, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07053_fast_pow_mod_ne_one

def fullRecordGapValue07054 : Nat := fullRecordGapCenterValue + 398078

theorem fullRecordGapTerm07054_eq_value :
    recordGapCenter + 398078 = fullRecordGapValue07054 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07054_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07054 (fullRecordGapValue07054 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07054_not_prime : ¬(recordGapCenter + 398078).Prime := by
  rw [fullRecordGapTerm07054_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07054, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07054_fast_pow_mod_ne_one

def fullRecordGapValue07055 : Nat := fullRecordGapCenterValue + 398162

theorem fullRecordGapTerm07055_eq_value :
    recordGapCenter + 398162 = fullRecordGapValue07055 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07055_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07055 (fullRecordGapValue07055 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07055_not_prime : ¬(recordGapCenter + 398162).Prime := by
  rw [fullRecordGapTerm07055_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07055, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07055_fast_pow_mod_ne_one

def fullRecordGapValue07056 : Nat := fullRecordGapCenterValue + 398252

theorem fullRecordGapTerm07056_eq_value :
    recordGapCenter + 398252 = fullRecordGapValue07056 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07056_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07056 (fullRecordGapValue07056 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07056_not_prime : ¬(recordGapCenter + 398252).Prime := by
  rw [fullRecordGapTerm07056_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07056, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07056_fast_pow_mod_ne_one

def fullRecordGapValue07057 : Nat := fullRecordGapCenterValue + 398408

theorem fullRecordGapTerm07057_eq_value :
    recordGapCenter + 398408 = fullRecordGapValue07057 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07057_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07057 (fullRecordGapValue07057 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07057_not_prime : ¬(recordGapCenter + 398408).Prime := by
  rw [fullRecordGapTerm07057_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07057, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07057_fast_pow_mod_ne_one

def fullRecordGapValue07058 : Nat := fullRecordGapCenterValue + 398756

theorem fullRecordGapTerm07058_eq_value :
    recordGapCenter + 398756 = fullRecordGapValue07058 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07058_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07058 (fullRecordGapValue07058 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07058_not_prime : ¬(recordGapCenter + 398756).Prime := by
  rw [fullRecordGapTerm07058_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07058, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07058_fast_pow_mod_ne_one

def fullRecordGapValue07059 : Nat := fullRecordGapCenterValue + 398778

theorem fullRecordGapTerm07059_eq_value :
    recordGapCenter + 398778 = fullRecordGapValue07059 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07059_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07059 (fullRecordGapValue07059 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07059_not_prime : ¬(recordGapCenter + 398778).Prime := by
  rw [fullRecordGapTerm07059_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07059, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07059_fast_pow_mod_ne_one

def fullRecordGapValue07060 : Nat := fullRecordGapCenterValue + 398798

theorem fullRecordGapTerm07060_eq_value :
    recordGapCenter + 398798 = fullRecordGapValue07060 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07060_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07060 (fullRecordGapValue07060 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07060_not_prime : ¬(recordGapCenter + 398798).Prime := by
  rw [fullRecordGapTerm07060_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07060, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07060_fast_pow_mod_ne_one

def fullRecordGapValue07061 : Nat := fullRecordGapCenterValue + 398802

theorem fullRecordGapTerm07061_eq_value :
    recordGapCenter + 398802 = fullRecordGapValue07061 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07061_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07061 (fullRecordGapValue07061 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07061_not_prime : ¬(recordGapCenter + 398802).Prime := by
  rw [fullRecordGapTerm07061_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07061, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07061_fast_pow_mod_ne_one

def fullRecordGapValue07062 : Nat := fullRecordGapCenterValue + 398822

theorem fullRecordGapTerm07062_eq_value :
    recordGapCenter + 398822 = fullRecordGapValue07062 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07062_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07062 (fullRecordGapValue07062 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07062_not_prime : ¬(recordGapCenter + 398822).Prime := by
  rw [fullRecordGapTerm07062_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07062, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07062_fast_pow_mod_ne_one

def fullRecordGapValue07063 : Nat := fullRecordGapCenterValue + 398828

theorem fullRecordGapTerm07063_eq_value :
    recordGapCenter + 398828 = fullRecordGapValue07063 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07063_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07063 (fullRecordGapValue07063 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07063_not_prime : ¬(recordGapCenter + 398828).Prime := by
  rw [fullRecordGapTerm07063_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07063, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07063_fast_pow_mod_ne_one

def fullRecordGapValue07064 : Nat := fullRecordGapCenterValue + 398858

theorem fullRecordGapTerm07064_eq_value :
    recordGapCenter + 398858 = fullRecordGapValue07064 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07064_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07064 (fullRecordGapValue07064 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07064_not_prime : ¬(recordGapCenter + 398858).Prime := by
  rw [fullRecordGapTerm07064_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07064, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07064_fast_pow_mod_ne_one

def fullRecordGapValue07065 : Nat := fullRecordGapCenterValue + 398946

theorem fullRecordGapTerm07065_eq_value :
    recordGapCenter + 398946 = fullRecordGapValue07065 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07065_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07065 (fullRecordGapValue07065 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07065_not_prime : ¬(recordGapCenter + 398946).Prime := by
  rw [fullRecordGapTerm07065_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07065, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07065_fast_pow_mod_ne_one

def fullRecordGapValue07066 : Nat := fullRecordGapCenterValue + 399002

theorem fullRecordGapTerm07066_eq_value :
    recordGapCenter + 399002 = fullRecordGapValue07066 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07066_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07066 (fullRecordGapValue07066 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07066_not_prime : ¬(recordGapCenter + 399002).Prime := by
  rw [fullRecordGapTerm07066_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07066, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07066_fast_pow_mod_ne_one

def fullRecordGapValue07067 : Nat := fullRecordGapCenterValue + 399236

theorem fullRecordGapTerm07067_eq_value :
    recordGapCenter + 399236 = fullRecordGapValue07067 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07067_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07067 (fullRecordGapValue07067 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07067_not_prime : ¬(recordGapCenter + 399236).Prime := by
  rw [fullRecordGapTerm07067_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07067, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07067_fast_pow_mod_ne_one

def fullRecordGapValue07068 : Nat := fullRecordGapCenterValue + 399242

theorem fullRecordGapTerm07068_eq_value :
    recordGapCenter + 399242 = fullRecordGapValue07068 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07068_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07068 (fullRecordGapValue07068 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07068_not_prime : ¬(recordGapCenter + 399242).Prime := by
  rw [fullRecordGapTerm07068_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07068, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07068_fast_pow_mod_ne_one

def fullRecordGapValue07069 : Nat := fullRecordGapCenterValue + 399246

theorem fullRecordGapTerm07069_eq_value :
    recordGapCenter + 399246 = fullRecordGapValue07069 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07069_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07069 (fullRecordGapValue07069 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07069_not_prime : ¬(recordGapCenter + 399246).Prime := by
  rw [fullRecordGapTerm07069_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07069, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07069_fast_pow_mod_ne_one

def fullRecordGapValue07070 : Nat := fullRecordGapCenterValue + 399332

theorem fullRecordGapTerm07070_eq_value :
    recordGapCenter + 399332 = fullRecordGapValue07070 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07070_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07070 (fullRecordGapValue07070 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07070_not_prime : ¬(recordGapCenter + 399332).Prime := by
  rw [fullRecordGapTerm07070_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07070, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07070_fast_pow_mod_ne_one

def fullRecordGapValue07071 : Nat := fullRecordGapCenterValue + 399368

theorem fullRecordGapTerm07071_eq_value :
    recordGapCenter + 399368 = fullRecordGapValue07071 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07071_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07071 (fullRecordGapValue07071 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07071_not_prime : ¬(recordGapCenter + 399368).Prime := by
  rw [fullRecordGapTerm07071_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07071, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07071_fast_pow_mod_ne_one

def fullRecordGapValue07072 : Nat := fullRecordGapCenterValue + 399458

theorem fullRecordGapTerm07072_eq_value :
    recordGapCenter + 399458 = fullRecordGapValue07072 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07072_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07072 (fullRecordGapValue07072 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07072_not_prime : ¬(recordGapCenter + 399458).Prime := by
  rw [fullRecordGapTerm07072_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07072, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07072_fast_pow_mod_ne_one

def fullRecordGapValue07073 : Nat := fullRecordGapCenterValue + 399506

theorem fullRecordGapTerm07073_eq_value :
    recordGapCenter + 399506 = fullRecordGapValue07073 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07073_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07073 (fullRecordGapValue07073 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07073_not_prime : ¬(recordGapCenter + 399506).Prime := by
  rw [fullRecordGapTerm07073_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07073, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07073_fast_pow_mod_ne_one

def fullRecordGapValue07074 : Nat := fullRecordGapCenterValue + 399512

theorem fullRecordGapTerm07074_eq_value :
    recordGapCenter + 399512 = fullRecordGapValue07074 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07074_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07074 (fullRecordGapValue07074 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07074_not_prime : ¬(recordGapCenter + 399512).Prime := by
  rw [fullRecordGapTerm07074_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07074, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07074_fast_pow_mod_ne_one

def fullRecordGapValue07075 : Nat := fullRecordGapCenterValue + 399558

theorem fullRecordGapTerm07075_eq_value :
    recordGapCenter + 399558 = fullRecordGapValue07075 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07075_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07075 (fullRecordGapValue07075 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07075_not_prime : ¬(recordGapCenter + 399558).Prime := by
  rw [fullRecordGapTerm07075_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07075, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07075_fast_pow_mod_ne_one

def fullRecordGapValue07076 : Nat := fullRecordGapCenterValue + 399638

theorem fullRecordGapTerm07076_eq_value :
    recordGapCenter + 399638 = fullRecordGapValue07076 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07076_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07076 (fullRecordGapValue07076 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07076_not_prime : ¬(recordGapCenter + 399638).Prime := by
  rw [fullRecordGapTerm07076_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07076, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07076_fast_pow_mod_ne_one

def fullRecordGapValue07077 : Nat := fullRecordGapCenterValue + 399662

theorem fullRecordGapTerm07077_eq_value :
    recordGapCenter + 399662 = fullRecordGapValue07077 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07077_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07077 (fullRecordGapValue07077 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07077_not_prime : ¬(recordGapCenter + 399662).Prime := by
  rw [fullRecordGapTerm07077_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07077, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07077_fast_pow_mod_ne_one

def fullRecordGapValue07078 : Nat := fullRecordGapCenterValue + 399702

theorem fullRecordGapTerm07078_eq_value :
    recordGapCenter + 399702 = fullRecordGapValue07078 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07078_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07078 (fullRecordGapValue07078 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07078_not_prime : ¬(recordGapCenter + 399702).Prime := by
  rw [fullRecordGapTerm07078_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07078, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07078_fast_pow_mod_ne_one

def fullRecordGapValue07079 : Nat := fullRecordGapCenterValue + 399716

theorem fullRecordGapTerm07079_eq_value :
    recordGapCenter + 399716 = fullRecordGapValue07079 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07079_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07079 (fullRecordGapValue07079 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07079_not_prime : ¬(recordGapCenter + 399716).Prime := by
  rw [fullRecordGapTerm07079_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07079, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07079_fast_pow_mod_ne_one

def fullRecordGapValue07080 : Nat := fullRecordGapCenterValue + 399746

theorem fullRecordGapTerm07080_eq_value :
    recordGapCenter + 399746 = fullRecordGapValue07080 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07080_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07080 (fullRecordGapValue07080 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07080_not_prime : ¬(recordGapCenter + 399746).Prime := by
  rw [fullRecordGapTerm07080_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07080, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07080_fast_pow_mod_ne_one

def fullRecordGapValue07081 : Nat := fullRecordGapCenterValue + 399998

theorem fullRecordGapTerm07081_eq_value :
    recordGapCenter + 399998 = fullRecordGapValue07081 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07081_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07081 (fullRecordGapValue07081 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07081_not_prime : ¬(recordGapCenter + 399998).Prime := by
  rw [fullRecordGapTerm07081_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07081, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07081_fast_pow_mod_ne_one

def fullRecordGapValue07082 : Nat := fullRecordGapCenterValue + 400046

theorem fullRecordGapTerm07082_eq_value :
    recordGapCenter + 400046 = fullRecordGapValue07082 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07082_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07082 (fullRecordGapValue07082 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07082_not_prime : ¬(recordGapCenter + 400046).Prime := by
  rw [fullRecordGapTerm07082_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07082, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07082_fast_pow_mod_ne_one

def fullRecordGapValue07083 : Nat := fullRecordGapCenterValue + 400058

theorem fullRecordGapTerm07083_eq_value :
    recordGapCenter + 400058 = fullRecordGapValue07083 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07083_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07083 (fullRecordGapValue07083 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07083_not_prime : ¬(recordGapCenter + 400058).Prime := by
  rw [fullRecordGapTerm07083_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07083, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07083_fast_pow_mod_ne_one

def fullRecordGapValue07084 : Nat := fullRecordGapCenterValue + 400082

theorem fullRecordGapTerm07084_eq_value :
    recordGapCenter + 400082 = fullRecordGapValue07084 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07084_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07084 (fullRecordGapValue07084 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07084_not_prime : ¬(recordGapCenter + 400082).Prime := by
  rw [fullRecordGapTerm07084_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07084, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07084_fast_pow_mod_ne_one

def fullRecordGapValue07085 : Nat := fullRecordGapCenterValue + 400206

theorem fullRecordGapTerm07085_eq_value :
    recordGapCenter + 400206 = fullRecordGapValue07085 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07085_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07085 (fullRecordGapValue07085 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07085_not_prime : ¬(recordGapCenter + 400206).Prime := by
  rw [fullRecordGapTerm07085_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07085, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07085_fast_pow_mod_ne_one

def fullRecordGapValue07086 : Nat := fullRecordGapCenterValue + 400382

theorem fullRecordGapTerm07086_eq_value :
    recordGapCenter + 400382 = fullRecordGapValue07086 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07086_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07086 (fullRecordGapValue07086 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07086_not_prime : ¬(recordGapCenter + 400382).Prime := by
  rw [fullRecordGapTerm07086_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07086, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07086_fast_pow_mod_ne_one

def fullRecordGapValue07087 : Nat := fullRecordGapCenterValue + 400586

theorem fullRecordGapTerm07087_eq_value :
    recordGapCenter + 400586 = fullRecordGapValue07087 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07087_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07087 (fullRecordGapValue07087 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07087_not_prime : ¬(recordGapCenter + 400586).Prime := by
  rw [fullRecordGapTerm07087_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07087, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07087_fast_pow_mod_ne_one

def fullRecordGapValue07088 : Nat := fullRecordGapCenterValue + 400676

theorem fullRecordGapTerm07088_eq_value :
    recordGapCenter + 400676 = fullRecordGapValue07088 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07088_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07088 (fullRecordGapValue07088 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07088_not_prime : ¬(recordGapCenter + 400676).Prime := by
  rw [fullRecordGapTerm07088_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07088, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07088_fast_pow_mod_ne_one

def fullRecordGapValue07089 : Nat := fullRecordGapCenterValue + 400746

theorem fullRecordGapTerm07089_eq_value :
    recordGapCenter + 400746 = fullRecordGapValue07089 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07089_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07089 (fullRecordGapValue07089 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07089_not_prime : ¬(recordGapCenter + 400746).Prime := by
  rw [fullRecordGapTerm07089_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07089, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07089_fast_pow_mod_ne_one

def fullRecordGapValue07090 : Nat := fullRecordGapCenterValue + 400766

theorem fullRecordGapTerm07090_eq_value :
    recordGapCenter + 400766 = fullRecordGapValue07090 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07090_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07090 (fullRecordGapValue07090 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07090_not_prime : ¬(recordGapCenter + 400766).Prime := by
  rw [fullRecordGapTerm07090_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07090, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07090_fast_pow_mod_ne_one

def fullRecordGapValue07091 : Nat := fullRecordGapCenterValue + 400802

theorem fullRecordGapTerm07091_eq_value :
    recordGapCenter + 400802 = fullRecordGapValue07091 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07091_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07091 (fullRecordGapValue07091 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07091_not_prime : ¬(recordGapCenter + 400802).Prime := by
  rw [fullRecordGapTerm07091_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07091, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07091_fast_pow_mod_ne_one

def fullRecordGapValue07092 : Nat := fullRecordGapCenterValue + 400886

theorem fullRecordGapTerm07092_eq_value :
    recordGapCenter + 400886 = fullRecordGapValue07092 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07092_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07092 (fullRecordGapValue07092 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07092_not_prime : ¬(recordGapCenter + 400886).Prime := by
  rw [fullRecordGapTerm07092_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07092, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07092_fast_pow_mod_ne_one

def fullRecordGapValue07093 : Nat := fullRecordGapCenterValue + 400922

theorem fullRecordGapTerm07093_eq_value :
    recordGapCenter + 400922 = fullRecordGapValue07093 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07093_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07093 (fullRecordGapValue07093 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07093_not_prime : ¬(recordGapCenter + 400922).Prime := by
  rw [fullRecordGapTerm07093_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07093, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07093_fast_pow_mod_ne_one

def fullRecordGapValue07094 : Nat := fullRecordGapCenterValue + 401252

theorem fullRecordGapTerm07094_eq_value :
    recordGapCenter + 401252 = fullRecordGapValue07094 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07094_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07094 (fullRecordGapValue07094 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07094_not_prime : ¬(recordGapCenter + 401252).Prime := by
  rw [fullRecordGapTerm07094_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07094, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07094_fast_pow_mod_ne_one

def fullRecordGapValue07095 : Nat := fullRecordGapCenterValue + 401378

theorem fullRecordGapTerm07095_eq_value :
    recordGapCenter + 401378 = fullRecordGapValue07095 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07095_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07095 (fullRecordGapValue07095 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07095_not_prime : ¬(recordGapCenter + 401378).Prime := by
  rw [fullRecordGapTerm07095_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07095, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07095_fast_pow_mod_ne_one

def fullRecordGapValue07096 : Nat := fullRecordGapCenterValue + 401426

theorem fullRecordGapTerm07096_eq_value :
    recordGapCenter + 401426 = fullRecordGapValue07096 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07096_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07096 (fullRecordGapValue07096 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07096_not_prime : ¬(recordGapCenter + 401426).Prime := by
  rw [fullRecordGapTerm07096_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07096, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07096_fast_pow_mod_ne_one

def fullRecordGapValue07097 : Nat := fullRecordGapCenterValue + 401462

theorem fullRecordGapTerm07097_eq_value :
    recordGapCenter + 401462 = fullRecordGapValue07097 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07097_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07097 (fullRecordGapValue07097 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07097_not_prime : ¬(recordGapCenter + 401462).Prime := by
  rw [fullRecordGapTerm07097_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07097, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07097_fast_pow_mod_ne_one

def fullRecordGapValue07098 : Nat := fullRecordGapCenterValue + 401516

theorem fullRecordGapTerm07098_eq_value :
    recordGapCenter + 401516 = fullRecordGapValue07098 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07098_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07098 (fullRecordGapValue07098 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07098_not_prime : ¬(recordGapCenter + 401516).Prime := by
  rw [fullRecordGapTerm07098_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07098, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07098_fast_pow_mod_ne_one

def fullRecordGapValue07099 : Nat := fullRecordGapCenterValue + 401538

theorem fullRecordGapTerm07099_eq_value :
    recordGapCenter + 401538 = fullRecordGapValue07099 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07099_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07099 (fullRecordGapValue07099 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07099_not_prime : ¬(recordGapCenter + 401538).Prime := by
  rw [fullRecordGapTerm07099_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07099, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07099_fast_pow_mod_ne_one

def fullRecordGapValue07100 : Nat := fullRecordGapCenterValue + 401586

theorem fullRecordGapTerm07100_eq_value :
    recordGapCenter + 401586 = fullRecordGapValue07100 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07100_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07100 (fullRecordGapValue07100 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07100_not_prime : ¬(recordGapCenter + 401586).Prime := by
  rw [fullRecordGapTerm07100_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07100, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07100_fast_pow_mod_ne_one

def fullRecordGapValue07101 : Nat := fullRecordGapCenterValue + 401612

theorem fullRecordGapTerm07101_eq_value :
    recordGapCenter + 401612 = fullRecordGapValue07101 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07101_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07101 (fullRecordGapValue07101 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07101_not_prime : ¬(recordGapCenter + 401612).Prime := by
  rw [fullRecordGapTerm07101_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07101, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07101_fast_pow_mod_ne_one

def fullRecordGapValue07102 : Nat := fullRecordGapCenterValue + 401762

theorem fullRecordGapTerm07102_eq_value :
    recordGapCenter + 401762 = fullRecordGapValue07102 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07102_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07102 (fullRecordGapValue07102 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07102_not_prime : ¬(recordGapCenter + 401762).Prime := by
  rw [fullRecordGapTerm07102_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07102, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07102_fast_pow_mod_ne_one

def fullRecordGapValue07103 : Nat := fullRecordGapCenterValue + 401768

theorem fullRecordGapTerm07103_eq_value :
    recordGapCenter + 401768 = fullRecordGapValue07103 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07103_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07103 (fullRecordGapValue07103 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07103_not_prime : ¬(recordGapCenter + 401768).Prime := by
  rw [fullRecordGapTerm07103_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07103, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07103_fast_pow_mod_ne_one

def fullRecordGapValue07104 : Nat := fullRecordGapCenterValue + 401798

theorem fullRecordGapTerm07104_eq_value :
    recordGapCenter + 401798 = fullRecordGapValue07104 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07104_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07104 (fullRecordGapValue07104 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07104_not_prime : ¬(recordGapCenter + 401798).Prime := by
  rw [fullRecordGapTerm07104_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07104, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07104_fast_pow_mod_ne_one

def fullRecordGapValue07105 : Nat := fullRecordGapCenterValue + 401942

theorem fullRecordGapTerm07105_eq_value :
    recordGapCenter + 401942 = fullRecordGapValue07105 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07105_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07105 (fullRecordGapValue07105 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07105_not_prime : ¬(recordGapCenter + 401942).Prime := by
  rw [fullRecordGapTerm07105_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07105, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07105_fast_pow_mod_ne_one

def fullRecordGapValue07106 : Nat := fullRecordGapCenterValue + 401966

theorem fullRecordGapTerm07106_eq_value :
    recordGapCenter + 401966 = fullRecordGapValue07106 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07106_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07106 (fullRecordGapValue07106 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07106_not_prime : ¬(recordGapCenter + 401966).Prime := by
  rw [fullRecordGapTerm07106_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07106, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07106_fast_pow_mod_ne_one

def fullRecordGapValue07107 : Nat := fullRecordGapCenterValue + 401972

theorem fullRecordGapTerm07107_eq_value :
    recordGapCenter + 401972 = fullRecordGapValue07107 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07107_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07107 (fullRecordGapValue07107 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07107_not_prime : ¬(recordGapCenter + 401972).Prime := by
  rw [fullRecordGapTerm07107_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07107, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07107_fast_pow_mod_ne_one

def fullRecordGapValue07108 : Nat := fullRecordGapCenterValue + 402092

theorem fullRecordGapTerm07108_eq_value :
    recordGapCenter + 402092 = fullRecordGapValue07108 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07108_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07108 (fullRecordGapValue07108 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07108_not_prime : ¬(recordGapCenter + 402092).Prime := by
  rw [fullRecordGapTerm07108_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07108, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07108_fast_pow_mod_ne_one

def fullRecordGapValue07109 : Nat := fullRecordGapCenterValue + 402098

theorem fullRecordGapTerm07109_eq_value :
    recordGapCenter + 402098 = fullRecordGapValue07109 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07109_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07109 (fullRecordGapValue07109 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07109_not_prime : ¬(recordGapCenter + 402098).Prime := by
  rw [fullRecordGapTerm07109_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07109, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07109_fast_pow_mod_ne_one

def fullRecordGapValue07110 : Nat := fullRecordGapCenterValue + 402126

theorem fullRecordGapTerm07110_eq_value :
    recordGapCenter + 402126 = fullRecordGapValue07110 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07110_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07110 (fullRecordGapValue07110 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07110_not_prime : ¬(recordGapCenter + 402126).Prime := by
  rw [fullRecordGapTerm07110_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07110, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07110_fast_pow_mod_ne_one

def fullRecordGapValue07111 : Nat := fullRecordGapCenterValue + 402188

theorem fullRecordGapTerm07111_eq_value :
    recordGapCenter + 402188 = fullRecordGapValue07111 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07111_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07111 (fullRecordGapValue07111 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07111_not_prime : ¬(recordGapCenter + 402188).Prime := by
  rw [fullRecordGapTerm07111_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07111, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07111_fast_pow_mod_ne_one

def fullRecordGapValue07112 : Nat := fullRecordGapCenterValue + 402386

theorem fullRecordGapTerm07112_eq_value :
    recordGapCenter + 402386 = fullRecordGapValue07112 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07112_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07112 (fullRecordGapValue07112 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07112_not_prime : ¬(recordGapCenter + 402386).Prime := by
  rw [fullRecordGapTerm07112_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07112, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07112_fast_pow_mod_ne_one

def fullRecordGapValue07113 : Nat := fullRecordGapCenterValue + 402452

theorem fullRecordGapTerm07113_eq_value :
    recordGapCenter + 402452 = fullRecordGapValue07113 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07113_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07113 (fullRecordGapValue07113 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07113_not_prime : ¬(recordGapCenter + 402452).Prime := by
  rw [fullRecordGapTerm07113_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07113, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07113_fast_pow_mod_ne_one

def fullRecordGapValue07114 : Nat := fullRecordGapCenterValue + 402692

theorem fullRecordGapTerm07114_eq_value :
    recordGapCenter + 402692 = fullRecordGapValue07114 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07114_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07114 (fullRecordGapValue07114 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07114_not_prime : ¬(recordGapCenter + 402692).Prime := by
  rw [fullRecordGapTerm07114_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07114, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07114_fast_pow_mod_ne_one

def fullRecordGapValue07115 : Nat := fullRecordGapCenterValue + 402806

theorem fullRecordGapTerm07115_eq_value :
    recordGapCenter + 402806 = fullRecordGapValue07115 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07115_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07115 (fullRecordGapValue07115 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07115_not_prime : ¬(recordGapCenter + 402806).Prime := by
  rw [fullRecordGapTerm07115_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07115, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07115_fast_pow_mod_ne_one

def fullRecordGapValue07116 : Nat := fullRecordGapCenterValue + 402812

theorem fullRecordGapTerm07116_eq_value :
    recordGapCenter + 402812 = fullRecordGapValue07116 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07116_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07116 (fullRecordGapValue07116 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07116_not_prime : ¬(recordGapCenter + 402812).Prime := by
  rw [fullRecordGapTerm07116_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07116, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07116_fast_pow_mod_ne_one

def fullRecordGapValue07117 : Nat := fullRecordGapCenterValue + 402902

theorem fullRecordGapTerm07117_eq_value :
    recordGapCenter + 402902 = fullRecordGapValue07117 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07117_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07117 (fullRecordGapValue07117 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07117_not_prime : ¬(recordGapCenter + 402902).Prime := by
  rw [fullRecordGapTerm07117_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07117, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07117_fast_pow_mod_ne_one

def fullRecordGapValue07118 : Nat := fullRecordGapCenterValue + 402932

theorem fullRecordGapTerm07118_eq_value :
    recordGapCenter + 402932 = fullRecordGapValue07118 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07118_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07118 (fullRecordGapValue07118 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07118_not_prime : ¬(recordGapCenter + 402932).Prime := by
  rw [fullRecordGapTerm07118_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07118, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07118_fast_pow_mod_ne_one

def fullRecordGapValue07119 : Nat := fullRecordGapCenterValue + 403016

theorem fullRecordGapTerm07119_eq_value :
    recordGapCenter + 403016 = fullRecordGapValue07119 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07119_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07119 (fullRecordGapValue07119 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07119_not_prime : ¬(recordGapCenter + 403016).Prime := by
  rw [fullRecordGapTerm07119_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07119, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07119_fast_pow_mod_ne_one

def fullRecordGapValue07120 : Nat := fullRecordGapCenterValue + 403076

theorem fullRecordGapTerm07120_eq_value :
    recordGapCenter + 403076 = fullRecordGapValue07120 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07120_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07120 (fullRecordGapValue07120 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07120_not_prime : ¬(recordGapCenter + 403076).Prime := by
  rw [fullRecordGapTerm07120_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07120, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07120_fast_pow_mod_ne_one

def fullRecordGapValue07121 : Nat := fullRecordGapCenterValue + 403148

theorem fullRecordGapTerm07121_eq_value :
    recordGapCenter + 403148 = fullRecordGapValue07121 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07121_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07121 (fullRecordGapValue07121 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07121_not_prime : ¬(recordGapCenter + 403148).Prime := by
  rw [fullRecordGapTerm07121_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07121, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07121_fast_pow_mod_ne_one

def fullRecordGapValue07122 : Nat := fullRecordGapCenterValue + 403266

theorem fullRecordGapTerm07122_eq_value :
    recordGapCenter + 403266 = fullRecordGapValue07122 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07122_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07122 (fullRecordGapValue07122 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07122_not_prime : ¬(recordGapCenter + 403266).Prime := by
  rw [fullRecordGapTerm07122_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07122, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07122_fast_pow_mod_ne_one

def fullRecordGapValue07123 : Nat := fullRecordGapCenterValue + 403292

theorem fullRecordGapTerm07123_eq_value :
    recordGapCenter + 403292 = fullRecordGapValue07123 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07123_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07123 (fullRecordGapValue07123 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07123_not_prime : ¬(recordGapCenter + 403292).Prime := by
  rw [fullRecordGapTerm07123_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07123, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07123_fast_pow_mod_ne_one

def fullRecordGapValue07124 : Nat := fullRecordGapCenterValue + 403302

theorem fullRecordGapTerm07124_eq_value :
    recordGapCenter + 403302 = fullRecordGapValue07124 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07124_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07124 (fullRecordGapValue07124 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07124_not_prime : ¬(recordGapCenter + 403302).Prime := by
  rw [fullRecordGapTerm07124_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07124, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07124_fast_pow_mod_ne_one

def fullRecordGapValue07125 : Nat := fullRecordGapCenterValue + 403386

theorem fullRecordGapTerm07125_eq_value :
    recordGapCenter + 403386 = fullRecordGapValue07125 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07125_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07125 (fullRecordGapValue07125 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07125_not_prime : ¬(recordGapCenter + 403386).Prime := by
  rw [fullRecordGapTerm07125_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07125, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07125_fast_pow_mod_ne_one

def fullRecordGapValue07126 : Nat := fullRecordGapCenterValue + 403412

theorem fullRecordGapTerm07126_eq_value :
    recordGapCenter + 403412 = fullRecordGapValue07126 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07126_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07126 (fullRecordGapValue07126 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07126_not_prime : ¬(recordGapCenter + 403412).Prime := by
  rw [fullRecordGapTerm07126_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07126, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07126_fast_pow_mod_ne_one

def fullRecordGapValue07127 : Nat := fullRecordGapCenterValue + 403418

theorem fullRecordGapTerm07127_eq_value :
    recordGapCenter + 403418 = fullRecordGapValue07127 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07127_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07127 (fullRecordGapValue07127 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07127_not_prime : ¬(recordGapCenter + 403418).Prime := by
  rw [fullRecordGapTerm07127_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07127, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07127_fast_pow_mod_ne_one

def fullRecordGapValue07128 : Nat := fullRecordGapCenterValue + 403538

theorem fullRecordGapTerm07128_eq_value :
    recordGapCenter + 403538 = fullRecordGapValue07128 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07128_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07128 (fullRecordGapValue07128 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07128_not_prime : ¬(recordGapCenter + 403538).Prime := by
  rw [fullRecordGapTerm07128_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07128, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07128_fast_pow_mod_ne_one

def fullRecordGapValue07129 : Nat := fullRecordGapCenterValue + 403562

theorem fullRecordGapTerm07129_eq_value :
    recordGapCenter + 403562 = fullRecordGapValue07129 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07129_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07129 (fullRecordGapValue07129 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07129_not_prime : ¬(recordGapCenter + 403562).Prime := by
  rw [fullRecordGapTerm07129_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07129, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07129_fast_pow_mod_ne_one

def fullRecordGapValue07130 : Nat := fullRecordGapCenterValue + 403566

theorem fullRecordGapTerm07130_eq_value :
    recordGapCenter + 403566 = fullRecordGapValue07130 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07130_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07130 (fullRecordGapValue07130 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07130_not_prime : ¬(recordGapCenter + 403566).Prime := by
  rw [fullRecordGapTerm07130_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07130, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07130_fast_pow_mod_ne_one

def fullRecordGapValue07131 : Nat := fullRecordGapCenterValue + 403638

theorem fullRecordGapTerm07131_eq_value :
    recordGapCenter + 403638 = fullRecordGapValue07131 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07131_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07131 (fullRecordGapValue07131 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07131_not_prime : ¬(recordGapCenter + 403638).Prime := by
  rw [fullRecordGapTerm07131_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07131, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07131_fast_pow_mod_ne_one

def fullRecordGapValue07132 : Nat := fullRecordGapCenterValue + 403778

theorem fullRecordGapTerm07132_eq_value :
    recordGapCenter + 403778 = fullRecordGapValue07132 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07132_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07132 (fullRecordGapValue07132 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07132_not_prime : ¬(recordGapCenter + 403778).Prime := by
  rw [fullRecordGapTerm07132_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07132, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07132_fast_pow_mod_ne_one

def fullRecordGapValue07133 : Nat := fullRecordGapCenterValue + 403838

theorem fullRecordGapTerm07133_eq_value :
    recordGapCenter + 403838 = fullRecordGapValue07133 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07133_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07133 (fullRecordGapValue07133 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07133_not_prime : ¬(recordGapCenter + 403838).Prime := by
  rw [fullRecordGapTerm07133_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07133, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07133_fast_pow_mod_ne_one

def fullRecordGapValue07134 : Nat := fullRecordGapCenterValue + 403946

theorem fullRecordGapTerm07134_eq_value :
    recordGapCenter + 403946 = fullRecordGapValue07134 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07134_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07134 (fullRecordGapValue07134 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07134_not_prime : ¬(recordGapCenter + 403946).Prime := by
  rw [fullRecordGapTerm07134_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07134, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07134_fast_pow_mod_ne_one

def fullRecordGapValue07135 : Nat := fullRecordGapCenterValue + 404126

theorem fullRecordGapTerm07135_eq_value :
    recordGapCenter + 404126 = fullRecordGapValue07135 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07135_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07135 (fullRecordGapValue07135 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07135_not_prime : ¬(recordGapCenter + 404126).Prime := by
  rw [fullRecordGapTerm07135_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07135, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07135_fast_pow_mod_ne_one

def fullRecordGapValue07136 : Nat := fullRecordGapCenterValue + 404252

theorem fullRecordGapTerm07136_eq_value :
    recordGapCenter + 404252 = fullRecordGapValue07136 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07136_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07136 (fullRecordGapValue07136 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07136_not_prime : ¬(recordGapCenter + 404252).Prime := by
  rw [fullRecordGapTerm07136_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07136, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07136_fast_pow_mod_ne_one

def fullRecordGapValue07137 : Nat := fullRecordGapCenterValue + 404258

theorem fullRecordGapTerm07137_eq_value :
    recordGapCenter + 404258 = fullRecordGapValue07137 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07137_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07137 (fullRecordGapValue07137 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07137_not_prime : ¬(recordGapCenter + 404258).Prime := by
  rw [fullRecordGapTerm07137_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07137, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07137_fast_pow_mod_ne_one

def fullRecordGapValue07138 : Nat := fullRecordGapCenterValue + 404346

theorem fullRecordGapTerm07138_eq_value :
    recordGapCenter + 404346 = fullRecordGapValue07138 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07138_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07138 (fullRecordGapValue07138 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07138_not_prime : ¬(recordGapCenter + 404346).Prime := by
  rw [fullRecordGapTerm07138_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07138, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07138_fast_pow_mod_ne_one

def fullRecordGapValue07139 : Nat := fullRecordGapCenterValue + 404366

theorem fullRecordGapTerm07139_eq_value :
    recordGapCenter + 404366 = fullRecordGapValue07139 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07139_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07139 (fullRecordGapValue07139 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07139_not_prime : ¬(recordGapCenter + 404366).Prime := by
  rw [fullRecordGapTerm07139_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07139, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07139_fast_pow_mod_ne_one

def fullRecordGapValue07140 : Nat := fullRecordGapCenterValue + 404402

theorem fullRecordGapTerm07140_eq_value :
    recordGapCenter + 404402 = fullRecordGapValue07140 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07140_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07140 (fullRecordGapValue07140 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07140_not_prime : ¬(recordGapCenter + 404402).Prime := by
  rw [fullRecordGapTerm07140_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07140, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07140_fast_pow_mod_ne_one

def fullRecordGapValue07141 : Nat := fullRecordGapCenterValue + 404526

theorem fullRecordGapTerm07141_eq_value :
    recordGapCenter + 404526 = fullRecordGapValue07141 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07141_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07141 (fullRecordGapValue07141 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07141_not_prime : ¬(recordGapCenter + 404526).Prime := by
  rw [fullRecordGapTerm07141_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07141, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07141_fast_pow_mod_ne_one

def fullRecordGapValue07142 : Nat := fullRecordGapCenterValue + 404762

theorem fullRecordGapTerm07142_eq_value :
    recordGapCenter + 404762 = fullRecordGapValue07142 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07142_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07142 (fullRecordGapValue07142 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07142_not_prime : ¬(recordGapCenter + 404762).Prime := by
  rw [fullRecordGapTerm07142_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07142, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07142_fast_pow_mod_ne_one

def fullRecordGapValue07143 : Nat := fullRecordGapCenterValue + 404792

theorem fullRecordGapTerm07143_eq_value :
    recordGapCenter + 404792 = fullRecordGapValue07143 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07143_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07143 (fullRecordGapValue07143 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07143_not_prime : ¬(recordGapCenter + 404792).Prime := by
  rw [fullRecordGapTerm07143_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07143, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07143_fast_pow_mod_ne_one

def fullRecordGapValue07144 : Nat := fullRecordGapCenterValue + 404958

theorem fullRecordGapTerm07144_eq_value :
    recordGapCenter + 404958 = fullRecordGapValue07144 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07144_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07144 (fullRecordGapValue07144 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07144_not_prime : ¬(recordGapCenter + 404958).Prime := by
  rw [fullRecordGapTerm07144_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07144, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07144_fast_pow_mod_ne_one

def fullRecordGapValue07145 : Nat := fullRecordGapCenterValue + 405000

theorem fullRecordGapTerm07145_eq_value :
    recordGapCenter + 405000 = fullRecordGapValue07145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07145 (fullRecordGapValue07145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07145_not_prime : ¬(recordGapCenter + 405000).Prime := by
  rw [fullRecordGapTerm07145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07145_fast_pow_mod_ne_one

def fullRecordGapValue07146 : Nat := fullRecordGapCenterValue + 405116

theorem fullRecordGapTerm07146_eq_value :
    recordGapCenter + 405116 = fullRecordGapValue07146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07146 (fullRecordGapValue07146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07146_not_prime : ¬(recordGapCenter + 405116).Prime := by
  rw [fullRecordGapTerm07146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07146_fast_pow_mod_ne_one

def fullRecordGapValue07147 : Nat := fullRecordGapCenterValue + 405176

theorem fullRecordGapTerm07147_eq_value :
    recordGapCenter + 405176 = fullRecordGapValue07147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07147 (fullRecordGapValue07147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07147_not_prime : ¬(recordGapCenter + 405176).Prime := by
  rw [fullRecordGapTerm07147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07147_fast_pow_mod_ne_one

def fullRecordGapValue07148 : Nat := fullRecordGapCenterValue + 405282

theorem fullRecordGapTerm07148_eq_value :
    recordGapCenter + 405282 = fullRecordGapValue07148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07148 (fullRecordGapValue07148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07148_not_prime : ¬(recordGapCenter + 405282).Prime := by
  rw [fullRecordGapTerm07148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07148_fast_pow_mod_ne_one

def fullRecordGapValue07149 : Nat := fullRecordGapCenterValue + 405332

theorem fullRecordGapTerm07149_eq_value :
    recordGapCenter + 405332 = fullRecordGapValue07149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07149 (fullRecordGapValue07149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07149_not_prime : ¬(recordGapCenter + 405332).Prime := by
  rw [fullRecordGapTerm07149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07149_fast_pow_mod_ne_one

def fullRecordGapValue07150 : Nat := fullRecordGapCenterValue + 405386

theorem fullRecordGapTerm07150_eq_value :
    recordGapCenter + 405386 = fullRecordGapValue07150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07150 (fullRecordGapValue07150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07150_not_prime : ¬(recordGapCenter + 405386).Prime := by
  rw [fullRecordGapTerm07150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07150_fast_pow_mod_ne_one

def fullRecordGapValue07151 : Nat := fullRecordGapCenterValue + 405402

theorem fullRecordGapTerm07151_eq_value :
    recordGapCenter + 405402 = fullRecordGapValue07151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07151 (fullRecordGapValue07151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07151_not_prime : ¬(recordGapCenter + 405402).Prime := by
  rw [fullRecordGapTerm07151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07151_fast_pow_mod_ne_one

def fullRecordGapValue07152 : Nat := fullRecordGapCenterValue + 405452

theorem fullRecordGapTerm07152_eq_value :
    recordGapCenter + 405452 = fullRecordGapValue07152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07152 (fullRecordGapValue07152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07152_not_prime : ¬(recordGapCenter + 405452).Prime := by
  rw [fullRecordGapTerm07152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07152_fast_pow_mod_ne_one

def fullRecordGapValue07153 : Nat := fullRecordGapCenterValue + 405458

theorem fullRecordGapTerm07153_eq_value :
    recordGapCenter + 405458 = fullRecordGapValue07153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07153 (fullRecordGapValue07153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07153_not_prime : ¬(recordGapCenter + 405458).Prime := by
  rw [fullRecordGapTerm07153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07153_fast_pow_mod_ne_one

def fullRecordGapValue07154 : Nat := fullRecordGapCenterValue + 405506

theorem fullRecordGapTerm07154_eq_value :
    recordGapCenter + 405506 = fullRecordGapValue07154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07154 (fullRecordGapValue07154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07154_not_prime : ¬(recordGapCenter + 405506).Prime := by
  rw [fullRecordGapTerm07154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07154_fast_pow_mod_ne_one

def fullRecordGapValue07155 : Nat := fullRecordGapCenterValue + 405906

theorem fullRecordGapTerm07155_eq_value :
    recordGapCenter + 405906 = fullRecordGapValue07155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07155 (fullRecordGapValue07155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07155_not_prime : ¬(recordGapCenter + 405906).Prime := by
  rw [fullRecordGapTerm07155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07155_fast_pow_mod_ne_one

def fullRecordGapValue07156 : Nat := fullRecordGapCenterValue + 405932

theorem fullRecordGapTerm07156_eq_value :
    recordGapCenter + 405932 = fullRecordGapValue07156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07156 (fullRecordGapValue07156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07156_not_prime : ¬(recordGapCenter + 405932).Prime := by
  rw [fullRecordGapTerm07156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07156_fast_pow_mod_ne_one

def fullRecordGapValue07157 : Nat := fullRecordGapCenterValue + 405998

theorem fullRecordGapTerm07157_eq_value :
    recordGapCenter + 405998 = fullRecordGapValue07157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07157 (fullRecordGapValue07157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07157_not_prime : ¬(recordGapCenter + 405998).Prime := by
  rw [fullRecordGapTerm07157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07157_fast_pow_mod_ne_one

def fullRecordGapValue07158 : Nat := fullRecordGapCenterValue + 406052

theorem fullRecordGapTerm07158_eq_value :
    recordGapCenter + 406052 = fullRecordGapValue07158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07158 (fullRecordGapValue07158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07158_not_prime : ¬(recordGapCenter + 406052).Prime := by
  rw [fullRecordGapTerm07158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07158_fast_pow_mod_ne_one

def fullRecordGapValue07159 : Nat := fullRecordGapCenterValue + 406338

theorem fullRecordGapTerm07159_eq_value :
    recordGapCenter + 406338 = fullRecordGapValue07159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07159 (fullRecordGapValue07159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07159_not_prime : ¬(recordGapCenter + 406338).Prime := by
  rw [fullRecordGapTerm07159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07159_fast_pow_mod_ne_one

def fullRecordGapValue07160 : Nat := fullRecordGapCenterValue + 406418

theorem fullRecordGapTerm07160_eq_value :
    recordGapCenter + 406418 = fullRecordGapValue07160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07160 (fullRecordGapValue07160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07160_not_prime : ¬(recordGapCenter + 406418).Prime := by
  rw [fullRecordGapTerm07160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07160_fast_pow_mod_ne_one

def fullRecordGapValue07161 : Nat := fullRecordGapCenterValue + 406442

theorem fullRecordGapTerm07161_eq_value :
    recordGapCenter + 406442 = fullRecordGapValue07161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07161 (fullRecordGapValue07161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07161_not_prime : ¬(recordGapCenter + 406442).Prime := by
  rw [fullRecordGapTerm07161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07161_fast_pow_mod_ne_one

def fullRecordGapValue07162 : Nat := fullRecordGapCenterValue + 406506

theorem fullRecordGapTerm07162_eq_value :
    recordGapCenter + 406506 = fullRecordGapValue07162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07162 (fullRecordGapValue07162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07162_not_prime : ¬(recordGapCenter + 406506).Prime := by
  rw [fullRecordGapTerm07162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07162_fast_pow_mod_ne_one

def fullRecordGapValue07163 : Nat := fullRecordGapCenterValue + 406560

theorem fullRecordGapTerm07163_eq_value :
    recordGapCenter + 406560 = fullRecordGapValue07163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07163 (fullRecordGapValue07163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07163_not_prime : ¬(recordGapCenter + 406560).Prime := by
  rw [fullRecordGapTerm07163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07163_fast_pow_mod_ne_one

def fullRecordGapValue07164 : Nat := fullRecordGapCenterValue + 406646

theorem fullRecordGapTerm07164_eq_value :
    recordGapCenter + 406646 = fullRecordGapValue07164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07164 (fullRecordGapValue07164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07164_not_prime : ¬(recordGapCenter + 406646).Prime := by
  rw [fullRecordGapTerm07164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07164_fast_pow_mod_ne_one

def fullRecordGapValue07165 : Nat := fullRecordGapCenterValue + 406682

theorem fullRecordGapTerm07165_eq_value :
    recordGapCenter + 406682 = fullRecordGapValue07165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07165 (fullRecordGapValue07165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07165_not_prime : ¬(recordGapCenter + 406682).Prime := by
  rw [fullRecordGapTerm07165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07165_fast_pow_mod_ne_one

def fullRecordGapValue07166 : Nat := fullRecordGapCenterValue + 406698

theorem fullRecordGapTerm07166_eq_value :
    recordGapCenter + 406698 = fullRecordGapValue07166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07166 (fullRecordGapValue07166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07166_not_prime : ¬(recordGapCenter + 406698).Prime := by
  rw [fullRecordGapTerm07166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07166_fast_pow_mod_ne_one

def fullRecordGapValue07167 : Nat := fullRecordGapCenterValue + 406712

theorem fullRecordGapTerm07167_eq_value :
    recordGapCenter + 406712 = fullRecordGapValue07167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07167 (fullRecordGapValue07167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07167_not_prime : ¬(recordGapCenter + 406712).Prime := by
  rw [fullRecordGapTerm07167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07167_fast_pow_mod_ne_one

def fullRecordGapValue07168 : Nat := fullRecordGapCenterValue + 406856

theorem fullRecordGapTerm07168_eq_value :
    recordGapCenter + 406856 = fullRecordGapValue07168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07168 (fullRecordGapValue07168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07168_not_prime : ¬(recordGapCenter + 406856).Prime := by
  rw [fullRecordGapTerm07168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07168_fast_pow_mod_ne_one

end PrimeFactorUnimodality
