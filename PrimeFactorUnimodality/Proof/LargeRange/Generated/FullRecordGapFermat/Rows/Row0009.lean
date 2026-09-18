import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue02049 : Nat := fullRecordGapCenterValue - 288994

theorem fullRecordGapTerm02049_eq_value :
    recordGapCenter - 288994 = fullRecordGapValue02049 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02049_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02049 (fullRecordGapValue02049 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02049_not_prime : ¬(recordGapCenter - 288994).Prime := by
  rw [fullRecordGapTerm02049_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02049, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02049_fast_pow_mod_ne_one

def fullRecordGapValue02050 : Nat := fullRecordGapCenterValue - 288892

theorem fullRecordGapTerm02050_eq_value :
    recordGapCenter - 288892 = fullRecordGapValue02050 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02050_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02050 (fullRecordGapValue02050 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02050_not_prime : ¬(recordGapCenter - 288892).Prime := by
  rw [fullRecordGapTerm02050_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02050, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02050_fast_pow_mod_ne_one

def fullRecordGapValue02051 : Nat := fullRecordGapCenterValue - 288844

theorem fullRecordGapTerm02051_eq_value :
    recordGapCenter - 288844 = fullRecordGapValue02051 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02051_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02051 (fullRecordGapValue02051 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02051_not_prime : ¬(recordGapCenter - 288844).Prime := by
  rw [fullRecordGapTerm02051_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02051, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02051_fast_pow_mod_ne_one

def fullRecordGapValue02052 : Nat := fullRecordGapCenterValue - 288682

theorem fullRecordGapTerm02052_eq_value :
    recordGapCenter - 288682 = fullRecordGapValue02052 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02052_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02052 (fullRecordGapValue02052 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02052_not_prime : ¬(recordGapCenter - 288682).Prime := by
  rw [fullRecordGapTerm02052_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02052, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02052_fast_pow_mod_ne_one

def fullRecordGapValue02053 : Nat := fullRecordGapCenterValue - 288474

theorem fullRecordGapTerm02053_eq_value :
    recordGapCenter - 288474 = fullRecordGapValue02053 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02053_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02053 (fullRecordGapValue02053 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02053_not_prime : ¬(recordGapCenter - 288474).Prime := by
  rw [fullRecordGapTerm02053_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02053, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02053_fast_pow_mod_ne_one

def fullRecordGapValue02054 : Nat := fullRecordGapCenterValue - 288322

theorem fullRecordGapTerm02054_eq_value :
    recordGapCenter - 288322 = fullRecordGapValue02054 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02054_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02054 (fullRecordGapValue02054 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02054_not_prime : ¬(recordGapCenter - 288322).Prime := by
  rw [fullRecordGapTerm02054_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02054, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02054_fast_pow_mod_ne_one

def fullRecordGapValue02055 : Nat := fullRecordGapCenterValue - 288294

theorem fullRecordGapTerm02055_eq_value :
    recordGapCenter - 288294 = fullRecordGapValue02055 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02055_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02055 (fullRecordGapValue02055 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02055_not_prime : ¬(recordGapCenter - 288294).Prime := by
  rw [fullRecordGapTerm02055_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02055, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02055_fast_pow_mod_ne_one

def fullRecordGapValue02056 : Nat := fullRecordGapCenterValue - 288174

theorem fullRecordGapTerm02056_eq_value :
    recordGapCenter - 288174 = fullRecordGapValue02056 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02056_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02056 (fullRecordGapValue02056 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02056_not_prime : ¬(recordGapCenter - 288174).Prime := by
  rw [fullRecordGapTerm02056_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02056, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02056_fast_pow_mod_ne_one

def fullRecordGapValue02057 : Nat := fullRecordGapCenterValue - 288172

theorem fullRecordGapTerm02057_eq_value :
    recordGapCenter - 288172 = fullRecordGapValue02057 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02057_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02057 (fullRecordGapValue02057 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02057_not_prime : ¬(recordGapCenter - 288172).Prime := by
  rw [fullRecordGapTerm02057_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02057, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02057_fast_pow_mod_ne_one

def fullRecordGapValue02058 : Nat := fullRecordGapCenterValue - 288124

theorem fullRecordGapTerm02058_eq_value :
    recordGapCenter - 288124 = fullRecordGapValue02058 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02058_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02058 (fullRecordGapValue02058 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02058_not_prime : ¬(recordGapCenter - 288124).Prime := by
  rw [fullRecordGapTerm02058_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02058, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02058_fast_pow_mod_ne_one

def fullRecordGapValue02059 : Nat := fullRecordGapCenterValue - 288120

theorem fullRecordGapTerm02059_eq_value :
    recordGapCenter - 288120 = fullRecordGapValue02059 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02059_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02059 (fullRecordGapValue02059 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02059_not_prime : ¬(recordGapCenter - 288120).Prime := by
  rw [fullRecordGapTerm02059_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02059, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02059_fast_pow_mod_ne_one

def fullRecordGapValue02060 : Nat := fullRecordGapCenterValue - 288000

theorem fullRecordGapTerm02060_eq_value :
    recordGapCenter - 288000 = fullRecordGapValue02060 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02060_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02060 (fullRecordGapValue02060 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02060_not_prime : ¬(recordGapCenter - 288000).Prime := by
  rw [fullRecordGapTerm02060_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02060, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02060_fast_pow_mod_ne_one

def fullRecordGapValue02061 : Nat := fullRecordGapCenterValue - 287884

theorem fullRecordGapTerm02061_eq_value :
    recordGapCenter - 287884 = fullRecordGapValue02061 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02061_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02061 (fullRecordGapValue02061 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02061_not_prime : ¬(recordGapCenter - 287884).Prime := by
  rw [fullRecordGapTerm02061_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02061, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02061_fast_pow_mod_ne_one

def fullRecordGapValue02062 : Nat := fullRecordGapCenterValue - 287662

theorem fullRecordGapTerm02062_eq_value :
    recordGapCenter - 287662 = fullRecordGapValue02062 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02062_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02062 (fullRecordGapValue02062 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02062_not_prime : ¬(recordGapCenter - 287662).Prime := by
  rw [fullRecordGapTerm02062_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02062, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02062_fast_pow_mod_ne_one

def fullRecordGapValue02063 : Nat := fullRecordGapCenterValue - 287634

theorem fullRecordGapTerm02063_eq_value :
    recordGapCenter - 287634 = fullRecordGapValue02063 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02063_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02063 (fullRecordGapValue02063 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02063_not_prime : ¬(recordGapCenter - 287634).Prime := by
  rw [fullRecordGapTerm02063_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02063, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02063_fast_pow_mod_ne_one

def fullRecordGapValue02064 : Nat := fullRecordGapCenterValue - 287548

theorem fullRecordGapTerm02064_eq_value :
    recordGapCenter - 287548 = fullRecordGapValue02064 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02064_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02064 (fullRecordGapValue02064 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02064_not_prime : ¬(recordGapCenter - 287548).Prime := by
  rw [fullRecordGapTerm02064_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02064, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02064_fast_pow_mod_ne_one

def fullRecordGapValue02065 : Nat := fullRecordGapCenterValue - 287502

theorem fullRecordGapTerm02065_eq_value :
    recordGapCenter - 287502 = fullRecordGapValue02065 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02065_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02065 (fullRecordGapValue02065 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02065_not_prime : ¬(recordGapCenter - 287502).Prime := by
  rw [fullRecordGapTerm02065_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02065, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02065_fast_pow_mod_ne_one

def fullRecordGapValue02066 : Nat := fullRecordGapCenterValue - 287458

theorem fullRecordGapTerm02066_eq_value :
    recordGapCenter - 287458 = fullRecordGapValue02066 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02066_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02066 (fullRecordGapValue02066 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02066_not_prime : ¬(recordGapCenter - 287458).Prime := by
  rw [fullRecordGapTerm02066_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02066, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02066_fast_pow_mod_ne_one

def fullRecordGapValue02067 : Nat := fullRecordGapCenterValue - 287418

theorem fullRecordGapTerm02067_eq_value :
    recordGapCenter - 287418 = fullRecordGapValue02067 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02067_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02067 (fullRecordGapValue02067 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02067_not_prime : ¬(recordGapCenter - 287418).Prime := by
  rw [fullRecordGapTerm02067_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02067, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02067_fast_pow_mod_ne_one

def fullRecordGapValue02068 : Nat := fullRecordGapCenterValue - 287284

theorem fullRecordGapTerm02068_eq_value :
    recordGapCenter - 287284 = fullRecordGapValue02068 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02068_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02068 (fullRecordGapValue02068 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02068_not_prime : ¬(recordGapCenter - 287284).Prime := by
  rw [fullRecordGapTerm02068_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02068, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02068_fast_pow_mod_ne_one

def fullRecordGapValue02069 : Nat := fullRecordGapCenterValue - 286978

theorem fullRecordGapTerm02069_eq_value :
    recordGapCenter - 286978 = fullRecordGapValue02069 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02069_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02069 (fullRecordGapValue02069 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02069_not_prime : ¬(recordGapCenter - 286978).Prime := by
  rw [fullRecordGapTerm02069_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02069, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02069_fast_pow_mod_ne_one

def fullRecordGapValue02070 : Nat := fullRecordGapCenterValue - 286954

theorem fullRecordGapTerm02070_eq_value :
    recordGapCenter - 286954 = fullRecordGapValue02070 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02070_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02070 (fullRecordGapValue02070 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02070_not_prime : ¬(recordGapCenter - 286954).Prime := by
  rw [fullRecordGapTerm02070_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02070, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02070_fast_pow_mod_ne_one

def fullRecordGapValue02071 : Nat := fullRecordGapCenterValue - 286828

theorem fullRecordGapTerm02071_eq_value :
    recordGapCenter - 286828 = fullRecordGapValue02071 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02071_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02071 (fullRecordGapValue02071 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02071_not_prime : ¬(recordGapCenter - 286828).Prime := by
  rw [fullRecordGapTerm02071_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02071, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02071_fast_pow_mod_ne_one

def fullRecordGapValue02072 : Nat := fullRecordGapCenterValue - 286720

theorem fullRecordGapTerm02072_eq_value :
    recordGapCenter - 286720 = fullRecordGapValue02072 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02072_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02072 (fullRecordGapValue02072 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02072_not_prime : ¬(recordGapCenter - 286720).Prime := by
  rw [fullRecordGapTerm02072_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02072, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02072_fast_pow_mod_ne_one

def fullRecordGapValue02073 : Nat := fullRecordGapCenterValue - 286684

theorem fullRecordGapTerm02073_eq_value :
    recordGapCenter - 286684 = fullRecordGapValue02073 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02073_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02073 (fullRecordGapValue02073 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02073_not_prime : ¬(recordGapCenter - 286684).Prime := by
  rw [fullRecordGapTerm02073_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02073, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02073_fast_pow_mod_ne_one

def fullRecordGapValue02074 : Nat := fullRecordGapCenterValue - 286674

theorem fullRecordGapTerm02074_eq_value :
    recordGapCenter - 286674 = fullRecordGapValue02074 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02074_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02074 (fullRecordGapValue02074 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02074_not_prime : ¬(recordGapCenter - 286674).Prime := by
  rw [fullRecordGapTerm02074_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02074, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02074_fast_pow_mod_ne_one

def fullRecordGapValue02075 : Nat := fullRecordGapCenterValue - 286662

theorem fullRecordGapTerm02075_eq_value :
    recordGapCenter - 286662 = fullRecordGapValue02075 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02075_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02075 (fullRecordGapValue02075 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02075_not_prime : ¬(recordGapCenter - 286662).Prime := by
  rw [fullRecordGapTerm02075_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02075, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02075_fast_pow_mod_ne_one

def fullRecordGapValue02076 : Nat := fullRecordGapCenterValue - 286372

theorem fullRecordGapTerm02076_eq_value :
    recordGapCenter - 286372 = fullRecordGapValue02076 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02076_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02076 (fullRecordGapValue02076 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02076_not_prime : ¬(recordGapCenter - 286372).Prime := by
  rw [fullRecordGapTerm02076_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02076, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02076_fast_pow_mod_ne_one

def fullRecordGapValue02077 : Nat := fullRecordGapCenterValue - 286302

theorem fullRecordGapTerm02077_eq_value :
    recordGapCenter - 286302 = fullRecordGapValue02077 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02077_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02077 (fullRecordGapValue02077 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02077_not_prime : ¬(recordGapCenter - 286302).Prime := by
  rw [fullRecordGapTerm02077_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02077, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02077_fast_pow_mod_ne_one

def fullRecordGapValue02078 : Nat := fullRecordGapCenterValue - 286282

theorem fullRecordGapTerm02078_eq_value :
    recordGapCenter - 286282 = fullRecordGapValue02078 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02078_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02078 (fullRecordGapValue02078 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02078_not_prime : ¬(recordGapCenter - 286282).Prime := by
  rw [fullRecordGapTerm02078_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02078, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02078_fast_pow_mod_ne_one

def fullRecordGapValue02079 : Nat := fullRecordGapCenterValue - 286204

theorem fullRecordGapTerm02079_eq_value :
    recordGapCenter - 286204 = fullRecordGapValue02079 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02079_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02079 (fullRecordGapValue02079 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02079_not_prime : ¬(recordGapCenter - 286204).Prime := by
  rw [fullRecordGapTerm02079_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02079, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02079_fast_pow_mod_ne_one

def fullRecordGapValue02080 : Nat := fullRecordGapCenterValue - 286108

theorem fullRecordGapTerm02080_eq_value :
    recordGapCenter - 286108 = fullRecordGapValue02080 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02080_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02080 (fullRecordGapValue02080 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02080_not_prime : ¬(recordGapCenter - 286108).Prime := by
  rw [fullRecordGapTerm02080_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02080, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02080_fast_pow_mod_ne_one

def fullRecordGapValue02081 : Nat := fullRecordGapCenterValue - 285954

theorem fullRecordGapTerm02081_eq_value :
    recordGapCenter - 285954 = fullRecordGapValue02081 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02081_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02081 (fullRecordGapValue02081 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02081_not_prime : ¬(recordGapCenter - 285954).Prime := by
  rw [fullRecordGapTerm02081_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02081, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02081_fast_pow_mod_ne_one

def fullRecordGapValue02082 : Nat := fullRecordGapCenterValue - 285942

theorem fullRecordGapTerm02082_eq_value :
    recordGapCenter - 285942 = fullRecordGapValue02082 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02082_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02082 (fullRecordGapValue02082 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02082_not_prime : ¬(recordGapCenter - 285942).Prime := by
  rw [fullRecordGapTerm02082_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02082, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02082_fast_pow_mod_ne_one

def fullRecordGapValue02083 : Nat := fullRecordGapCenterValue - 285898

theorem fullRecordGapTerm02083_eq_value :
    recordGapCenter - 285898 = fullRecordGapValue02083 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02083_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02083 (fullRecordGapValue02083 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02083_not_prime : ¬(recordGapCenter - 285898).Prime := by
  rw [fullRecordGapTerm02083_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02083, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02083_fast_pow_mod_ne_one

def fullRecordGapValue02084 : Nat := fullRecordGapCenterValue - 285742

theorem fullRecordGapTerm02084_eq_value :
    recordGapCenter - 285742 = fullRecordGapValue02084 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02084_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02084 (fullRecordGapValue02084 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02084_not_prime : ¬(recordGapCenter - 285742).Prime := by
  rw [fullRecordGapTerm02084_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02084, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02084_fast_pow_mod_ne_one

def fullRecordGapValue02085 : Nat := fullRecordGapCenterValue - 285738

theorem fullRecordGapTerm02085_eq_value :
    recordGapCenter - 285738 = fullRecordGapValue02085 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02085_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02085 (fullRecordGapValue02085 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02085_not_prime : ¬(recordGapCenter - 285738).Prime := by
  rw [fullRecordGapTerm02085_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02085, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02085_fast_pow_mod_ne_one

def fullRecordGapValue02086 : Nat := fullRecordGapCenterValue - 285598

theorem fullRecordGapTerm02086_eq_value :
    recordGapCenter - 285598 = fullRecordGapValue02086 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02086_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02086 (fullRecordGapValue02086 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02086_not_prime : ¬(recordGapCenter - 285598).Prime := by
  rw [fullRecordGapTerm02086_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02086, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02086_fast_pow_mod_ne_one

def fullRecordGapValue02087 : Nat := fullRecordGapCenterValue - 285394

theorem fullRecordGapTerm02087_eq_value :
    recordGapCenter - 285394 = fullRecordGapValue02087 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02087_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02087 (fullRecordGapValue02087 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02087_not_prime : ¬(recordGapCenter - 285394).Prime := by
  rw [fullRecordGapTerm02087_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02087, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02087_fast_pow_mod_ne_one

def fullRecordGapValue02088 : Nat := fullRecordGapCenterValue - 285378

theorem fullRecordGapTerm02088_eq_value :
    recordGapCenter - 285378 = fullRecordGapValue02088 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02088_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02088 (fullRecordGapValue02088 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02088_not_prime : ¬(recordGapCenter - 285378).Prime := by
  rw [fullRecordGapTerm02088_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02088, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02088_fast_pow_mod_ne_one

def fullRecordGapValue02089 : Nat := fullRecordGapCenterValue - 285198

theorem fullRecordGapTerm02089_eq_value :
    recordGapCenter - 285198 = fullRecordGapValue02089 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02089_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02089 (fullRecordGapValue02089 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02089_not_prime : ¬(recordGapCenter - 285198).Prime := by
  rw [fullRecordGapTerm02089_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02089, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02089_fast_pow_mod_ne_one

def fullRecordGapValue02090 : Nat := fullRecordGapCenterValue - 285148

theorem fullRecordGapTerm02090_eq_value :
    recordGapCenter - 285148 = fullRecordGapValue02090 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02090_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02090 (fullRecordGapValue02090 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02090_not_prime : ¬(recordGapCenter - 285148).Prime := by
  rw [fullRecordGapTerm02090_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02090, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02090_fast_pow_mod_ne_one

def fullRecordGapValue02091 : Nat := fullRecordGapCenterValue - 285120

theorem fullRecordGapTerm02091_eq_value :
    recordGapCenter - 285120 = fullRecordGapValue02091 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02091_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02091 (fullRecordGapValue02091 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02091_not_prime : ¬(recordGapCenter - 285120).Prime := by
  rw [fullRecordGapTerm02091_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02091, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02091_fast_pow_mod_ne_one

def fullRecordGapValue02092 : Nat := fullRecordGapCenterValue - 285042

theorem fullRecordGapTerm02092_eq_value :
    recordGapCenter - 285042 = fullRecordGapValue02092 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02092_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02092 (fullRecordGapValue02092 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02092_not_prime : ¬(recordGapCenter - 285042).Prime := by
  rw [fullRecordGapTerm02092_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02092, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02092_fast_pow_mod_ne_one

def fullRecordGapValue02093 : Nat := fullRecordGapCenterValue - 284938

theorem fullRecordGapTerm02093_eq_value :
    recordGapCenter - 284938 = fullRecordGapValue02093 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02093_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02093 (fullRecordGapValue02093 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02093_not_prime : ¬(recordGapCenter - 284938).Prime := by
  rw [fullRecordGapTerm02093_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02093, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02093_fast_pow_mod_ne_one

def fullRecordGapValue02094 : Nat := fullRecordGapCenterValue - 284932

theorem fullRecordGapTerm02094_eq_value :
    recordGapCenter - 284932 = fullRecordGapValue02094 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02094_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02094 (fullRecordGapValue02094 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02094_not_prime : ¬(recordGapCenter - 284932).Prime := by
  rw [fullRecordGapTerm02094_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02094, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02094_fast_pow_mod_ne_one

def fullRecordGapValue02095 : Nat := fullRecordGapCenterValue - 284764

theorem fullRecordGapTerm02095_eq_value :
    recordGapCenter - 284764 = fullRecordGapValue02095 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02095_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02095 (fullRecordGapValue02095 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02095_not_prime : ¬(recordGapCenter - 284764).Prime := by
  rw [fullRecordGapTerm02095_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02095, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02095_fast_pow_mod_ne_one

def fullRecordGapValue02096 : Nat := fullRecordGapCenterValue - 284644

theorem fullRecordGapTerm02096_eq_value :
    recordGapCenter - 284644 = fullRecordGapValue02096 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02096_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02096 (fullRecordGapValue02096 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02096_not_prime : ¬(recordGapCenter - 284644).Prime := by
  rw [fullRecordGapTerm02096_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02096, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02096_fast_pow_mod_ne_one

def fullRecordGapValue02097 : Nat := fullRecordGapCenterValue - 284638

theorem fullRecordGapTerm02097_eq_value :
    recordGapCenter - 284638 = fullRecordGapValue02097 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02097_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02097 (fullRecordGapValue02097 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02097_not_prime : ¬(recordGapCenter - 284638).Prime := by
  rw [fullRecordGapTerm02097_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02097, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02097_fast_pow_mod_ne_one

def fullRecordGapValue02098 : Nat := fullRecordGapCenterValue - 284592

theorem fullRecordGapTerm02098_eq_value :
    recordGapCenter - 284592 = fullRecordGapValue02098 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02098_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02098 (fullRecordGapValue02098 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02098_not_prime : ¬(recordGapCenter - 284592).Prime := by
  rw [fullRecordGapTerm02098_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02098, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02098_fast_pow_mod_ne_one

def fullRecordGapValue02099 : Nat := fullRecordGapCenterValue - 284542

theorem fullRecordGapTerm02099_eq_value :
    recordGapCenter - 284542 = fullRecordGapValue02099 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02099_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02099 (fullRecordGapValue02099 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02099_not_prime : ¬(recordGapCenter - 284542).Prime := by
  rw [fullRecordGapTerm02099_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02099, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02099_fast_pow_mod_ne_one

def fullRecordGapValue02100 : Nat := fullRecordGapCenterValue - 284422

theorem fullRecordGapTerm02100_eq_value :
    recordGapCenter - 284422 = fullRecordGapValue02100 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02100_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02100 (fullRecordGapValue02100 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02100_not_prime : ¬(recordGapCenter - 284422).Prime := by
  rw [fullRecordGapTerm02100_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02100, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02100_fast_pow_mod_ne_one

def fullRecordGapValue02101 : Nat := fullRecordGapCenterValue - 284322

theorem fullRecordGapTerm02101_eq_value :
    recordGapCenter - 284322 = fullRecordGapValue02101 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02101_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02101 (fullRecordGapValue02101 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02101_not_prime : ¬(recordGapCenter - 284322).Prime := by
  rw [fullRecordGapTerm02101_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02101, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02101_fast_pow_mod_ne_one

def fullRecordGapValue02102 : Nat := fullRecordGapCenterValue - 284302

theorem fullRecordGapTerm02102_eq_value :
    recordGapCenter - 284302 = fullRecordGapValue02102 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02102_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02102 (fullRecordGapValue02102 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02102_not_prime : ¬(recordGapCenter - 284302).Prime := by
  rw [fullRecordGapTerm02102_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02102, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02102_fast_pow_mod_ne_one

def fullRecordGapValue02103 : Nat := fullRecordGapCenterValue - 284044

theorem fullRecordGapTerm02103_eq_value :
    recordGapCenter - 284044 = fullRecordGapValue02103 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02103_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02103 (fullRecordGapValue02103 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02103_not_prime : ¬(recordGapCenter - 284044).Prime := by
  rw [fullRecordGapTerm02103_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02103, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02103_fast_pow_mod_ne_one

def fullRecordGapValue02104 : Nat := fullRecordGapCenterValue - 284038

theorem fullRecordGapTerm02104_eq_value :
    recordGapCenter - 284038 = fullRecordGapValue02104 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02104_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02104 (fullRecordGapValue02104 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02104_not_prime : ¬(recordGapCenter - 284038).Prime := by
  rw [fullRecordGapTerm02104_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02104, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02104_fast_pow_mod_ne_one

def fullRecordGapValue02105 : Nat := fullRecordGapCenterValue - 283854

theorem fullRecordGapTerm02105_eq_value :
    recordGapCenter - 283854 = fullRecordGapValue02105 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02105_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02105 (fullRecordGapValue02105 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02105_not_prime : ¬(recordGapCenter - 283854).Prime := by
  rw [fullRecordGapTerm02105_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02105, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02105_fast_pow_mod_ne_one

def fullRecordGapValue02106 : Nat := fullRecordGapCenterValue - 283828

theorem fullRecordGapTerm02106_eq_value :
    recordGapCenter - 283828 = fullRecordGapValue02106 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02106_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02106 (fullRecordGapValue02106 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02106_not_prime : ¬(recordGapCenter - 283828).Prime := by
  rw [fullRecordGapTerm02106_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02106, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02106_fast_pow_mod_ne_one

def fullRecordGapValue02107 : Nat := fullRecordGapCenterValue - 283818

theorem fullRecordGapTerm02107_eq_value :
    recordGapCenter - 283818 = fullRecordGapValue02107 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02107_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02107 (fullRecordGapValue02107 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02107_not_prime : ¬(recordGapCenter - 283818).Prime := by
  rw [fullRecordGapTerm02107_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02107, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02107_fast_pow_mod_ne_one

def fullRecordGapValue02108 : Nat := fullRecordGapCenterValue - 283702

theorem fullRecordGapTerm02108_eq_value :
    recordGapCenter - 283702 = fullRecordGapValue02108 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02108_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02108 (fullRecordGapValue02108 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02108_not_prime : ¬(recordGapCenter - 283702).Prime := by
  rw [fullRecordGapTerm02108_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02108, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02108_fast_pow_mod_ne_one

def fullRecordGapValue02109 : Nat := fullRecordGapCenterValue - 283684

theorem fullRecordGapTerm02109_eq_value :
    recordGapCenter - 283684 = fullRecordGapValue02109 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02109_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02109 (fullRecordGapValue02109 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02109_not_prime : ¬(recordGapCenter - 283684).Prime := by
  rw [fullRecordGapTerm02109_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02109, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02109_fast_pow_mod_ne_one

def fullRecordGapValue02110 : Nat := fullRecordGapCenterValue - 283614

theorem fullRecordGapTerm02110_eq_value :
    recordGapCenter - 283614 = fullRecordGapValue02110 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02110_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02110 (fullRecordGapValue02110 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02110_not_prime : ¬(recordGapCenter - 283614).Prime := by
  rw [fullRecordGapTerm02110_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02110, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02110_fast_pow_mod_ne_one

def fullRecordGapValue02111 : Nat := fullRecordGapCenterValue - 283534

theorem fullRecordGapTerm02111_eq_value :
    recordGapCenter - 283534 = fullRecordGapValue02111 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02111_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02111 (fullRecordGapValue02111 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02111_not_prime : ¬(recordGapCenter - 283534).Prime := by
  rw [fullRecordGapTerm02111_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02111, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02111_fast_pow_mod_ne_one

def fullRecordGapValue02112 : Nat := fullRecordGapCenterValue - 283500

theorem fullRecordGapTerm02112_eq_value :
    recordGapCenter - 283500 = fullRecordGapValue02112 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02112_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02112 (fullRecordGapValue02112 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02112_not_prime : ¬(recordGapCenter - 283500).Prime := by
  rw [fullRecordGapTerm02112_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02112, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02112_fast_pow_mod_ne_one

def fullRecordGapValue02113 : Nat := fullRecordGapCenterValue - 283174

theorem fullRecordGapTerm02113_eq_value :
    recordGapCenter - 283174 = fullRecordGapValue02113 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02113_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02113 (fullRecordGapValue02113 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02113_not_prime : ¬(recordGapCenter - 283174).Prime := by
  rw [fullRecordGapTerm02113_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02113, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02113_fast_pow_mod_ne_one

def fullRecordGapValue02114 : Nat := fullRecordGapCenterValue - 283134

theorem fullRecordGapTerm02114_eq_value :
    recordGapCenter - 283134 = fullRecordGapValue02114 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02114_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02114 (fullRecordGapValue02114 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02114_not_prime : ¬(recordGapCenter - 283134).Prime := by
  rw [fullRecordGapTerm02114_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02114, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02114_fast_pow_mod_ne_one

def fullRecordGapValue02115 : Nat := fullRecordGapCenterValue - 282994

theorem fullRecordGapTerm02115_eq_value :
    recordGapCenter - 282994 = fullRecordGapValue02115 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02115_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02115 (fullRecordGapValue02115 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02115_not_prime : ¬(recordGapCenter - 282994).Prime := by
  rw [fullRecordGapTerm02115_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02115, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02115_fast_pow_mod_ne_one

def fullRecordGapValue02116 : Nat := fullRecordGapCenterValue - 282922

theorem fullRecordGapTerm02116_eq_value :
    recordGapCenter - 282922 = fullRecordGapValue02116 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02116_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02116 (fullRecordGapValue02116 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02116_not_prime : ¬(recordGapCenter - 282922).Prime := by
  rw [fullRecordGapTerm02116_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02116, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02116_fast_pow_mod_ne_one

def fullRecordGapValue02117 : Nat := fullRecordGapCenterValue - 282868

theorem fullRecordGapTerm02117_eq_value :
    recordGapCenter - 282868 = fullRecordGapValue02117 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02117_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02117 (fullRecordGapValue02117 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02117_not_prime : ¬(recordGapCenter - 282868).Prime := by
  rw [fullRecordGapTerm02117_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02117, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02117_fast_pow_mod_ne_one

def fullRecordGapValue02118 : Nat := fullRecordGapCenterValue - 282774

theorem fullRecordGapTerm02118_eq_value :
    recordGapCenter - 282774 = fullRecordGapValue02118 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02118_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02118 (fullRecordGapValue02118 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02118_not_prime : ¬(recordGapCenter - 282774).Prime := by
  rw [fullRecordGapTerm02118_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02118, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02118_fast_pow_mod_ne_one

def fullRecordGapValue02119 : Nat := fullRecordGapCenterValue - 282508

theorem fullRecordGapTerm02119_eq_value :
    recordGapCenter - 282508 = fullRecordGapValue02119 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02119_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02119 (fullRecordGapValue02119 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02119_not_prime : ¬(recordGapCenter - 282508).Prime := by
  rw [fullRecordGapTerm02119_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02119, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02119_fast_pow_mod_ne_one

def fullRecordGapValue02120 : Nat := fullRecordGapCenterValue - 282442

theorem fullRecordGapTerm02120_eq_value :
    recordGapCenter - 282442 = fullRecordGapValue02120 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02120_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02120 (fullRecordGapValue02120 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02120_not_prime : ¬(recordGapCenter - 282442).Prime := by
  rw [fullRecordGapTerm02120_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02120, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02120_fast_pow_mod_ne_one

def fullRecordGapValue02121 : Nat := fullRecordGapCenterValue - 282354

theorem fullRecordGapTerm02121_eq_value :
    recordGapCenter - 282354 = fullRecordGapValue02121 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02121_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02121 (fullRecordGapValue02121 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02121_not_prime : ¬(recordGapCenter - 282354).Prime := by
  rw [fullRecordGapTerm02121_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02121, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02121_fast_pow_mod_ne_one

def fullRecordGapValue02122 : Nat := fullRecordGapCenterValue - 282292

theorem fullRecordGapTerm02122_eq_value :
    recordGapCenter - 282292 = fullRecordGapValue02122 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02122_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02122 (fullRecordGapValue02122 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02122_not_prime : ¬(recordGapCenter - 282292).Prime := by
  rw [fullRecordGapTerm02122_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02122, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02122_fast_pow_mod_ne_one

def fullRecordGapValue02123 : Nat := fullRecordGapCenterValue - 282214

theorem fullRecordGapTerm02123_eq_value :
    recordGapCenter - 282214 = fullRecordGapValue02123 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02123_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02123 (fullRecordGapValue02123 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02123_not_prime : ¬(recordGapCenter - 282214).Prime := by
  rw [fullRecordGapTerm02123_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02123, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02123_fast_pow_mod_ne_one

def fullRecordGapValue02124 : Nat := fullRecordGapCenterValue - 282102

theorem fullRecordGapTerm02124_eq_value :
    recordGapCenter - 282102 = fullRecordGapValue02124 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02124_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02124 (fullRecordGapValue02124 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02124_not_prime : ¬(recordGapCenter - 282102).Prime := by
  rw [fullRecordGapTerm02124_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02124, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02124_fast_pow_mod_ne_one

def fullRecordGapValue02125 : Nat := fullRecordGapCenterValue - 281734

theorem fullRecordGapTerm02125_eq_value :
    recordGapCenter - 281734 = fullRecordGapValue02125 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02125_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02125 (fullRecordGapValue02125 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02125_not_prime : ¬(recordGapCenter - 281734).Prime := by
  rw [fullRecordGapTerm02125_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02125, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02125_fast_pow_mod_ne_one

def fullRecordGapValue02126 : Nat := fullRecordGapCenterValue - 281518

theorem fullRecordGapTerm02126_eq_value :
    recordGapCenter - 281518 = fullRecordGapValue02126 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02126_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02126 (fullRecordGapValue02126 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02126_not_prime : ¬(recordGapCenter - 281518).Prime := by
  rw [fullRecordGapTerm02126_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02126, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02126_fast_pow_mod_ne_one

def fullRecordGapValue02127 : Nat := fullRecordGapCenterValue - 281458

theorem fullRecordGapTerm02127_eq_value :
    recordGapCenter - 281458 = fullRecordGapValue02127 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02127_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02127 (fullRecordGapValue02127 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02127_not_prime : ¬(recordGapCenter - 281458).Prime := by
  rw [fullRecordGapTerm02127_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02127, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02127_fast_pow_mod_ne_one

def fullRecordGapValue02128 : Nat := fullRecordGapCenterValue - 281434

theorem fullRecordGapTerm02128_eq_value :
    recordGapCenter - 281434 = fullRecordGapValue02128 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02128_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02128 (fullRecordGapValue02128 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02128_not_prime : ¬(recordGapCenter - 281434).Prime := by
  rw [fullRecordGapTerm02128_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02128, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02128_fast_pow_mod_ne_one

def fullRecordGapValue02129 : Nat := fullRecordGapCenterValue - 281262

theorem fullRecordGapTerm02129_eq_value :
    recordGapCenter - 281262 = fullRecordGapValue02129 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02129_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02129 (fullRecordGapValue02129 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02129_not_prime : ¬(recordGapCenter - 281262).Prime := by
  rw [fullRecordGapTerm02129_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02129, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02129_fast_pow_mod_ne_one

def fullRecordGapValue02130 : Nat := fullRecordGapCenterValue - 280954

theorem fullRecordGapTerm02130_eq_value :
    recordGapCenter - 280954 = fullRecordGapValue02130 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02130_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02130 (fullRecordGapValue02130 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02130_not_prime : ¬(recordGapCenter - 280954).Prime := by
  rw [fullRecordGapTerm02130_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02130, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02130_fast_pow_mod_ne_one

def fullRecordGapValue02131 : Nat := fullRecordGapCenterValue - 280762

theorem fullRecordGapTerm02131_eq_value :
    recordGapCenter - 280762 = fullRecordGapValue02131 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02131_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02131 (fullRecordGapValue02131 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02131_not_prime : ¬(recordGapCenter - 280762).Prime := by
  rw [fullRecordGapTerm02131_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02131, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02131_fast_pow_mod_ne_one

def fullRecordGapValue02132 : Nat := fullRecordGapCenterValue - 280594

theorem fullRecordGapTerm02132_eq_value :
    recordGapCenter - 280594 = fullRecordGapValue02132 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02132_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02132 (fullRecordGapValue02132 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02132_not_prime : ¬(recordGapCenter - 280594).Prime := by
  rw [fullRecordGapTerm02132_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02132, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02132_fast_pow_mod_ne_one

def fullRecordGapValue02133 : Nat := fullRecordGapCenterValue - 280564

theorem fullRecordGapTerm02133_eq_value :
    recordGapCenter - 280564 = fullRecordGapValue02133 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02133_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02133 (fullRecordGapValue02133 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02133_not_prime : ¬(recordGapCenter - 280564).Prime := by
  rw [fullRecordGapTerm02133_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02133, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02133_fast_pow_mod_ne_one

def fullRecordGapValue02134 : Nat := fullRecordGapCenterValue - 280542

theorem fullRecordGapTerm02134_eq_value :
    recordGapCenter - 280542 = fullRecordGapValue02134 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02134_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02134 (fullRecordGapValue02134 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02134_not_prime : ¬(recordGapCenter - 280542).Prime := by
  rw [fullRecordGapTerm02134_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02134, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02134_fast_pow_mod_ne_one

def fullRecordGapValue02135 : Nat := fullRecordGapCenterValue - 280468

theorem fullRecordGapTerm02135_eq_value :
    recordGapCenter - 280468 = fullRecordGapValue02135 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02135_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02135 (fullRecordGapValue02135 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02135_not_prime : ¬(recordGapCenter - 280468).Prime := by
  rw [fullRecordGapTerm02135_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02135, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02135_fast_pow_mod_ne_one

def fullRecordGapValue02136 : Nat := fullRecordGapCenterValue - 280362

theorem fullRecordGapTerm02136_eq_value :
    recordGapCenter - 280362 = fullRecordGapValue02136 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02136_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02136 (fullRecordGapValue02136 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02136_not_prime : ¬(recordGapCenter - 280362).Prime := by
  rw [fullRecordGapTerm02136_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02136, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02136_fast_pow_mod_ne_one

def fullRecordGapValue02137 : Nat := fullRecordGapCenterValue - 280342

theorem fullRecordGapTerm02137_eq_value :
    recordGapCenter - 280342 = fullRecordGapValue02137 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02137_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02137 (fullRecordGapValue02137 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02137_not_prime : ¬(recordGapCenter - 280342).Prime := by
  rw [fullRecordGapTerm02137_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02137, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02137_fast_pow_mod_ne_one

def fullRecordGapValue02138 : Nat := fullRecordGapCenterValue - 280338

theorem fullRecordGapTerm02138_eq_value :
    recordGapCenter - 280338 = fullRecordGapValue02138 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02138_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02138 (fullRecordGapValue02138 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02138_not_prime : ¬(recordGapCenter - 280338).Prime := by
  rw [fullRecordGapTerm02138_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02138, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02138_fast_pow_mod_ne_one

def fullRecordGapValue02139 : Nat := fullRecordGapCenterValue - 280122

theorem fullRecordGapTerm02139_eq_value :
    recordGapCenter - 280122 = fullRecordGapValue02139 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02139_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02139 (fullRecordGapValue02139 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02139_not_prime : ¬(recordGapCenter - 280122).Prime := by
  rw [fullRecordGapTerm02139_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02139, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02139_fast_pow_mod_ne_one

def fullRecordGapValue02140 : Nat := fullRecordGapCenterValue - 280012

theorem fullRecordGapTerm02140_eq_value :
    recordGapCenter - 280012 = fullRecordGapValue02140 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02140_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02140 (fullRecordGapValue02140 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02140_not_prime : ¬(recordGapCenter - 280012).Prime := by
  rw [fullRecordGapTerm02140_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02140, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02140_fast_pow_mod_ne_one

def fullRecordGapValue02141 : Nat := fullRecordGapCenterValue - 279988

theorem fullRecordGapTerm02141_eq_value :
    recordGapCenter - 279988 = fullRecordGapValue02141 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02141_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02141 (fullRecordGapValue02141 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02141_not_prime : ¬(recordGapCenter - 279988).Prime := by
  rw [fullRecordGapTerm02141_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02141, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02141_fast_pow_mod_ne_one

def fullRecordGapValue02142 : Nat := fullRecordGapCenterValue - 279982

theorem fullRecordGapTerm02142_eq_value :
    recordGapCenter - 279982 = fullRecordGapValue02142 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02142_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02142 (fullRecordGapValue02142 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02142_not_prime : ¬(recordGapCenter - 279982).Prime := by
  rw [fullRecordGapTerm02142_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02142, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02142_fast_pow_mod_ne_one

def fullRecordGapValue02143 : Nat := fullRecordGapCenterValue - 279934

theorem fullRecordGapTerm02143_eq_value :
    recordGapCenter - 279934 = fullRecordGapValue02143 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02143_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02143 (fullRecordGapValue02143 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02143_not_prime : ¬(recordGapCenter - 279934).Prime := by
  rw [fullRecordGapTerm02143_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02143, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02143_fast_pow_mod_ne_one

def fullRecordGapValue02144 : Nat := fullRecordGapCenterValue - 279834

theorem fullRecordGapTerm02144_eq_value :
    recordGapCenter - 279834 = fullRecordGapValue02144 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02144_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02144 (fullRecordGapValue02144 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02144_not_prime : ¬(recordGapCenter - 279834).Prime := by
  rw [fullRecordGapTerm02144_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02144, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02144_fast_pow_mod_ne_one

def fullRecordGapValue02145 : Nat := fullRecordGapCenterValue - 279814

theorem fullRecordGapTerm02145_eq_value :
    recordGapCenter - 279814 = fullRecordGapValue02145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02145 (fullRecordGapValue02145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02145_not_prime : ¬(recordGapCenter - 279814).Prime := by
  rw [fullRecordGapTerm02145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02145_fast_pow_mod_ne_one

def fullRecordGapValue02146 : Nat := fullRecordGapCenterValue - 279724

theorem fullRecordGapTerm02146_eq_value :
    recordGapCenter - 279724 = fullRecordGapValue02146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02146 (fullRecordGapValue02146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02146_not_prime : ¬(recordGapCenter - 279724).Prime := by
  rw [fullRecordGapTerm02146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02146_fast_pow_mod_ne_one

def fullRecordGapValue02147 : Nat := fullRecordGapCenterValue - 279534

theorem fullRecordGapTerm02147_eq_value :
    recordGapCenter - 279534 = fullRecordGapValue02147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02147 (fullRecordGapValue02147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02147_not_prime : ¬(recordGapCenter - 279534).Prime := by
  rw [fullRecordGapTerm02147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02147_fast_pow_mod_ne_one

def fullRecordGapValue02148 : Nat := fullRecordGapCenterValue - 279478

theorem fullRecordGapTerm02148_eq_value :
    recordGapCenter - 279478 = fullRecordGapValue02148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02148 (fullRecordGapValue02148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02148_not_prime : ¬(recordGapCenter - 279478).Prime := by
  rw [fullRecordGapTerm02148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02148_fast_pow_mod_ne_one

def fullRecordGapValue02149 : Nat := fullRecordGapCenterValue - 279418

theorem fullRecordGapTerm02149_eq_value :
    recordGapCenter - 279418 = fullRecordGapValue02149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02149 (fullRecordGapValue02149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02149_not_prime : ¬(recordGapCenter - 279418).Prime := by
  rw [fullRecordGapTerm02149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02149_fast_pow_mod_ne_one

def fullRecordGapValue02150 : Nat := fullRecordGapCenterValue - 279402

theorem fullRecordGapTerm02150_eq_value :
    recordGapCenter - 279402 = fullRecordGapValue02150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02150 (fullRecordGapValue02150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02150_not_prime : ¬(recordGapCenter - 279402).Prime := by
  rw [fullRecordGapTerm02150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02150_fast_pow_mod_ne_one

def fullRecordGapValue02151 : Nat := fullRecordGapCenterValue - 279388

theorem fullRecordGapTerm02151_eq_value :
    recordGapCenter - 279388 = fullRecordGapValue02151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02151 (fullRecordGapValue02151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02151_not_prime : ¬(recordGapCenter - 279388).Prime := by
  rw [fullRecordGapTerm02151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02151_fast_pow_mod_ne_one

def fullRecordGapValue02152 : Nat := fullRecordGapCenterValue - 279178

theorem fullRecordGapTerm02152_eq_value :
    recordGapCenter - 279178 = fullRecordGapValue02152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02152 (fullRecordGapValue02152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02152_not_prime : ¬(recordGapCenter - 279178).Prime := by
  rw [fullRecordGapTerm02152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02152_fast_pow_mod_ne_one

def fullRecordGapValue02153 : Nat := fullRecordGapCenterValue - 279142

theorem fullRecordGapTerm02153_eq_value :
    recordGapCenter - 279142 = fullRecordGapValue02153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02153 (fullRecordGapValue02153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02153_not_prime : ¬(recordGapCenter - 279142).Prime := by
  rw [fullRecordGapTerm02153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02153_fast_pow_mod_ne_one

def fullRecordGapValue02154 : Nat := fullRecordGapCenterValue - 278934

theorem fullRecordGapTerm02154_eq_value :
    recordGapCenter - 278934 = fullRecordGapValue02154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02154 (fullRecordGapValue02154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02154_not_prime : ¬(recordGapCenter - 278934).Prime := by
  rw [fullRecordGapTerm02154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02154_fast_pow_mod_ne_one

def fullRecordGapValue02155 : Nat := fullRecordGapCenterValue - 278862

theorem fullRecordGapTerm02155_eq_value :
    recordGapCenter - 278862 = fullRecordGapValue02155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02155 (fullRecordGapValue02155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02155_not_prime : ¬(recordGapCenter - 278862).Prime := by
  rw [fullRecordGapTerm02155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02155_fast_pow_mod_ne_one

def fullRecordGapValue02156 : Nat := fullRecordGapCenterValue - 278742

theorem fullRecordGapTerm02156_eq_value :
    recordGapCenter - 278742 = fullRecordGapValue02156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02156 (fullRecordGapValue02156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02156_not_prime : ¬(recordGapCenter - 278742).Prime := by
  rw [fullRecordGapTerm02156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02156_fast_pow_mod_ne_one

def fullRecordGapValue02157 : Nat := fullRecordGapCenterValue - 278682

theorem fullRecordGapTerm02157_eq_value :
    recordGapCenter - 278682 = fullRecordGapValue02157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02157 (fullRecordGapValue02157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02157_not_prime : ¬(recordGapCenter - 278682).Prime := by
  rw [fullRecordGapTerm02157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02157_fast_pow_mod_ne_one

def fullRecordGapValue02158 : Nat := fullRecordGapCenterValue - 278644

theorem fullRecordGapTerm02158_eq_value :
    recordGapCenter - 278644 = fullRecordGapValue02158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02158 (fullRecordGapValue02158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02158_not_prime : ¬(recordGapCenter - 278644).Prime := by
  rw [fullRecordGapTerm02158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02158_fast_pow_mod_ne_one

def fullRecordGapValue02159 : Nat := fullRecordGapCenterValue - 278602

theorem fullRecordGapTerm02159_eq_value :
    recordGapCenter - 278602 = fullRecordGapValue02159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02159 (fullRecordGapValue02159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02159_not_prime : ¬(recordGapCenter - 278602).Prime := by
  rw [fullRecordGapTerm02159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02159_fast_pow_mod_ne_one

def fullRecordGapValue02160 : Nat := fullRecordGapCenterValue - 278394

theorem fullRecordGapTerm02160_eq_value :
    recordGapCenter - 278394 = fullRecordGapValue02160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02160 (fullRecordGapValue02160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02160_not_prime : ¬(recordGapCenter - 278394).Prime := by
  rw [fullRecordGapTerm02160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02160_fast_pow_mod_ne_one

def fullRecordGapValue02161 : Nat := fullRecordGapCenterValue - 278374

theorem fullRecordGapTerm02161_eq_value :
    recordGapCenter - 278374 = fullRecordGapValue02161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02161 (fullRecordGapValue02161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02161_not_prime : ¬(recordGapCenter - 278374).Prime := by
  rw [fullRecordGapTerm02161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02161_fast_pow_mod_ne_one

def fullRecordGapValue02162 : Nat := fullRecordGapCenterValue - 278338

theorem fullRecordGapTerm02162_eq_value :
    recordGapCenter - 278338 = fullRecordGapValue02162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02162 (fullRecordGapValue02162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02162_not_prime : ¬(recordGapCenter - 278338).Prime := by
  rw [fullRecordGapTerm02162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02162_fast_pow_mod_ne_one

def fullRecordGapValue02163 : Nat := fullRecordGapCenterValue - 278218

theorem fullRecordGapTerm02163_eq_value :
    recordGapCenter - 278218 = fullRecordGapValue02163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02163 (fullRecordGapValue02163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02163_not_prime : ¬(recordGapCenter - 278218).Prime := by
  rw [fullRecordGapTerm02163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02163_fast_pow_mod_ne_one

def fullRecordGapValue02164 : Nat := fullRecordGapCenterValue - 278158

theorem fullRecordGapTerm02164_eq_value :
    recordGapCenter - 278158 = fullRecordGapValue02164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02164 (fullRecordGapValue02164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02164_not_prime : ¬(recordGapCenter - 278158).Prime := by
  rw [fullRecordGapTerm02164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02164_fast_pow_mod_ne_one

def fullRecordGapValue02165 : Nat := fullRecordGapCenterValue - 277954

theorem fullRecordGapTerm02165_eq_value :
    recordGapCenter - 277954 = fullRecordGapValue02165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02165 (fullRecordGapValue02165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02165_not_prime : ¬(recordGapCenter - 277954).Prime := by
  rw [fullRecordGapTerm02165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02165_fast_pow_mod_ne_one

def fullRecordGapValue02166 : Nat := fullRecordGapCenterValue - 277918

theorem fullRecordGapTerm02166_eq_value :
    recordGapCenter - 277918 = fullRecordGapValue02166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02166 (fullRecordGapValue02166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02166_not_prime : ¬(recordGapCenter - 277918).Prime := by
  rw [fullRecordGapTerm02166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02166_fast_pow_mod_ne_one

def fullRecordGapValue02167 : Nat := fullRecordGapCenterValue - 277834

theorem fullRecordGapTerm02167_eq_value :
    recordGapCenter - 277834 = fullRecordGapValue02167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02167 (fullRecordGapValue02167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02167_not_prime : ¬(recordGapCenter - 277834).Prime := by
  rw [fullRecordGapTerm02167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02167_fast_pow_mod_ne_one

def fullRecordGapValue02168 : Nat := fullRecordGapCenterValue - 277828

theorem fullRecordGapTerm02168_eq_value :
    recordGapCenter - 277828 = fullRecordGapValue02168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02168 (fullRecordGapValue02168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02168_not_prime : ¬(recordGapCenter - 277828).Prime := by
  rw [fullRecordGapTerm02168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02168_fast_pow_mod_ne_one

def fullRecordGapValue02169 : Nat := fullRecordGapCenterValue - 277738

theorem fullRecordGapTerm02169_eq_value :
    recordGapCenter - 277738 = fullRecordGapValue02169 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02169_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02169 (fullRecordGapValue02169 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02169_not_prime : ¬(recordGapCenter - 277738).Prime := by
  rw [fullRecordGapTerm02169_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02169, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02169_fast_pow_mod_ne_one

def fullRecordGapValue02170 : Nat := fullRecordGapCenterValue - 277708

theorem fullRecordGapTerm02170_eq_value :
    recordGapCenter - 277708 = fullRecordGapValue02170 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02170_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02170 (fullRecordGapValue02170 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02170_not_prime : ¬(recordGapCenter - 277708).Prime := by
  rw [fullRecordGapTerm02170_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02170, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02170_fast_pow_mod_ne_one

def fullRecordGapValue02171 : Nat := fullRecordGapCenterValue - 277674

theorem fullRecordGapTerm02171_eq_value :
    recordGapCenter - 277674 = fullRecordGapValue02171 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02171_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02171 (fullRecordGapValue02171 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02171_not_prime : ¬(recordGapCenter - 277674).Prime := by
  rw [fullRecordGapTerm02171_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02171, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02171_fast_pow_mod_ne_one

def fullRecordGapValue02172 : Nat := fullRecordGapCenterValue - 277638

theorem fullRecordGapTerm02172_eq_value :
    recordGapCenter - 277638 = fullRecordGapValue02172 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02172_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02172 (fullRecordGapValue02172 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02172_not_prime : ¬(recordGapCenter - 277638).Prime := by
  rw [fullRecordGapTerm02172_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02172, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02172_fast_pow_mod_ne_one

def fullRecordGapValue02173 : Nat := fullRecordGapCenterValue - 277462

theorem fullRecordGapTerm02173_eq_value :
    recordGapCenter - 277462 = fullRecordGapValue02173 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02173_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02173 (fullRecordGapValue02173 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02173_not_prime : ¬(recordGapCenter - 277462).Prime := by
  rw [fullRecordGapTerm02173_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02173, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02173_fast_pow_mod_ne_one

def fullRecordGapValue02174 : Nat := fullRecordGapCenterValue - 277374

theorem fullRecordGapTerm02174_eq_value :
    recordGapCenter - 277374 = fullRecordGapValue02174 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02174_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02174 (fullRecordGapValue02174 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02174_not_prime : ¬(recordGapCenter - 277374).Prime := by
  rw [fullRecordGapTerm02174_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02174, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02174_fast_pow_mod_ne_one

def fullRecordGapValue02175 : Nat := fullRecordGapCenterValue - 277294

theorem fullRecordGapTerm02175_eq_value :
    recordGapCenter - 277294 = fullRecordGapValue02175 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02175_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02175 (fullRecordGapValue02175 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02175_not_prime : ¬(recordGapCenter - 277294).Prime := by
  rw [fullRecordGapTerm02175_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02175, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02175_fast_pow_mod_ne_one

def fullRecordGapValue02176 : Nat := fullRecordGapCenterValue - 277252

theorem fullRecordGapTerm02176_eq_value :
    recordGapCenter - 277252 = fullRecordGapValue02176 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02176_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02176 (fullRecordGapValue02176 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02176_not_prime : ¬(recordGapCenter - 277252).Prime := by
  rw [fullRecordGapTerm02176_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02176, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02176_fast_pow_mod_ne_one

def fullRecordGapValue02177 : Nat := fullRecordGapCenterValue - 277200

theorem fullRecordGapTerm02177_eq_value :
    recordGapCenter - 277200 = fullRecordGapValue02177 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02177_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02177 (fullRecordGapValue02177 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02177_not_prime : ¬(recordGapCenter - 277200).Prime := by
  rw [fullRecordGapTerm02177_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02177, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02177_fast_pow_mod_ne_one

def fullRecordGapValue02178 : Nat := fullRecordGapCenterValue - 277162

theorem fullRecordGapTerm02178_eq_value :
    recordGapCenter - 277162 = fullRecordGapValue02178 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02178_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02178 (fullRecordGapValue02178 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02178_not_prime : ¬(recordGapCenter - 277162).Prime := by
  rw [fullRecordGapTerm02178_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02178, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02178_fast_pow_mod_ne_one

def fullRecordGapValue02179 : Nat := fullRecordGapCenterValue - 277122

theorem fullRecordGapTerm02179_eq_value :
    recordGapCenter - 277122 = fullRecordGapValue02179 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02179_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02179 (fullRecordGapValue02179 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02179_not_prime : ¬(recordGapCenter - 277122).Prime := by
  rw [fullRecordGapTerm02179_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02179, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02179_fast_pow_mod_ne_one

def fullRecordGapValue02180 : Nat := fullRecordGapCenterValue - 276988

theorem fullRecordGapTerm02180_eq_value :
    recordGapCenter - 276988 = fullRecordGapValue02180 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02180_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02180 (fullRecordGapValue02180 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02180_not_prime : ¬(recordGapCenter - 276988).Prime := by
  rw [fullRecordGapTerm02180_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02180, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02180_fast_pow_mod_ne_one

def fullRecordGapValue02181 : Nat := fullRecordGapCenterValue - 276814

theorem fullRecordGapTerm02181_eq_value :
    recordGapCenter - 276814 = fullRecordGapValue02181 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02181_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02181 (fullRecordGapValue02181 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02181_not_prime : ¬(recordGapCenter - 276814).Prime := by
  rw [fullRecordGapTerm02181_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02181, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02181_fast_pow_mod_ne_one

def fullRecordGapValue02182 : Nat := fullRecordGapCenterValue - 276618

theorem fullRecordGapTerm02182_eq_value :
    recordGapCenter - 276618 = fullRecordGapValue02182 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02182_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02182 (fullRecordGapValue02182 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02182_not_prime : ¬(recordGapCenter - 276618).Prime := by
  rw [fullRecordGapTerm02182_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02182, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02182_fast_pow_mod_ne_one

def fullRecordGapValue02183 : Nat := fullRecordGapCenterValue - 276604

theorem fullRecordGapTerm02183_eq_value :
    recordGapCenter - 276604 = fullRecordGapValue02183 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02183_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02183 (fullRecordGapValue02183 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02183_not_prime : ¬(recordGapCenter - 276604).Prime := by
  rw [fullRecordGapTerm02183_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02183, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02183_fast_pow_mod_ne_one

def fullRecordGapValue02184 : Nat := fullRecordGapCenterValue - 276594

theorem fullRecordGapTerm02184_eq_value :
    recordGapCenter - 276594 = fullRecordGapValue02184 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02184_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02184 (fullRecordGapValue02184 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02184_not_prime : ¬(recordGapCenter - 276594).Prime := by
  rw [fullRecordGapTerm02184_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02184, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02184_fast_pow_mod_ne_one

def fullRecordGapValue02185 : Nat := fullRecordGapCenterValue - 276502

theorem fullRecordGapTerm02185_eq_value :
    recordGapCenter - 276502 = fullRecordGapValue02185 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02185_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02185 (fullRecordGapValue02185 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02185_not_prime : ¬(recordGapCenter - 276502).Prime := by
  rw [fullRecordGapTerm02185_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02185, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02185_fast_pow_mod_ne_one

def fullRecordGapValue02186 : Nat := fullRecordGapCenterValue - 276358

theorem fullRecordGapTerm02186_eq_value :
    recordGapCenter - 276358 = fullRecordGapValue02186 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02186_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02186 (fullRecordGapValue02186 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02186_not_prime : ¬(recordGapCenter - 276358).Prime := by
  rw [fullRecordGapTerm02186_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02186, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02186_fast_pow_mod_ne_one

def fullRecordGapValue02187 : Nat := fullRecordGapCenterValue - 276294

theorem fullRecordGapTerm02187_eq_value :
    recordGapCenter - 276294 = fullRecordGapValue02187 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02187_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02187 (fullRecordGapValue02187 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02187_not_prime : ¬(recordGapCenter - 276294).Prime := by
  rw [fullRecordGapTerm02187_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02187, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02187_fast_pow_mod_ne_one

def fullRecordGapValue02188 : Nat := fullRecordGapCenterValue - 276268

theorem fullRecordGapTerm02188_eq_value :
    recordGapCenter - 276268 = fullRecordGapValue02188 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02188_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02188 (fullRecordGapValue02188 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02188_not_prime : ¬(recordGapCenter - 276268).Prime := by
  rw [fullRecordGapTerm02188_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02188, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02188_fast_pow_mod_ne_one

def fullRecordGapValue02189 : Nat := fullRecordGapCenterValue - 276162

theorem fullRecordGapTerm02189_eq_value :
    recordGapCenter - 276162 = fullRecordGapValue02189 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02189_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02189 (fullRecordGapValue02189 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02189_not_prime : ¬(recordGapCenter - 276162).Prime := by
  rw [fullRecordGapTerm02189_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02189, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02189_fast_pow_mod_ne_one

def fullRecordGapValue02190 : Nat := fullRecordGapCenterValue - 276154

theorem fullRecordGapTerm02190_eq_value :
    recordGapCenter - 276154 = fullRecordGapValue02190 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02190_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02190 (fullRecordGapValue02190 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02190_not_prime : ¬(recordGapCenter - 276154).Prime := by
  rw [fullRecordGapTerm02190_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02190, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02190_fast_pow_mod_ne_one

def fullRecordGapValue02191 : Nat := fullRecordGapCenterValue - 276124

theorem fullRecordGapTerm02191_eq_value :
    recordGapCenter - 276124 = fullRecordGapValue02191 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02191_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02191 (fullRecordGapValue02191 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02191_not_prime : ¬(recordGapCenter - 276124).Prime := by
  rw [fullRecordGapTerm02191_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02191, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02191_fast_pow_mod_ne_one

def fullRecordGapValue02192 : Nat := fullRecordGapCenterValue - 275788

theorem fullRecordGapTerm02192_eq_value :
    recordGapCenter - 275788 = fullRecordGapValue02192 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02192_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02192 (fullRecordGapValue02192 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02192_not_prime : ¬(recordGapCenter - 275788).Prime := by
  rw [fullRecordGapTerm02192_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02192, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02192_fast_pow_mod_ne_one

def fullRecordGapValue02193 : Nat := fullRecordGapCenterValue - 275734

theorem fullRecordGapTerm02193_eq_value :
    recordGapCenter - 275734 = fullRecordGapValue02193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02193 (fullRecordGapValue02193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02193_not_prime : ¬(recordGapCenter - 275734).Prime := by
  rw [fullRecordGapTerm02193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02193_fast_pow_mod_ne_one

def fullRecordGapValue02194 : Nat := fullRecordGapCenterValue - 275718

theorem fullRecordGapTerm02194_eq_value :
    recordGapCenter - 275718 = fullRecordGapValue02194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02194 (fullRecordGapValue02194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02194_not_prime : ¬(recordGapCenter - 275718).Prime := by
  rw [fullRecordGapTerm02194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02194_fast_pow_mod_ne_one

def fullRecordGapValue02195 : Nat := fullRecordGapCenterValue - 275694

theorem fullRecordGapTerm02195_eq_value :
    recordGapCenter - 275694 = fullRecordGapValue02195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02195 (fullRecordGapValue02195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02195_not_prime : ¬(recordGapCenter - 275694).Prime := by
  rw [fullRecordGapTerm02195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02195_fast_pow_mod_ne_one

def fullRecordGapValue02196 : Nat := fullRecordGapCenterValue - 275562

theorem fullRecordGapTerm02196_eq_value :
    recordGapCenter - 275562 = fullRecordGapValue02196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02196 (fullRecordGapValue02196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02196_not_prime : ¬(recordGapCenter - 275562).Prime := by
  rw [fullRecordGapTerm02196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02196_fast_pow_mod_ne_one

def fullRecordGapValue02197 : Nat := fullRecordGapCenterValue - 275524

theorem fullRecordGapTerm02197_eq_value :
    recordGapCenter - 275524 = fullRecordGapValue02197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02197 (fullRecordGapValue02197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02197_not_prime : ¬(recordGapCenter - 275524).Prime := by
  rw [fullRecordGapTerm02197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02197_fast_pow_mod_ne_one

def fullRecordGapValue02198 : Nat := fullRecordGapCenterValue - 275214

theorem fullRecordGapTerm02198_eq_value :
    recordGapCenter - 275214 = fullRecordGapValue02198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02198 (fullRecordGapValue02198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02198_not_prime : ¬(recordGapCenter - 275214).Prime := by
  rw [fullRecordGapTerm02198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02198_fast_pow_mod_ne_one

def fullRecordGapValue02199 : Nat := fullRecordGapCenterValue - 275194

theorem fullRecordGapTerm02199_eq_value :
    recordGapCenter - 275194 = fullRecordGapValue02199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02199 (fullRecordGapValue02199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02199_not_prime : ¬(recordGapCenter - 275194).Prime := by
  rw [fullRecordGapTerm02199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02199_fast_pow_mod_ne_one

def fullRecordGapValue02200 : Nat := fullRecordGapCenterValue - 275118

theorem fullRecordGapTerm02200_eq_value :
    recordGapCenter - 275118 = fullRecordGapValue02200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02200 (fullRecordGapValue02200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02200_not_prime : ¬(recordGapCenter - 275118).Prime := by
  rw [fullRecordGapTerm02200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02200_fast_pow_mod_ne_one

def fullRecordGapValue02201 : Nat := fullRecordGapCenterValue - 274972

theorem fullRecordGapTerm02201_eq_value :
    recordGapCenter - 274972 = fullRecordGapValue02201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02201 (fullRecordGapValue02201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02201_not_prime : ¬(recordGapCenter - 274972).Prime := by
  rw [fullRecordGapTerm02201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02201_fast_pow_mod_ne_one

def fullRecordGapValue02202 : Nat := fullRecordGapCenterValue - 274902

theorem fullRecordGapTerm02202_eq_value :
    recordGapCenter - 274902 = fullRecordGapValue02202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02202 (fullRecordGapValue02202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02202_not_prime : ¬(recordGapCenter - 274902).Prime := by
  rw [fullRecordGapTerm02202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02202_fast_pow_mod_ne_one

def fullRecordGapValue02203 : Nat := fullRecordGapCenterValue - 274738

theorem fullRecordGapTerm02203_eq_value :
    recordGapCenter - 274738 = fullRecordGapValue02203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02203 (fullRecordGapValue02203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02203_not_prime : ¬(recordGapCenter - 274738).Prime := by
  rw [fullRecordGapTerm02203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02203_fast_pow_mod_ne_one

def fullRecordGapValue02204 : Nat := fullRecordGapCenterValue - 274732

theorem fullRecordGapTerm02204_eq_value :
    recordGapCenter - 274732 = fullRecordGapValue02204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02204 (fullRecordGapValue02204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02204_not_prime : ¬(recordGapCenter - 274732).Prime := by
  rw [fullRecordGapTerm02204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02204_fast_pow_mod_ne_one

def fullRecordGapValue02205 : Nat := fullRecordGapCenterValue - 274678

theorem fullRecordGapTerm02205_eq_value :
    recordGapCenter - 274678 = fullRecordGapValue02205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02205 (fullRecordGapValue02205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02205_not_prime : ¬(recordGapCenter - 274678).Prime := by
  rw [fullRecordGapTerm02205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02205_fast_pow_mod_ne_one

def fullRecordGapValue02206 : Nat := fullRecordGapCenterValue - 274578

theorem fullRecordGapTerm02206_eq_value :
    recordGapCenter - 274578 = fullRecordGapValue02206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02206 (fullRecordGapValue02206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02206_not_prime : ¬(recordGapCenter - 274578).Prime := by
  rw [fullRecordGapTerm02206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02206_fast_pow_mod_ne_one

def fullRecordGapValue02207 : Nat := fullRecordGapCenterValue - 274558

theorem fullRecordGapTerm02207_eq_value :
    recordGapCenter - 274558 = fullRecordGapValue02207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02207 (fullRecordGapValue02207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02207_not_prime : ¬(recordGapCenter - 274558).Prime := by
  rw [fullRecordGapTerm02207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02207_fast_pow_mod_ne_one

def fullRecordGapValue02208 : Nat := fullRecordGapCenterValue - 274402

theorem fullRecordGapTerm02208_eq_value :
    recordGapCenter - 274402 = fullRecordGapValue02208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02208 (fullRecordGapValue02208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02208_not_prime : ¬(recordGapCenter - 274402).Prime := by
  rw [fullRecordGapTerm02208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02208_fast_pow_mod_ne_one

def fullRecordGapValue02209 : Nat := fullRecordGapCenterValue - 274242

theorem fullRecordGapTerm02209_eq_value :
    recordGapCenter - 274242 = fullRecordGapValue02209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02209 (fullRecordGapValue02209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02209_not_prime : ¬(recordGapCenter - 274242).Prime := by
  rw [fullRecordGapTerm02209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02209_fast_pow_mod_ne_one

def fullRecordGapValue02210 : Nat := fullRecordGapCenterValue - 274084

theorem fullRecordGapTerm02210_eq_value :
    recordGapCenter - 274084 = fullRecordGapValue02210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02210 (fullRecordGapValue02210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02210_not_prime : ¬(recordGapCenter - 274084).Prime := by
  rw [fullRecordGapTerm02210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02210_fast_pow_mod_ne_one

def fullRecordGapValue02211 : Nat := fullRecordGapCenterValue - 273982

theorem fullRecordGapTerm02211_eq_value :
    recordGapCenter - 273982 = fullRecordGapValue02211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02211 (fullRecordGapValue02211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02211_not_prime : ¬(recordGapCenter - 273982).Prime := by
  rw [fullRecordGapTerm02211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02211_fast_pow_mod_ne_one

def fullRecordGapValue02212 : Nat := fullRecordGapCenterValue - 273748

theorem fullRecordGapTerm02212_eq_value :
    recordGapCenter - 273748 = fullRecordGapValue02212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02212 (fullRecordGapValue02212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02212_not_prime : ¬(recordGapCenter - 273748).Prime := by
  rw [fullRecordGapTerm02212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02212_fast_pow_mod_ne_one

def fullRecordGapValue02213 : Nat := fullRecordGapCenterValue - 273682

theorem fullRecordGapTerm02213_eq_value :
    recordGapCenter - 273682 = fullRecordGapValue02213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02213 (fullRecordGapValue02213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02213_not_prime : ¬(recordGapCenter - 273682).Prime := by
  rw [fullRecordGapTerm02213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02213_fast_pow_mod_ne_one

def fullRecordGapValue02214 : Nat := fullRecordGapCenterValue - 273622

theorem fullRecordGapTerm02214_eq_value :
    recordGapCenter - 273622 = fullRecordGapValue02214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02214 (fullRecordGapValue02214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02214_not_prime : ¬(recordGapCenter - 273622).Prime := by
  rw [fullRecordGapTerm02214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02214_fast_pow_mod_ne_one

def fullRecordGapValue02215 : Nat := fullRecordGapCenterValue - 273538

theorem fullRecordGapTerm02215_eq_value :
    recordGapCenter - 273538 = fullRecordGapValue02215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02215 (fullRecordGapValue02215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02215_not_prime : ¬(recordGapCenter - 273538).Prime := by
  rw [fullRecordGapTerm02215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02215_fast_pow_mod_ne_one

def fullRecordGapValue02216 : Nat := fullRecordGapCenterValue - 273534

theorem fullRecordGapTerm02216_eq_value :
    recordGapCenter - 273534 = fullRecordGapValue02216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02216 (fullRecordGapValue02216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02216_not_prime : ¬(recordGapCenter - 273534).Prime := by
  rw [fullRecordGapTerm02216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02216_fast_pow_mod_ne_one

def fullRecordGapValue02217 : Nat := fullRecordGapCenterValue - 273502

theorem fullRecordGapTerm02217_eq_value :
    recordGapCenter - 273502 = fullRecordGapValue02217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02217 (fullRecordGapValue02217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02217_not_prime : ¬(recordGapCenter - 273502).Prime := by
  rw [fullRecordGapTerm02217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02217_fast_pow_mod_ne_one

def fullRecordGapValue02218 : Nat := fullRecordGapCenterValue - 273454

theorem fullRecordGapTerm02218_eq_value :
    recordGapCenter - 273454 = fullRecordGapValue02218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02218 (fullRecordGapValue02218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02218_not_prime : ¬(recordGapCenter - 273454).Prime := by
  rw [fullRecordGapTerm02218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02218_fast_pow_mod_ne_one

def fullRecordGapValue02219 : Nat := fullRecordGapCenterValue - 273318

theorem fullRecordGapTerm02219_eq_value :
    recordGapCenter - 273318 = fullRecordGapValue02219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02219 (fullRecordGapValue02219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02219_not_prime : ¬(recordGapCenter - 273318).Prime := by
  rw [fullRecordGapTerm02219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02219_fast_pow_mod_ne_one

def fullRecordGapValue02220 : Nat := fullRecordGapCenterValue - 273214

theorem fullRecordGapTerm02220_eq_value :
    recordGapCenter - 273214 = fullRecordGapValue02220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02220 (fullRecordGapValue02220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02220_not_prime : ¬(recordGapCenter - 273214).Prime := by
  rw [fullRecordGapTerm02220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02220_fast_pow_mod_ne_one

def fullRecordGapValue02221 : Nat := fullRecordGapCenterValue - 273198

theorem fullRecordGapTerm02221_eq_value :
    recordGapCenter - 273198 = fullRecordGapValue02221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02221 (fullRecordGapValue02221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02221_not_prime : ¬(recordGapCenter - 273198).Prime := by
  rw [fullRecordGapTerm02221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02221_fast_pow_mod_ne_one

def fullRecordGapValue02222 : Nat := fullRecordGapCenterValue - 273018

theorem fullRecordGapTerm02222_eq_value :
    recordGapCenter - 273018 = fullRecordGapValue02222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02222 (fullRecordGapValue02222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02222_not_prime : ¬(recordGapCenter - 273018).Prime := by
  rw [fullRecordGapTerm02222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02222_fast_pow_mod_ne_one

def fullRecordGapValue02223 : Nat := fullRecordGapCenterValue - 272962

theorem fullRecordGapTerm02223_eq_value :
    recordGapCenter - 272962 = fullRecordGapValue02223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02223 (fullRecordGapValue02223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02223_not_prime : ¬(recordGapCenter - 272962).Prime := by
  rw [fullRecordGapTerm02223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02223_fast_pow_mod_ne_one

def fullRecordGapValue02224 : Nat := fullRecordGapCenterValue - 272908

theorem fullRecordGapTerm02224_eq_value :
    recordGapCenter - 272908 = fullRecordGapValue02224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02224 (fullRecordGapValue02224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02224_not_prime : ¬(recordGapCenter - 272908).Prime := by
  rw [fullRecordGapTerm02224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02224_fast_pow_mod_ne_one

def fullRecordGapValue02225 : Nat := fullRecordGapCenterValue - 272638

theorem fullRecordGapTerm02225_eq_value :
    recordGapCenter - 272638 = fullRecordGapValue02225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02225 (fullRecordGapValue02225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02225_not_prime : ¬(recordGapCenter - 272638).Prime := by
  rw [fullRecordGapTerm02225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02225_fast_pow_mod_ne_one

def fullRecordGapValue02226 : Nat := fullRecordGapCenterValue - 272284

theorem fullRecordGapTerm02226_eq_value :
    recordGapCenter - 272284 = fullRecordGapValue02226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02226 (fullRecordGapValue02226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02226_not_prime : ¬(recordGapCenter - 272284).Prime := by
  rw [fullRecordGapTerm02226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02226_fast_pow_mod_ne_one

def fullRecordGapValue02227 : Nat := fullRecordGapCenterValue - 272262

theorem fullRecordGapTerm02227_eq_value :
    recordGapCenter - 272262 = fullRecordGapValue02227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02227 (fullRecordGapValue02227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02227_not_prime : ¬(recordGapCenter - 272262).Prime := by
  rw [fullRecordGapTerm02227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02227_fast_pow_mod_ne_one

def fullRecordGapValue02228 : Nat := fullRecordGapCenterValue - 272212

theorem fullRecordGapTerm02228_eq_value :
    recordGapCenter - 272212 = fullRecordGapValue02228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02228 (fullRecordGapValue02228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02228_not_prime : ¬(recordGapCenter - 272212).Prime := by
  rw [fullRecordGapTerm02228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02228_fast_pow_mod_ne_one

def fullRecordGapValue02229 : Nat := fullRecordGapCenterValue - 272092

theorem fullRecordGapTerm02229_eq_value :
    recordGapCenter - 272092 = fullRecordGapValue02229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02229 (fullRecordGapValue02229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02229_not_prime : ¬(recordGapCenter - 272092).Prime := by
  rw [fullRecordGapTerm02229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02229_fast_pow_mod_ne_one

def fullRecordGapValue02230 : Nat := fullRecordGapCenterValue - 271974

theorem fullRecordGapTerm02230_eq_value :
    recordGapCenter - 271974 = fullRecordGapValue02230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02230 (fullRecordGapValue02230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02230_not_prime : ¬(recordGapCenter - 271974).Prime := by
  rw [fullRecordGapTerm02230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02230_fast_pow_mod_ne_one

def fullRecordGapValue02231 : Nat := fullRecordGapCenterValue - 271954

theorem fullRecordGapTerm02231_eq_value :
    recordGapCenter - 271954 = fullRecordGapValue02231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02231 (fullRecordGapValue02231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02231_not_prime : ¬(recordGapCenter - 271954).Prime := by
  rw [fullRecordGapTerm02231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02231_fast_pow_mod_ne_one

def fullRecordGapValue02232 : Nat := fullRecordGapCenterValue - 271948

theorem fullRecordGapTerm02232_eq_value :
    recordGapCenter - 271948 = fullRecordGapValue02232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02232 (fullRecordGapValue02232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02232_not_prime : ¬(recordGapCenter - 271948).Prime := by
  rw [fullRecordGapTerm02232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02232_fast_pow_mod_ne_one

def fullRecordGapValue02233 : Nat := fullRecordGapCenterValue - 271914

theorem fullRecordGapTerm02233_eq_value :
    recordGapCenter - 271914 = fullRecordGapValue02233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02233 (fullRecordGapValue02233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02233_not_prime : ¬(recordGapCenter - 271914).Prime := by
  rw [fullRecordGapTerm02233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02233_fast_pow_mod_ne_one

def fullRecordGapValue02234 : Nat := fullRecordGapCenterValue - 271842

theorem fullRecordGapTerm02234_eq_value :
    recordGapCenter - 271842 = fullRecordGapValue02234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02234 (fullRecordGapValue02234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02234_not_prime : ¬(recordGapCenter - 271842).Prime := by
  rw [fullRecordGapTerm02234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02234_fast_pow_mod_ne_one

def fullRecordGapValue02235 : Nat := fullRecordGapCenterValue - 271798

theorem fullRecordGapTerm02235_eq_value :
    recordGapCenter - 271798 = fullRecordGapValue02235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02235 (fullRecordGapValue02235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02235_not_prime : ¬(recordGapCenter - 271798).Prime := by
  rw [fullRecordGapTerm02235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02235_fast_pow_mod_ne_one

def fullRecordGapValue02236 : Nat := fullRecordGapCenterValue - 271758

theorem fullRecordGapTerm02236_eq_value :
    recordGapCenter - 271758 = fullRecordGapValue02236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02236 (fullRecordGapValue02236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02236_not_prime : ¬(recordGapCenter - 271758).Prime := by
  rw [fullRecordGapTerm02236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02236_fast_pow_mod_ne_one

def fullRecordGapValue02237 : Nat := fullRecordGapCenterValue - 271732

theorem fullRecordGapTerm02237_eq_value :
    recordGapCenter - 271732 = fullRecordGapValue02237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02237 (fullRecordGapValue02237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02237_not_prime : ¬(recordGapCenter - 271732).Prime := by
  rw [fullRecordGapTerm02237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02237_fast_pow_mod_ne_one

def fullRecordGapValue02238 : Nat := fullRecordGapCenterValue - 271578

theorem fullRecordGapTerm02238_eq_value :
    recordGapCenter - 271578 = fullRecordGapValue02238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02238 (fullRecordGapValue02238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02238_not_prime : ¬(recordGapCenter - 271578).Prime := by
  rw [fullRecordGapTerm02238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02238_fast_pow_mod_ne_one

def fullRecordGapValue02239 : Nat := fullRecordGapCenterValue - 271564

theorem fullRecordGapTerm02239_eq_value :
    recordGapCenter - 271564 = fullRecordGapValue02239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02239 (fullRecordGapValue02239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02239_not_prime : ¬(recordGapCenter - 271564).Prime := by
  rw [fullRecordGapTerm02239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02239_fast_pow_mod_ne_one

def fullRecordGapValue02240 : Nat := fullRecordGapCenterValue - 271554

theorem fullRecordGapTerm02240_eq_value :
    recordGapCenter - 271554 = fullRecordGapValue02240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02240 (fullRecordGapValue02240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02240_not_prime : ¬(recordGapCenter - 271554).Prime := by
  rw [fullRecordGapTerm02240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02240_fast_pow_mod_ne_one

def fullRecordGapValue02241 : Nat := fullRecordGapCenterValue - 271438

theorem fullRecordGapTerm02241_eq_value :
    recordGapCenter - 271438 = fullRecordGapValue02241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02241 (fullRecordGapValue02241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02241_not_prime : ¬(recordGapCenter - 271438).Prime := by
  rw [fullRecordGapTerm02241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02241_fast_pow_mod_ne_one

def fullRecordGapValue02242 : Nat := fullRecordGapCenterValue - 271294

theorem fullRecordGapTerm02242_eq_value :
    recordGapCenter - 271294 = fullRecordGapValue02242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02242 (fullRecordGapValue02242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02242_not_prime : ¬(recordGapCenter - 271294).Prime := by
  rw [fullRecordGapTerm02242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02242_fast_pow_mod_ne_one

def fullRecordGapValue02243 : Nat := fullRecordGapCenterValue - 271204

theorem fullRecordGapTerm02243_eq_value :
    recordGapCenter - 271204 = fullRecordGapValue02243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02243 (fullRecordGapValue02243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02243_not_prime : ¬(recordGapCenter - 271204).Prime := by
  rw [fullRecordGapTerm02243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02243_fast_pow_mod_ne_one

def fullRecordGapValue02244 : Nat := fullRecordGapCenterValue - 271162

theorem fullRecordGapTerm02244_eq_value :
    recordGapCenter - 271162 = fullRecordGapValue02244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02244 (fullRecordGapValue02244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02244_not_prime : ¬(recordGapCenter - 271162).Prime := by
  rw [fullRecordGapTerm02244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02244_fast_pow_mod_ne_one

def fullRecordGapValue02245 : Nat := fullRecordGapCenterValue - 270958

theorem fullRecordGapTerm02245_eq_value :
    recordGapCenter - 270958 = fullRecordGapValue02245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02245 (fullRecordGapValue02245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02245_not_prime : ¬(recordGapCenter - 270958).Prime := by
  rw [fullRecordGapTerm02245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02245_fast_pow_mod_ne_one

def fullRecordGapValue02246 : Nat := fullRecordGapCenterValue - 270898

theorem fullRecordGapTerm02246_eq_value :
    recordGapCenter - 270898 = fullRecordGapValue02246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02246 (fullRecordGapValue02246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02246_not_prime : ¬(recordGapCenter - 270898).Prime := by
  rw [fullRecordGapTerm02246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02246_fast_pow_mod_ne_one

def fullRecordGapValue02247 : Nat := fullRecordGapCenterValue - 270862

theorem fullRecordGapTerm02247_eq_value :
    recordGapCenter - 270862 = fullRecordGapValue02247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02247 (fullRecordGapValue02247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02247_not_prime : ¬(recordGapCenter - 270862).Prime := by
  rw [fullRecordGapTerm02247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02247_fast_pow_mod_ne_one

def fullRecordGapValue02248 : Nat := fullRecordGapCenterValue - 270834

theorem fullRecordGapTerm02248_eq_value :
    recordGapCenter - 270834 = fullRecordGapValue02248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02248 (fullRecordGapValue02248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02248_not_prime : ¬(recordGapCenter - 270834).Prime := by
  rw [fullRecordGapTerm02248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02248_fast_pow_mod_ne_one

def fullRecordGapValue02249 : Nat := fullRecordGapCenterValue - 270822

theorem fullRecordGapTerm02249_eq_value :
    recordGapCenter - 270822 = fullRecordGapValue02249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02249 (fullRecordGapValue02249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02249_not_prime : ¬(recordGapCenter - 270822).Prime := by
  rw [fullRecordGapTerm02249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02249_fast_pow_mod_ne_one

def fullRecordGapValue02250 : Nat := fullRecordGapCenterValue - 270694

theorem fullRecordGapTerm02250_eq_value :
    recordGapCenter - 270694 = fullRecordGapValue02250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02250 (fullRecordGapValue02250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02250_not_prime : ¬(recordGapCenter - 270694).Prime := by
  rw [fullRecordGapTerm02250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02250_fast_pow_mod_ne_one

def fullRecordGapValue02251 : Nat := fullRecordGapCenterValue - 270562

theorem fullRecordGapTerm02251_eq_value :
    recordGapCenter - 270562 = fullRecordGapValue02251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02251 (fullRecordGapValue02251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02251_not_prime : ¬(recordGapCenter - 270562).Prime := by
  rw [fullRecordGapTerm02251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02251_fast_pow_mod_ne_one

def fullRecordGapValue02252 : Nat := fullRecordGapCenterValue - 270462

theorem fullRecordGapTerm02252_eq_value :
    recordGapCenter - 270462 = fullRecordGapValue02252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02252 (fullRecordGapValue02252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02252_not_prime : ¬(recordGapCenter - 270462).Prime := by
  rw [fullRecordGapTerm02252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02252_fast_pow_mod_ne_one

def fullRecordGapValue02253 : Nat := fullRecordGapCenterValue - 270268

theorem fullRecordGapTerm02253_eq_value :
    recordGapCenter - 270268 = fullRecordGapValue02253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02253 (fullRecordGapValue02253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02253_not_prime : ¬(recordGapCenter - 270268).Prime := by
  rw [fullRecordGapTerm02253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02253_fast_pow_mod_ne_one

def fullRecordGapValue02254 : Nat := fullRecordGapCenterValue - 270262

theorem fullRecordGapTerm02254_eq_value :
    recordGapCenter - 270262 = fullRecordGapValue02254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02254 (fullRecordGapValue02254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02254_not_prime : ¬(recordGapCenter - 270262).Prime := by
  rw [fullRecordGapTerm02254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02254_fast_pow_mod_ne_one

def fullRecordGapValue02255 : Nat := fullRecordGapCenterValue - 270238

theorem fullRecordGapTerm02255_eq_value :
    recordGapCenter - 270238 = fullRecordGapValue02255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02255 (fullRecordGapValue02255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02255_not_prime : ¬(recordGapCenter - 270238).Prime := by
  rw [fullRecordGapTerm02255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02255_fast_pow_mod_ne_one

def fullRecordGapValue02256 : Nat := fullRecordGapCenterValue - 270118

theorem fullRecordGapTerm02256_eq_value :
    recordGapCenter - 270118 = fullRecordGapValue02256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02256 (fullRecordGapValue02256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02256_not_prime : ¬(recordGapCenter - 270118).Prime := by
  rw [fullRecordGapTerm02256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02256_fast_pow_mod_ne_one

def fullRecordGapValue02257 : Nat := fullRecordGapCenterValue - 270078

theorem fullRecordGapTerm02257_eq_value :
    recordGapCenter - 270078 = fullRecordGapValue02257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02257 (fullRecordGapValue02257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02257_not_prime : ¬(recordGapCenter - 270078).Prime := by
  rw [fullRecordGapTerm02257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02257_fast_pow_mod_ne_one

def fullRecordGapValue02258 : Nat := fullRecordGapCenterValue - 269842

theorem fullRecordGapTerm02258_eq_value :
    recordGapCenter - 269842 = fullRecordGapValue02258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02258 (fullRecordGapValue02258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02258_not_prime : ¬(recordGapCenter - 269842).Prime := by
  rw [fullRecordGapTerm02258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02258_fast_pow_mod_ne_one

def fullRecordGapValue02259 : Nat := fullRecordGapCenterValue - 269734

theorem fullRecordGapTerm02259_eq_value :
    recordGapCenter - 269734 = fullRecordGapValue02259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02259 (fullRecordGapValue02259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02259_not_prime : ¬(recordGapCenter - 269734).Prime := by
  rw [fullRecordGapTerm02259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02259_fast_pow_mod_ne_one

def fullRecordGapValue02260 : Nat := fullRecordGapCenterValue - 269562

theorem fullRecordGapTerm02260_eq_value :
    recordGapCenter - 269562 = fullRecordGapValue02260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02260 (fullRecordGapValue02260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02260_not_prime : ¬(recordGapCenter - 269562).Prime := by
  rw [fullRecordGapTerm02260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02260_fast_pow_mod_ne_one

def fullRecordGapValue02261 : Nat := fullRecordGapCenterValue - 269554

theorem fullRecordGapTerm02261_eq_value :
    recordGapCenter - 269554 = fullRecordGapValue02261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02261 (fullRecordGapValue02261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02261_not_prime : ¬(recordGapCenter - 269554).Prime := by
  rw [fullRecordGapTerm02261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02261_fast_pow_mod_ne_one

def fullRecordGapValue02262 : Nat := fullRecordGapCenterValue - 269398

theorem fullRecordGapTerm02262_eq_value :
    recordGapCenter - 269398 = fullRecordGapValue02262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02262 (fullRecordGapValue02262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02262_not_prime : ¬(recordGapCenter - 269398).Prime := by
  rw [fullRecordGapTerm02262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02262_fast_pow_mod_ne_one

def fullRecordGapValue02263 : Nat := fullRecordGapCenterValue - 269362

theorem fullRecordGapTerm02263_eq_value :
    recordGapCenter - 269362 = fullRecordGapValue02263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02263 (fullRecordGapValue02263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02263_not_prime : ¬(recordGapCenter - 269362).Prime := by
  rw [fullRecordGapTerm02263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02263_fast_pow_mod_ne_one

def fullRecordGapValue02264 : Nat := fullRecordGapCenterValue - 269358

theorem fullRecordGapTerm02264_eq_value :
    recordGapCenter - 269358 = fullRecordGapValue02264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02264 (fullRecordGapValue02264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02264_not_prime : ¬(recordGapCenter - 269358).Prime := by
  rw [fullRecordGapTerm02264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02264_fast_pow_mod_ne_one

def fullRecordGapValue02265 : Nat := fullRecordGapCenterValue - 269322

theorem fullRecordGapTerm02265_eq_value :
    recordGapCenter - 269322 = fullRecordGapValue02265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02265 (fullRecordGapValue02265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02265_not_prime : ¬(recordGapCenter - 269322).Prime := by
  rw [fullRecordGapTerm02265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02265_fast_pow_mod_ne_one

def fullRecordGapValue02266 : Nat := fullRecordGapCenterValue - 269092

theorem fullRecordGapTerm02266_eq_value :
    recordGapCenter - 269092 = fullRecordGapValue02266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02266 (fullRecordGapValue02266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02266_not_prime : ¬(recordGapCenter - 269092).Prime := by
  rw [fullRecordGapTerm02266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02266_fast_pow_mod_ne_one

def fullRecordGapValue02267 : Nat := fullRecordGapCenterValue - 269058

theorem fullRecordGapTerm02267_eq_value :
    recordGapCenter - 269058 = fullRecordGapValue02267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02267 (fullRecordGapValue02267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02267_not_prime : ¬(recordGapCenter - 269058).Prime := by
  rw [fullRecordGapTerm02267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02267_fast_pow_mod_ne_one

def fullRecordGapValue02268 : Nat := fullRecordGapCenterValue - 269044

theorem fullRecordGapTerm02268_eq_value :
    recordGapCenter - 269044 = fullRecordGapValue02268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02268 (fullRecordGapValue02268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02268_not_prime : ¬(recordGapCenter - 269044).Prime := by
  rw [fullRecordGapTerm02268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02268_fast_pow_mod_ne_one

def fullRecordGapValue02269 : Nat := fullRecordGapCenterValue - 268678

theorem fullRecordGapTerm02269_eq_value :
    recordGapCenter - 268678 = fullRecordGapValue02269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02269 (fullRecordGapValue02269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02269_not_prime : ¬(recordGapCenter - 268678).Prime := by
  rw [fullRecordGapTerm02269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02269_fast_pow_mod_ne_one

def fullRecordGapValue02270 : Nat := fullRecordGapCenterValue - 268638

theorem fullRecordGapTerm02270_eq_value :
    recordGapCenter - 268638 = fullRecordGapValue02270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02270 (fullRecordGapValue02270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02270_not_prime : ¬(recordGapCenter - 268638).Prime := by
  rw [fullRecordGapTerm02270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02270_fast_pow_mod_ne_one

def fullRecordGapValue02271 : Nat := fullRecordGapCenterValue - 268564

theorem fullRecordGapTerm02271_eq_value :
    recordGapCenter - 268564 = fullRecordGapValue02271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02271 (fullRecordGapValue02271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02271_not_prime : ¬(recordGapCenter - 268564).Prime := by
  rw [fullRecordGapTerm02271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02271_fast_pow_mod_ne_one

def fullRecordGapValue02272 : Nat := fullRecordGapCenterValue - 268098

theorem fullRecordGapTerm02272_eq_value :
    recordGapCenter - 268098 = fullRecordGapValue02272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02272 (fullRecordGapValue02272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02272_not_prime : ¬(recordGapCenter - 268098).Prime := by
  rw [fullRecordGapTerm02272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02272_fast_pow_mod_ne_one

def fullRecordGapValue02273 : Nat := fullRecordGapCenterValue - 268084

theorem fullRecordGapTerm02273_eq_value :
    recordGapCenter - 268084 = fullRecordGapValue02273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02273 (fullRecordGapValue02273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02273_not_prime : ¬(recordGapCenter - 268084).Prime := by
  rw [fullRecordGapTerm02273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02273_fast_pow_mod_ne_one

def fullRecordGapValue02274 : Nat := fullRecordGapCenterValue - 268012

theorem fullRecordGapTerm02274_eq_value :
    recordGapCenter - 268012 = fullRecordGapValue02274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02274 (fullRecordGapValue02274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02274_not_prime : ¬(recordGapCenter - 268012).Prime := by
  rw [fullRecordGapTerm02274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02274_fast_pow_mod_ne_one

def fullRecordGapValue02275 : Nat := fullRecordGapCenterValue - 267958

theorem fullRecordGapTerm02275_eq_value :
    recordGapCenter - 267958 = fullRecordGapValue02275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02275 (fullRecordGapValue02275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02275_not_prime : ¬(recordGapCenter - 267958).Prime := by
  rw [fullRecordGapTerm02275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02275_fast_pow_mod_ne_one

def fullRecordGapValue02276 : Nat := fullRecordGapCenterValue - 267892

theorem fullRecordGapTerm02276_eq_value :
    recordGapCenter - 267892 = fullRecordGapValue02276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02276 (fullRecordGapValue02276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02276_not_prime : ¬(recordGapCenter - 267892).Prime := by
  rw [fullRecordGapTerm02276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02276_fast_pow_mod_ne_one

def fullRecordGapValue02277 : Nat := fullRecordGapCenterValue - 267538

theorem fullRecordGapTerm02277_eq_value :
    recordGapCenter - 267538 = fullRecordGapValue02277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02277 (fullRecordGapValue02277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02277_not_prime : ¬(recordGapCenter - 267538).Prime := by
  rw [fullRecordGapTerm02277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02277_fast_pow_mod_ne_one

def fullRecordGapValue02278 : Nat := fullRecordGapCenterValue - 267522

theorem fullRecordGapTerm02278_eq_value :
    recordGapCenter - 267522 = fullRecordGapValue02278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02278 (fullRecordGapValue02278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02278_not_prime : ¬(recordGapCenter - 267522).Prime := by
  rw [fullRecordGapTerm02278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02278_fast_pow_mod_ne_one

def fullRecordGapValue02279 : Nat := fullRecordGapCenterValue - 267474

theorem fullRecordGapTerm02279_eq_value :
    recordGapCenter - 267474 = fullRecordGapValue02279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02279 (fullRecordGapValue02279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02279_not_prime : ¬(recordGapCenter - 267474).Prime := by
  rw [fullRecordGapTerm02279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02279_fast_pow_mod_ne_one

def fullRecordGapValue02280 : Nat := fullRecordGapCenterValue - 267378

theorem fullRecordGapTerm02280_eq_value :
    recordGapCenter - 267378 = fullRecordGapValue02280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02280 (fullRecordGapValue02280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02280_not_prime : ¬(recordGapCenter - 267378).Prime := by
  rw [fullRecordGapTerm02280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02280_fast_pow_mod_ne_one

def fullRecordGapValue02281 : Nat := fullRecordGapCenterValue - 267118

theorem fullRecordGapTerm02281_eq_value :
    recordGapCenter - 267118 = fullRecordGapValue02281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02281 (fullRecordGapValue02281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02281_not_prime : ¬(recordGapCenter - 267118).Prime := by
  rw [fullRecordGapTerm02281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02281_fast_pow_mod_ne_one

def fullRecordGapValue02282 : Nat := fullRecordGapCenterValue - 266998

theorem fullRecordGapTerm02282_eq_value :
    recordGapCenter - 266998 = fullRecordGapValue02282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02282 (fullRecordGapValue02282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02282_not_prime : ¬(recordGapCenter - 266998).Prime := by
  rw [fullRecordGapTerm02282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02282_fast_pow_mod_ne_one

def fullRecordGapValue02283 : Nat := fullRecordGapCenterValue - 266902

theorem fullRecordGapTerm02283_eq_value :
    recordGapCenter - 266902 = fullRecordGapValue02283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02283 (fullRecordGapValue02283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02283_not_prime : ¬(recordGapCenter - 266902).Prime := by
  rw [fullRecordGapTerm02283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02283_fast_pow_mod_ne_one

def fullRecordGapValue02284 : Nat := fullRecordGapCenterValue - 266878

theorem fullRecordGapTerm02284_eq_value :
    recordGapCenter - 266878 = fullRecordGapValue02284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02284 (fullRecordGapValue02284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02284_not_prime : ¬(recordGapCenter - 266878).Prime := by
  rw [fullRecordGapTerm02284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02284_fast_pow_mod_ne_one

def fullRecordGapValue02285 : Nat := fullRecordGapCenterValue - 266782

theorem fullRecordGapTerm02285_eq_value :
    recordGapCenter - 266782 = fullRecordGapValue02285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02285 (fullRecordGapValue02285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02285_not_prime : ¬(recordGapCenter - 266782).Prime := by
  rw [fullRecordGapTerm02285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02285_fast_pow_mod_ne_one

def fullRecordGapValue02286 : Nat := fullRecordGapCenterValue - 266758

theorem fullRecordGapTerm02286_eq_value :
    recordGapCenter - 266758 = fullRecordGapValue02286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02286 (fullRecordGapValue02286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02286_not_prime : ¬(recordGapCenter - 266758).Prime := by
  rw [fullRecordGapTerm02286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02286_fast_pow_mod_ne_one

def fullRecordGapValue02287 : Nat := fullRecordGapCenterValue - 266698

theorem fullRecordGapTerm02287_eq_value :
    recordGapCenter - 266698 = fullRecordGapValue02287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02287 (fullRecordGapValue02287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02287_not_prime : ¬(recordGapCenter - 266698).Prime := by
  rw [fullRecordGapTerm02287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02287_fast_pow_mod_ne_one

def fullRecordGapValue02288 : Nat := fullRecordGapCenterValue - 266404

theorem fullRecordGapTerm02288_eq_value :
    recordGapCenter - 266404 = fullRecordGapValue02288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02288 (fullRecordGapValue02288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02288_not_prime : ¬(recordGapCenter - 266404).Prime := by
  rw [fullRecordGapTerm02288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02288_fast_pow_mod_ne_one

def fullRecordGapValue02289 : Nat := fullRecordGapCenterValue - 266338

theorem fullRecordGapTerm02289_eq_value :
    recordGapCenter - 266338 = fullRecordGapValue02289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02289 (fullRecordGapValue02289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02289_not_prime : ¬(recordGapCenter - 266338).Prime := by
  rw [fullRecordGapTerm02289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02289_fast_pow_mod_ne_one

def fullRecordGapValue02290 : Nat := fullRecordGapCenterValue - 266298

theorem fullRecordGapTerm02290_eq_value :
    recordGapCenter - 266298 = fullRecordGapValue02290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02290 (fullRecordGapValue02290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02290_not_prime : ¬(recordGapCenter - 266298).Prime := by
  rw [fullRecordGapTerm02290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02290_fast_pow_mod_ne_one

def fullRecordGapValue02291 : Nat := fullRecordGapCenterValue - 266242

theorem fullRecordGapTerm02291_eq_value :
    recordGapCenter - 266242 = fullRecordGapValue02291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02291 (fullRecordGapValue02291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02291_not_prime : ¬(recordGapCenter - 266242).Prime := by
  rw [fullRecordGapTerm02291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02291_fast_pow_mod_ne_one

def fullRecordGapValue02292 : Nat := fullRecordGapCenterValue - 266112

theorem fullRecordGapTerm02292_eq_value :
    recordGapCenter - 266112 = fullRecordGapValue02292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02292 (fullRecordGapValue02292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02292_not_prime : ¬(recordGapCenter - 266112).Prime := by
  rw [fullRecordGapTerm02292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02292_fast_pow_mod_ne_one

def fullRecordGapValue02293 : Nat := fullRecordGapCenterValue - 265942

theorem fullRecordGapTerm02293_eq_value :
    recordGapCenter - 265942 = fullRecordGapValue02293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02293 (fullRecordGapValue02293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02293_not_prime : ¬(recordGapCenter - 265942).Prime := by
  rw [fullRecordGapTerm02293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02293_fast_pow_mod_ne_one

def fullRecordGapValue02294 : Nat := fullRecordGapCenterValue - 265858

theorem fullRecordGapTerm02294_eq_value :
    recordGapCenter - 265858 = fullRecordGapValue02294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02294 (fullRecordGapValue02294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02294_not_prime : ¬(recordGapCenter - 265858).Prime := by
  rw [fullRecordGapTerm02294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02294_fast_pow_mod_ne_one

def fullRecordGapValue02295 : Nat := fullRecordGapCenterValue - 265828

theorem fullRecordGapTerm02295_eq_value :
    recordGapCenter - 265828 = fullRecordGapValue02295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02295 (fullRecordGapValue02295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02295_not_prime : ¬(recordGapCenter - 265828).Prime := by
  rw [fullRecordGapTerm02295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02295_fast_pow_mod_ne_one

def fullRecordGapValue02296 : Nat := fullRecordGapCenterValue - 265822

theorem fullRecordGapTerm02296_eq_value :
    recordGapCenter - 265822 = fullRecordGapValue02296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02296 (fullRecordGapValue02296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02296_not_prime : ¬(recordGapCenter - 265822).Prime := by
  rw [fullRecordGapTerm02296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02296_fast_pow_mod_ne_one

def fullRecordGapValue02297 : Nat := fullRecordGapCenterValue - 265758

theorem fullRecordGapTerm02297_eq_value :
    recordGapCenter - 265758 = fullRecordGapValue02297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02297 (fullRecordGapValue02297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02297_not_prime : ¬(recordGapCenter - 265758).Prime := by
  rw [fullRecordGapTerm02297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02297_fast_pow_mod_ne_one

def fullRecordGapValue02298 : Nat := fullRecordGapCenterValue - 265674

theorem fullRecordGapTerm02298_eq_value :
    recordGapCenter - 265674 = fullRecordGapValue02298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02298 (fullRecordGapValue02298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02298_not_prime : ¬(recordGapCenter - 265674).Prime := by
  rw [fullRecordGapTerm02298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02298_fast_pow_mod_ne_one

def fullRecordGapValue02299 : Nat := fullRecordGapCenterValue - 265614

theorem fullRecordGapTerm02299_eq_value :
    recordGapCenter - 265614 = fullRecordGapValue02299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02299 (fullRecordGapValue02299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02299_not_prime : ¬(recordGapCenter - 265614).Prime := by
  rw [fullRecordGapTerm02299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02299_fast_pow_mod_ne_one

def fullRecordGapValue02300 : Nat := fullRecordGapCenterValue - 265612

theorem fullRecordGapTerm02300_eq_value :
    recordGapCenter - 265612 = fullRecordGapValue02300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02300 (fullRecordGapValue02300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02300_not_prime : ¬(recordGapCenter - 265612).Prime := by
  rw [fullRecordGapTerm02300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02300_fast_pow_mod_ne_one

def fullRecordGapValue02301 : Nat := fullRecordGapCenterValue - 265578

theorem fullRecordGapTerm02301_eq_value :
    recordGapCenter - 265578 = fullRecordGapValue02301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02301 (fullRecordGapValue02301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02301_not_prime : ¬(recordGapCenter - 265578).Prime := by
  rw [fullRecordGapTerm02301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02301_fast_pow_mod_ne_one

def fullRecordGapValue02302 : Nat := fullRecordGapCenterValue - 265498

theorem fullRecordGapTerm02302_eq_value :
    recordGapCenter - 265498 = fullRecordGapValue02302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02302 (fullRecordGapValue02302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02302_not_prime : ¬(recordGapCenter - 265498).Prime := by
  rw [fullRecordGapTerm02302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02302_fast_pow_mod_ne_one

def fullRecordGapValue02303 : Nat := fullRecordGapCenterValue - 265372

theorem fullRecordGapTerm02303_eq_value :
    recordGapCenter - 265372 = fullRecordGapValue02303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02303 (fullRecordGapValue02303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02303_not_prime : ¬(recordGapCenter - 265372).Prime := by
  rw [fullRecordGapTerm02303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02303_fast_pow_mod_ne_one

def fullRecordGapValue02304 : Nat := fullRecordGapCenterValue - 265348

theorem fullRecordGapTerm02304_eq_value :
    recordGapCenter - 265348 = fullRecordGapValue02304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02304 (fullRecordGapValue02304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02304_not_prime : ¬(recordGapCenter - 265348).Prime := by
  rw [fullRecordGapTerm02304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02304_fast_pow_mod_ne_one

end PrimeFactorUnimodality
