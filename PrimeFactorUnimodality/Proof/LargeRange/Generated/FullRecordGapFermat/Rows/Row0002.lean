import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue00257 : Nat := fullRecordGapCenterValue - 435600

theorem fullRecordGapTerm00257_eq_value :
    recordGapCenter - 435600 = fullRecordGapValue00257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00257 (fullRecordGapValue00257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00257_not_prime : ¬(recordGapCenter - 435600).Prime := by
  rw [fullRecordGapTerm00257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00257_fast_pow_mod_ne_one

def fullRecordGapValue00258 : Nat := fullRecordGapCenterValue - 435354

theorem fullRecordGapTerm00258_eq_value :
    recordGapCenter - 435354 = fullRecordGapValue00258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00258 (fullRecordGapValue00258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00258_not_prime : ¬(recordGapCenter - 435354).Prime := by
  rw [fullRecordGapTerm00258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00258_fast_pow_mod_ne_one

def fullRecordGapValue00259 : Nat := fullRecordGapCenterValue - 435322

theorem fullRecordGapTerm00259_eq_value :
    recordGapCenter - 435322 = fullRecordGapValue00259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00259 (fullRecordGapValue00259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00259_not_prime : ¬(recordGapCenter - 435322).Prime := by
  rw [fullRecordGapTerm00259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00259_fast_pow_mod_ne_one

def fullRecordGapValue00260 : Nat := fullRecordGapCenterValue - 435304

theorem fullRecordGapTerm00260_eq_value :
    recordGapCenter - 435304 = fullRecordGapValue00260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00260 (fullRecordGapValue00260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00260_not_prime : ¬(recordGapCenter - 435304).Prime := by
  rw [fullRecordGapTerm00260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00260_fast_pow_mod_ne_one

def fullRecordGapValue00261 : Nat := fullRecordGapCenterValue - 435154

theorem fullRecordGapTerm00261_eq_value :
    recordGapCenter - 435154 = fullRecordGapValue00261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00261 (fullRecordGapValue00261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00261_not_prime : ¬(recordGapCenter - 435154).Prime := by
  rw [fullRecordGapTerm00261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00261_fast_pow_mod_ne_one

def fullRecordGapValue00262 : Nat := fullRecordGapCenterValue - 435118

theorem fullRecordGapTerm00262_eq_value :
    recordGapCenter - 435118 = fullRecordGapValue00262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00262 (fullRecordGapValue00262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00262_not_prime : ¬(recordGapCenter - 435118).Prime := by
  rw [fullRecordGapTerm00262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00262_fast_pow_mod_ne_one

def fullRecordGapValue00263 : Nat := fullRecordGapCenterValue - 434998

theorem fullRecordGapTerm00263_eq_value :
    recordGapCenter - 434998 = fullRecordGapValue00263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00263 (fullRecordGapValue00263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00263_not_prime : ¬(recordGapCenter - 434998).Prime := by
  rw [fullRecordGapTerm00263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00263_fast_pow_mod_ne_one

def fullRecordGapValue00264 : Nat := fullRecordGapCenterValue - 434982

theorem fullRecordGapTerm00264_eq_value :
    recordGapCenter - 434982 = fullRecordGapValue00264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00264 (fullRecordGapValue00264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00264_not_prime : ¬(recordGapCenter - 434982).Prime := by
  rw [fullRecordGapTerm00264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00264_fast_pow_mod_ne_one

def fullRecordGapValue00265 : Nat := fullRecordGapCenterValue - 434958

theorem fullRecordGapTerm00265_eq_value :
    recordGapCenter - 434958 = fullRecordGapValue00265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00265 (fullRecordGapValue00265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00265_not_prime : ¬(recordGapCenter - 434958).Prime := by
  rw [fullRecordGapTerm00265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00265_fast_pow_mod_ne_one

def fullRecordGapValue00266 : Nat := fullRecordGapCenterValue - 434914

theorem fullRecordGapTerm00266_eq_value :
    recordGapCenter - 434914 = fullRecordGapValue00266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00266 (fullRecordGapValue00266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00266_not_prime : ¬(recordGapCenter - 434914).Prime := by
  rw [fullRecordGapTerm00266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00266_fast_pow_mod_ne_one

def fullRecordGapValue00267 : Nat := fullRecordGapCenterValue - 434802

theorem fullRecordGapTerm00267_eq_value :
    recordGapCenter - 434802 = fullRecordGapValue00267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00267 (fullRecordGapValue00267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00267_not_prime : ¬(recordGapCenter - 434802).Prime := by
  rw [fullRecordGapTerm00267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00267_fast_pow_mod_ne_one

def fullRecordGapValue00268 : Nat := fullRecordGapCenterValue - 434734

theorem fullRecordGapTerm00268_eq_value :
    recordGapCenter - 434734 = fullRecordGapValue00268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00268 (fullRecordGapValue00268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00268_not_prime : ¬(recordGapCenter - 434734).Prime := by
  rw [fullRecordGapTerm00268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00268_fast_pow_mod_ne_one

def fullRecordGapValue00269 : Nat := fullRecordGapCenterValue - 434572

theorem fullRecordGapTerm00269_eq_value :
    recordGapCenter - 434572 = fullRecordGapValue00269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00269 (fullRecordGapValue00269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00269_not_prime : ¬(recordGapCenter - 434572).Prime := by
  rw [fullRecordGapTerm00269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00269_fast_pow_mod_ne_one

def fullRecordGapValue00270 : Nat := fullRecordGapCenterValue - 434524

theorem fullRecordGapTerm00270_eq_value :
    recordGapCenter - 434524 = fullRecordGapValue00270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00270 (fullRecordGapValue00270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00270_not_prime : ¬(recordGapCenter - 434524).Prime := by
  rw [fullRecordGapTerm00270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00270_fast_pow_mod_ne_one

def fullRecordGapValue00271 : Nat := fullRecordGapCenterValue - 434458

theorem fullRecordGapTerm00271_eq_value :
    recordGapCenter - 434458 = fullRecordGapValue00271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00271 (fullRecordGapValue00271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00271_not_prime : ¬(recordGapCenter - 434458).Prime := by
  rw [fullRecordGapTerm00271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00271_fast_pow_mod_ne_one

def fullRecordGapValue00272 : Nat := fullRecordGapCenterValue - 434410

theorem fullRecordGapTerm00272_eq_value :
    recordGapCenter - 434410 = fullRecordGapValue00272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00272 (fullRecordGapValue00272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00272_not_prime : ¬(recordGapCenter - 434410).Prime := by
  rw [fullRecordGapTerm00272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00272_fast_pow_mod_ne_one

def fullRecordGapValue00273 : Nat := fullRecordGapCenterValue - 434338

theorem fullRecordGapTerm00273_eq_value :
    recordGapCenter - 434338 = fullRecordGapValue00273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00273 (fullRecordGapValue00273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00273_not_prime : ¬(recordGapCenter - 434338).Prime := by
  rw [fullRecordGapTerm00273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00273_fast_pow_mod_ne_one

def fullRecordGapValue00274 : Nat := fullRecordGapCenterValue - 434314

theorem fullRecordGapTerm00274_eq_value :
    recordGapCenter - 434314 = fullRecordGapValue00274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00274 (fullRecordGapValue00274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00274_not_prime : ¬(recordGapCenter - 434314).Prime := by
  rw [fullRecordGapTerm00274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00274_fast_pow_mod_ne_one

def fullRecordGapValue00275 : Nat := fullRecordGapCenterValue - 434298

theorem fullRecordGapTerm00275_eq_value :
    recordGapCenter - 434298 = fullRecordGapValue00275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00275 (fullRecordGapValue00275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00275_not_prime : ¬(recordGapCenter - 434298).Prime := by
  rw [fullRecordGapTerm00275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00275_fast_pow_mod_ne_one

def fullRecordGapValue00276 : Nat := fullRecordGapCenterValue - 434242

theorem fullRecordGapTerm00276_eq_value :
    recordGapCenter - 434242 = fullRecordGapValue00276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00276 (fullRecordGapValue00276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00276_not_prime : ¬(recordGapCenter - 434242).Prime := by
  rw [fullRecordGapTerm00276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00276_fast_pow_mod_ne_one

def fullRecordGapValue00277 : Nat := fullRecordGapCenterValue - 434202

theorem fullRecordGapTerm00277_eq_value :
    recordGapCenter - 434202 = fullRecordGapValue00277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00277 (fullRecordGapValue00277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00277_not_prime : ¬(recordGapCenter - 434202).Prime := by
  rw [fullRecordGapTerm00277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00277_fast_pow_mod_ne_one

def fullRecordGapValue00278 : Nat := fullRecordGapCenterValue - 434164

theorem fullRecordGapTerm00278_eq_value :
    recordGapCenter - 434164 = fullRecordGapValue00278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00278 (fullRecordGapValue00278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00278_not_prime : ¬(recordGapCenter - 434164).Prime := by
  rw [fullRecordGapTerm00278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00278_fast_pow_mod_ne_one

def fullRecordGapValue00279 : Nat := fullRecordGapCenterValue - 434002

theorem fullRecordGapTerm00279_eq_value :
    recordGapCenter - 434002 = fullRecordGapValue00279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00279 (fullRecordGapValue00279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00279_not_prime : ¬(recordGapCenter - 434002).Prime := by
  rw [fullRecordGapTerm00279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00279_fast_pow_mod_ne_one

def fullRecordGapValue00280 : Nat := fullRecordGapCenterValue - 433990

theorem fullRecordGapTerm00280_eq_value :
    recordGapCenter - 433990 = fullRecordGapValue00280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00280 (fullRecordGapValue00280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00280_not_prime : ¬(recordGapCenter - 433990).Prime := by
  rw [fullRecordGapTerm00280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00280_fast_pow_mod_ne_one

def fullRecordGapValue00281 : Nat := fullRecordGapCenterValue - 433894

theorem fullRecordGapTerm00281_eq_value :
    recordGapCenter - 433894 = fullRecordGapValue00281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00281 (fullRecordGapValue00281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00281_not_prime : ¬(recordGapCenter - 433894).Prime := by
  rw [fullRecordGapTerm00281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00281_fast_pow_mod_ne_one

def fullRecordGapValue00282 : Nat := fullRecordGapCenterValue - 433878

theorem fullRecordGapTerm00282_eq_value :
    recordGapCenter - 433878 = fullRecordGapValue00282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00282 (fullRecordGapValue00282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00282_not_prime : ¬(recordGapCenter - 433878).Prime := by
  rw [fullRecordGapTerm00282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00282_fast_pow_mod_ne_one

def fullRecordGapValue00283 : Nat := fullRecordGapCenterValue - 433702

theorem fullRecordGapTerm00283_eq_value :
    recordGapCenter - 433702 = fullRecordGapValue00283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00283 (fullRecordGapValue00283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00283_not_prime : ¬(recordGapCenter - 433702).Prime := by
  rw [fullRecordGapTerm00283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00283_fast_pow_mod_ne_one

def fullRecordGapValue00284 : Nat := fullRecordGapCenterValue - 433684

theorem fullRecordGapTerm00284_eq_value :
    recordGapCenter - 433684 = fullRecordGapValue00284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00284 (fullRecordGapValue00284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00284_not_prime : ¬(recordGapCenter - 433684).Prime := by
  rw [fullRecordGapTerm00284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00284_fast_pow_mod_ne_one

def fullRecordGapValue00285 : Nat := fullRecordGapCenterValue - 433614

theorem fullRecordGapTerm00285_eq_value :
    recordGapCenter - 433614 = fullRecordGapValue00285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00285 (fullRecordGapValue00285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00285_not_prime : ¬(recordGapCenter - 433614).Prime := by
  rw [fullRecordGapTerm00285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00285_fast_pow_mod_ne_one

def fullRecordGapValue00286 : Nat := fullRecordGapCenterValue - 433372

theorem fullRecordGapTerm00286_eq_value :
    recordGapCenter - 433372 = fullRecordGapValue00286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00286 (fullRecordGapValue00286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00286_not_prime : ¬(recordGapCenter - 433372).Prime := by
  rw [fullRecordGapTerm00286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00286_fast_pow_mod_ne_one

def fullRecordGapValue00287 : Nat := fullRecordGapCenterValue - 433282

theorem fullRecordGapTerm00287_eq_value :
    recordGapCenter - 433282 = fullRecordGapValue00287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00287 (fullRecordGapValue00287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00287_not_prime : ¬(recordGapCenter - 433282).Prime := by
  rw [fullRecordGapTerm00287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00287_fast_pow_mod_ne_one

def fullRecordGapValue00288 : Nat := fullRecordGapCenterValue - 433138

theorem fullRecordGapTerm00288_eq_value :
    recordGapCenter - 433138 = fullRecordGapValue00288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00288 (fullRecordGapValue00288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00288_not_prime : ¬(recordGapCenter - 433138).Prime := by
  rw [fullRecordGapTerm00288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00288_fast_pow_mod_ne_one

def fullRecordGapValue00289 : Nat := fullRecordGapCenterValue - 433018

theorem fullRecordGapTerm00289_eq_value :
    recordGapCenter - 433018 = fullRecordGapValue00289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00289 (fullRecordGapValue00289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00289_not_prime : ¬(recordGapCenter - 433018).Prime := by
  rw [fullRecordGapTerm00289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00289_fast_pow_mod_ne_one

def fullRecordGapValue00290 : Nat := fullRecordGapCenterValue - 433002

theorem fullRecordGapTerm00290_eq_value :
    recordGapCenter - 433002 = fullRecordGapValue00290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00290 (fullRecordGapValue00290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00290_not_prime : ¬(recordGapCenter - 433002).Prime := by
  rw [fullRecordGapTerm00290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00290_fast_pow_mod_ne_one

def fullRecordGapValue00291 : Nat := fullRecordGapCenterValue - 432988

theorem fullRecordGapTerm00291_eq_value :
    recordGapCenter - 432988 = fullRecordGapValue00291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00291 (fullRecordGapValue00291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00291_not_prime : ¬(recordGapCenter - 432988).Prime := by
  rw [fullRecordGapTerm00291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00291_fast_pow_mod_ne_one

def fullRecordGapValue00292 : Nat := fullRecordGapCenterValue - 432910

theorem fullRecordGapTerm00292_eq_value :
    recordGapCenter - 432910 = fullRecordGapValue00292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00292 (fullRecordGapValue00292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00292_not_prime : ¬(recordGapCenter - 432910).Prime := by
  rw [fullRecordGapTerm00292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00292_fast_pow_mod_ne_one

def fullRecordGapValue00293 : Nat := fullRecordGapCenterValue - 432868

theorem fullRecordGapTerm00293_eq_value :
    recordGapCenter - 432868 = fullRecordGapValue00293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00293 (fullRecordGapValue00293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00293_not_prime : ¬(recordGapCenter - 432868).Prime := by
  rw [fullRecordGapTerm00293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00293_fast_pow_mod_ne_one

def fullRecordGapValue00294 : Nat := fullRecordGapCenterValue - 432862

theorem fullRecordGapTerm00294_eq_value :
    recordGapCenter - 432862 = fullRecordGapValue00294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00294 (fullRecordGapValue00294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00294_not_prime : ¬(recordGapCenter - 432862).Prime := by
  rw [fullRecordGapTerm00294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00294_fast_pow_mod_ne_one

def fullRecordGapValue00295 : Nat := fullRecordGapCenterValue - 432844

theorem fullRecordGapTerm00295_eq_value :
    recordGapCenter - 432844 = fullRecordGapValue00295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00295 (fullRecordGapValue00295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00295_not_prime : ¬(recordGapCenter - 432844).Prime := by
  rw [fullRecordGapTerm00295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00295_fast_pow_mod_ne_one

def fullRecordGapValue00296 : Nat := fullRecordGapCenterValue - 432802

theorem fullRecordGapTerm00296_eq_value :
    recordGapCenter - 432802 = fullRecordGapValue00296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00296 (fullRecordGapValue00296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00296_not_prime : ¬(recordGapCenter - 432802).Prime := by
  rw [fullRecordGapTerm00296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00296_fast_pow_mod_ne_one

def fullRecordGapValue00297 : Nat := fullRecordGapCenterValue - 432742

theorem fullRecordGapTerm00297_eq_value :
    recordGapCenter - 432742 = fullRecordGapValue00297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00297 (fullRecordGapValue00297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00297_not_prime : ¬(recordGapCenter - 432742).Prime := by
  rw [fullRecordGapTerm00297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00297_fast_pow_mod_ne_one

def fullRecordGapValue00298 : Nat := fullRecordGapCenterValue - 432472

theorem fullRecordGapTerm00298_eq_value :
    recordGapCenter - 432472 = fullRecordGapValue00298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00298 (fullRecordGapValue00298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00298_not_prime : ¬(recordGapCenter - 432472).Prime := by
  rw [fullRecordGapTerm00298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00298_fast_pow_mod_ne_one

def fullRecordGapValue00299 : Nat := fullRecordGapCenterValue - 432462

theorem fullRecordGapTerm00299_eq_value :
    recordGapCenter - 432462 = fullRecordGapValue00299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00299 (fullRecordGapValue00299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00299_not_prime : ¬(recordGapCenter - 432462).Prime := by
  rw [fullRecordGapTerm00299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00299_fast_pow_mod_ne_one

def fullRecordGapValue00300 : Nat := fullRecordGapCenterValue - 432358

theorem fullRecordGapTerm00300_eq_value :
    recordGapCenter - 432358 = fullRecordGapValue00300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00300 (fullRecordGapValue00300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00300_not_prime : ¬(recordGapCenter - 432358).Prime := by
  rw [fullRecordGapTerm00300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00300_fast_pow_mod_ne_one

def fullRecordGapValue00301 : Nat := fullRecordGapCenterValue - 432318

theorem fullRecordGapTerm00301_eq_value :
    recordGapCenter - 432318 = fullRecordGapValue00301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00301 (fullRecordGapValue00301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00301_not_prime : ¬(recordGapCenter - 432318).Prime := by
  rw [fullRecordGapTerm00301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00301_fast_pow_mod_ne_one

def fullRecordGapValue00302 : Nat := fullRecordGapCenterValue - 432070

theorem fullRecordGapTerm00302_eq_value :
    recordGapCenter - 432070 = fullRecordGapValue00302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00302 (fullRecordGapValue00302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00302_not_prime : ¬(recordGapCenter - 432070).Prime := by
  rw [fullRecordGapTerm00302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00302_fast_pow_mod_ne_one

def fullRecordGapValue00303 : Nat := fullRecordGapCenterValue - 432010

theorem fullRecordGapTerm00303_eq_value :
    recordGapCenter - 432010 = fullRecordGapValue00303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00303 (fullRecordGapValue00303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00303_not_prime : ¬(recordGapCenter - 432010).Prime := by
  rw [fullRecordGapTerm00303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00303_fast_pow_mod_ne_one

def fullRecordGapValue00304 : Nat := fullRecordGapCenterValue - 432000

theorem fullRecordGapTerm00304_eq_value :
    recordGapCenter - 432000 = fullRecordGapValue00304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00304 (fullRecordGapValue00304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00304_not_prime : ¬(recordGapCenter - 432000).Prime := by
  rw [fullRecordGapTerm00304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00304_fast_pow_mod_ne_one

def fullRecordGapValue00305 : Nat := fullRecordGapCenterValue - 431962

theorem fullRecordGapTerm00305_eq_value :
    recordGapCenter - 431962 = fullRecordGapValue00305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00305 (fullRecordGapValue00305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00305_not_prime : ¬(recordGapCenter - 431962).Prime := by
  rw [fullRecordGapTerm00305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00305_fast_pow_mod_ne_one

def fullRecordGapValue00306 : Nat := fullRecordGapCenterValue - 431944

theorem fullRecordGapTerm00306_eq_value :
    recordGapCenter - 431944 = fullRecordGapValue00306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00306 (fullRecordGapValue00306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00306_not_prime : ¬(recordGapCenter - 431944).Prime := by
  rw [fullRecordGapTerm00306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00306_fast_pow_mod_ne_one

def fullRecordGapValue00307 : Nat := fullRecordGapCenterValue - 431898

theorem fullRecordGapTerm00307_eq_value :
    recordGapCenter - 431898 = fullRecordGapValue00307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00307 (fullRecordGapValue00307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00307_not_prime : ¬(recordGapCenter - 431898).Prime := by
  rw [fullRecordGapTerm00307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00307_fast_pow_mod_ne_one

def fullRecordGapValue00308 : Nat := fullRecordGapCenterValue - 431890

theorem fullRecordGapTerm00308_eq_value :
    recordGapCenter - 431890 = fullRecordGapValue00308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00308 (fullRecordGapValue00308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00308_not_prime : ¬(recordGapCenter - 431890).Prime := by
  rw [fullRecordGapTerm00308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00308_fast_pow_mod_ne_one

def fullRecordGapValue00309 : Nat := fullRecordGapCenterValue - 431778

theorem fullRecordGapTerm00309_eq_value :
    recordGapCenter - 431778 = fullRecordGapValue00309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00309 (fullRecordGapValue00309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00309_not_prime : ¬(recordGapCenter - 431778).Prime := by
  rw [fullRecordGapTerm00309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00309_fast_pow_mod_ne_one

def fullRecordGapValue00310 : Nat := fullRecordGapCenterValue - 431764

theorem fullRecordGapTerm00310_eq_value :
    recordGapCenter - 431764 = fullRecordGapValue00310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00310 (fullRecordGapValue00310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00310_not_prime : ¬(recordGapCenter - 431764).Prime := by
  rw [fullRecordGapTerm00310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00310_fast_pow_mod_ne_one

def fullRecordGapValue00311 : Nat := fullRecordGapCenterValue - 431682

theorem fullRecordGapTerm00311_eq_value :
    recordGapCenter - 431682 = fullRecordGapValue00311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00311 (fullRecordGapValue00311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00311_not_prime : ¬(recordGapCenter - 431682).Prime := by
  rw [fullRecordGapTerm00311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00311_fast_pow_mod_ne_one

def fullRecordGapValue00312 : Nat := fullRecordGapCenterValue - 431608

theorem fullRecordGapTerm00312_eq_value :
    recordGapCenter - 431608 = fullRecordGapValue00312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00312 (fullRecordGapValue00312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00312_not_prime : ¬(recordGapCenter - 431608).Prime := by
  rw [fullRecordGapTerm00312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00312_fast_pow_mod_ne_one

def fullRecordGapValue00313 : Nat := fullRecordGapCenterValue - 431590

theorem fullRecordGapTerm00313_eq_value :
    recordGapCenter - 431590 = fullRecordGapValue00313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00313 (fullRecordGapValue00313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00313_not_prime : ¬(recordGapCenter - 431590).Prime := by
  rw [fullRecordGapTerm00313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00313_fast_pow_mod_ne_one

def fullRecordGapValue00314 : Nat := fullRecordGapCenterValue - 431394

theorem fullRecordGapTerm00314_eq_value :
    recordGapCenter - 431394 = fullRecordGapValue00314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00314 (fullRecordGapValue00314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00314_not_prime : ¬(recordGapCenter - 431394).Prime := by
  rw [fullRecordGapTerm00314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00314_fast_pow_mod_ne_one

def fullRecordGapValue00315 : Nat := fullRecordGapCenterValue - 431308

theorem fullRecordGapTerm00315_eq_value :
    recordGapCenter - 431308 = fullRecordGapValue00315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00315 (fullRecordGapValue00315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00315_not_prime : ¬(recordGapCenter - 431308).Prime := by
  rw [fullRecordGapTerm00315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00315_fast_pow_mod_ne_one

def fullRecordGapValue00316 : Nat := fullRecordGapCenterValue - 431092

theorem fullRecordGapTerm00316_eq_value :
    recordGapCenter - 431092 = fullRecordGapValue00316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00316 (fullRecordGapValue00316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00316_not_prime : ¬(recordGapCenter - 431092).Prime := by
  rw [fullRecordGapTerm00316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00316_fast_pow_mod_ne_one

def fullRecordGapValue00317 : Nat := fullRecordGapCenterValue - 431058

theorem fullRecordGapTerm00317_eq_value :
    recordGapCenter - 431058 = fullRecordGapValue00317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00317 (fullRecordGapValue00317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00317_not_prime : ¬(recordGapCenter - 431058).Prime := by
  rw [fullRecordGapTerm00317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00317_fast_pow_mod_ne_one

def fullRecordGapValue00318 : Nat := fullRecordGapCenterValue - 431014

theorem fullRecordGapTerm00318_eq_value :
    recordGapCenter - 431014 = fullRecordGapValue00318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00318 (fullRecordGapValue00318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00318_not_prime : ¬(recordGapCenter - 431014).Prime := by
  rw [fullRecordGapTerm00318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00318_fast_pow_mod_ne_one

def fullRecordGapValue00319 : Nat := fullRecordGapCenterValue - 430888

theorem fullRecordGapTerm00319_eq_value :
    recordGapCenter - 430888 = fullRecordGapValue00319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00319 (fullRecordGapValue00319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00319_not_prime : ¬(recordGapCenter - 430888).Prime := by
  rw [fullRecordGapTerm00319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00319_fast_pow_mod_ne_one

def fullRecordGapValue00320 : Nat := fullRecordGapCenterValue - 430854

theorem fullRecordGapTerm00320_eq_value :
    recordGapCenter - 430854 = fullRecordGapValue00320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00320 (fullRecordGapValue00320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00320_not_prime : ¬(recordGapCenter - 430854).Prime := by
  rw [fullRecordGapTerm00320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00320_fast_pow_mod_ne_one

def fullRecordGapValue00321 : Nat := fullRecordGapCenterValue - 430842

theorem fullRecordGapTerm00321_eq_value :
    recordGapCenter - 430842 = fullRecordGapValue00321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00321 (fullRecordGapValue00321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00321_not_prime : ¬(recordGapCenter - 430842).Prime := by
  rw [fullRecordGapTerm00321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00321_fast_pow_mod_ne_one

def fullRecordGapValue00322 : Nat := fullRecordGapCenterValue - 430834

theorem fullRecordGapTerm00322_eq_value :
    recordGapCenter - 430834 = fullRecordGapValue00322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00322 (fullRecordGapValue00322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00322_not_prime : ¬(recordGapCenter - 430834).Prime := by
  rw [fullRecordGapTerm00322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00322_fast_pow_mod_ne_one

def fullRecordGapValue00323 : Nat := fullRecordGapCenterValue - 430792

theorem fullRecordGapTerm00323_eq_value :
    recordGapCenter - 430792 = fullRecordGapValue00323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00323 (fullRecordGapValue00323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00323_not_prime : ¬(recordGapCenter - 430792).Prime := by
  rw [fullRecordGapTerm00323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00323_fast_pow_mod_ne_one

def fullRecordGapValue00324 : Nat := fullRecordGapCenterValue - 430762

theorem fullRecordGapTerm00324_eq_value :
    recordGapCenter - 430762 = fullRecordGapValue00324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00324 (fullRecordGapValue00324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00324_not_prime : ¬(recordGapCenter - 430762).Prime := by
  rw [fullRecordGapTerm00324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00324_fast_pow_mod_ne_one

def fullRecordGapValue00325 : Nat := fullRecordGapCenterValue - 430734

theorem fullRecordGapTerm00325_eq_value :
    recordGapCenter - 430734 = fullRecordGapValue00325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00325 (fullRecordGapValue00325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00325_not_prime : ¬(recordGapCenter - 430734).Prime := by
  rw [fullRecordGapTerm00325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00325_fast_pow_mod_ne_one

def fullRecordGapValue00326 : Nat := fullRecordGapCenterValue - 430684

theorem fullRecordGapTerm00326_eq_value :
    recordGapCenter - 430684 = fullRecordGapValue00326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00326 (fullRecordGapValue00326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00326_not_prime : ¬(recordGapCenter - 430684).Prime := by
  rw [fullRecordGapTerm00326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00326_fast_pow_mod_ne_one

def fullRecordGapValue00327 : Nat := fullRecordGapCenterValue - 430594

theorem fullRecordGapTerm00327_eq_value :
    recordGapCenter - 430594 = fullRecordGapValue00327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00327 (fullRecordGapValue00327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00327_not_prime : ¬(recordGapCenter - 430594).Prime := by
  rw [fullRecordGapTerm00327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00327_fast_pow_mod_ne_one

def fullRecordGapValue00328 : Nat := fullRecordGapCenterValue - 430558

theorem fullRecordGapTerm00328_eq_value :
    recordGapCenter - 430558 = fullRecordGapValue00328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00328 (fullRecordGapValue00328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00328_not_prime : ¬(recordGapCenter - 430558).Prime := by
  rw [fullRecordGapTerm00328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00328_fast_pow_mod_ne_one

def fullRecordGapValue00329 : Nat := fullRecordGapCenterValue - 430552

theorem fullRecordGapTerm00329_eq_value :
    recordGapCenter - 430552 = fullRecordGapValue00329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00329 (fullRecordGapValue00329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00329_not_prime : ¬(recordGapCenter - 430552).Prime := by
  rw [fullRecordGapTerm00329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00329_fast_pow_mod_ne_one

def fullRecordGapValue00330 : Nat := fullRecordGapCenterValue - 430264

theorem fullRecordGapTerm00330_eq_value :
    recordGapCenter - 430264 = fullRecordGapValue00330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00330 (fullRecordGapValue00330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00330_not_prime : ¬(recordGapCenter - 430264).Prime := by
  rw [fullRecordGapTerm00330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00330_fast_pow_mod_ne_one

def fullRecordGapValue00331 : Nat := fullRecordGapCenterValue - 430174

theorem fullRecordGapTerm00331_eq_value :
    recordGapCenter - 430174 = fullRecordGapValue00331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00331 (fullRecordGapValue00331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00331_not_prime : ¬(recordGapCenter - 430174).Prime := by
  rw [fullRecordGapTerm00331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00331_fast_pow_mod_ne_one

def fullRecordGapValue00332 : Nat := fullRecordGapCenterValue - 430072

theorem fullRecordGapTerm00332_eq_value :
    recordGapCenter - 430072 = fullRecordGapValue00332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00332 (fullRecordGapValue00332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00332_not_prime : ¬(recordGapCenter - 430072).Prime := by
  rw [fullRecordGapTerm00332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00332_fast_pow_mod_ne_one

def fullRecordGapValue00333 : Nat := fullRecordGapCenterValue - 429798

theorem fullRecordGapTerm00333_eq_value :
    recordGapCenter - 429798 = fullRecordGapValue00333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00333 (fullRecordGapValue00333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00333_not_prime : ¬(recordGapCenter - 429798).Prime := by
  rw [fullRecordGapTerm00333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00333_fast_pow_mod_ne_one

def fullRecordGapValue00334 : Nat := fullRecordGapCenterValue - 429622

theorem fullRecordGapTerm00334_eq_value :
    recordGapCenter - 429622 = fullRecordGapValue00334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00334 (fullRecordGapValue00334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00334_not_prime : ¬(recordGapCenter - 429622).Prime := by
  rw [fullRecordGapTerm00334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00334_fast_pow_mod_ne_one

def fullRecordGapValue00335 : Nat := fullRecordGapCenterValue - 429544

theorem fullRecordGapTerm00335_eq_value :
    recordGapCenter - 429544 = fullRecordGapValue00335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00335 (fullRecordGapValue00335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00335_not_prime : ¬(recordGapCenter - 429544).Prime := by
  rw [fullRecordGapTerm00335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00335_fast_pow_mod_ne_one

def fullRecordGapValue00336 : Nat := fullRecordGapCenterValue - 429508

theorem fullRecordGapTerm00336_eq_value :
    recordGapCenter - 429508 = fullRecordGapValue00336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00336 (fullRecordGapValue00336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00336_not_prime : ¬(recordGapCenter - 429508).Prime := by
  rw [fullRecordGapTerm00336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00336_fast_pow_mod_ne_one

def fullRecordGapValue00337 : Nat := fullRecordGapCenterValue - 429414

theorem fullRecordGapTerm00337_eq_value :
    recordGapCenter - 429414 = fullRecordGapValue00337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00337 (fullRecordGapValue00337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00337_not_prime : ¬(recordGapCenter - 429414).Prime := by
  rw [fullRecordGapTerm00337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00337_fast_pow_mod_ne_one

def fullRecordGapValue00338 : Nat := fullRecordGapCenterValue - 429222

theorem fullRecordGapTerm00338_eq_value :
    recordGapCenter - 429222 = fullRecordGapValue00338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00338 (fullRecordGapValue00338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00338_not_prime : ¬(recordGapCenter - 429222).Prime := by
  rw [fullRecordGapTerm00338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00338_fast_pow_mod_ne_one

def fullRecordGapValue00339 : Nat := fullRecordGapCenterValue - 429064

theorem fullRecordGapTerm00339_eq_value :
    recordGapCenter - 429064 = fullRecordGapValue00339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00339 (fullRecordGapValue00339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00339_not_prime : ¬(recordGapCenter - 429064).Prime := by
  rw [fullRecordGapTerm00339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00339_fast_pow_mod_ne_one

def fullRecordGapValue00340 : Nat := fullRecordGapCenterValue - 428998

theorem fullRecordGapTerm00340_eq_value :
    recordGapCenter - 428998 = fullRecordGapValue00340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00340 (fullRecordGapValue00340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00340_not_prime : ¬(recordGapCenter - 428998).Prime := by
  rw [fullRecordGapTerm00340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00340_fast_pow_mod_ne_one

def fullRecordGapValue00341 : Nat := fullRecordGapCenterValue - 428878

theorem fullRecordGapTerm00341_eq_value :
    recordGapCenter - 428878 = fullRecordGapValue00341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00341 (fullRecordGapValue00341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00341_not_prime : ¬(recordGapCenter - 428878).Prime := by
  rw [fullRecordGapTerm00341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00341_fast_pow_mod_ne_one

def fullRecordGapValue00342 : Nat := fullRecordGapCenterValue - 428788

theorem fullRecordGapTerm00342_eq_value :
    recordGapCenter - 428788 = fullRecordGapValue00342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00342 (fullRecordGapValue00342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00342_not_prime : ¬(recordGapCenter - 428788).Prime := by
  rw [fullRecordGapTerm00342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00342_fast_pow_mod_ne_one

def fullRecordGapValue00343 : Nat := fullRecordGapCenterValue - 428782

theorem fullRecordGapTerm00343_eq_value :
    recordGapCenter - 428782 = fullRecordGapValue00343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00343 (fullRecordGapValue00343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00343_not_prime : ¬(recordGapCenter - 428782).Prime := by
  rw [fullRecordGapTerm00343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00343_fast_pow_mod_ne_one

def fullRecordGapValue00344 : Nat := fullRecordGapCenterValue - 428728

theorem fullRecordGapTerm00344_eq_value :
    recordGapCenter - 428728 = fullRecordGapValue00344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00344 (fullRecordGapValue00344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00344_not_prime : ¬(recordGapCenter - 428728).Prime := by
  rw [fullRecordGapTerm00344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00344_fast_pow_mod_ne_one

def fullRecordGapValue00345 : Nat := fullRecordGapCenterValue - 428658

theorem fullRecordGapTerm00345_eq_value :
    recordGapCenter - 428658 = fullRecordGapValue00345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00345 (fullRecordGapValue00345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00345_not_prime : ¬(recordGapCenter - 428658).Prime := by
  rw [fullRecordGapTerm00345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00345_fast_pow_mod_ne_one

def fullRecordGapValue00346 : Nat := fullRecordGapCenterValue - 428622

theorem fullRecordGapTerm00346_eq_value :
    recordGapCenter - 428622 = fullRecordGapValue00346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00346 (fullRecordGapValue00346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00346_not_prime : ¬(recordGapCenter - 428622).Prime := by
  rw [fullRecordGapTerm00346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00346_fast_pow_mod_ne_one

def fullRecordGapValue00347 : Nat := fullRecordGapCenterValue - 428334

theorem fullRecordGapTerm00347_eq_value :
    recordGapCenter - 428334 = fullRecordGapValue00347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00347 (fullRecordGapValue00347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00347_not_prime : ¬(recordGapCenter - 428334).Prime := by
  rw [fullRecordGapTerm00347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00347_fast_pow_mod_ne_one

def fullRecordGapValue00348 : Nat := fullRecordGapCenterValue - 427998

theorem fullRecordGapTerm00348_eq_value :
    recordGapCenter - 427998 = fullRecordGapValue00348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00348 (fullRecordGapValue00348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00348_not_prime : ¬(recordGapCenter - 427998).Prime := by
  rw [fullRecordGapTerm00348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00348_fast_pow_mod_ne_one

def fullRecordGapValue00349 : Nat := fullRecordGapCenterValue - 427972

theorem fullRecordGapTerm00349_eq_value :
    recordGapCenter - 427972 = fullRecordGapValue00349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00349 (fullRecordGapValue00349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00349_not_prime : ¬(recordGapCenter - 427972).Prime := by
  rw [fullRecordGapTerm00349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00349_fast_pow_mod_ne_one

def fullRecordGapValue00350 : Nat := fullRecordGapCenterValue - 427962

theorem fullRecordGapTerm00350_eq_value :
    recordGapCenter - 427962 = fullRecordGapValue00350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00350 (fullRecordGapValue00350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00350_not_prime : ¬(recordGapCenter - 427962).Prime := by
  rw [fullRecordGapTerm00350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00350_fast_pow_mod_ne_one

def fullRecordGapValue00351 : Nat := fullRecordGapCenterValue - 427902

theorem fullRecordGapTerm00351_eq_value :
    recordGapCenter - 427902 = fullRecordGapValue00351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00351 (fullRecordGapValue00351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00351_not_prime : ¬(recordGapCenter - 427902).Prime := by
  rw [fullRecordGapTerm00351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00351_fast_pow_mod_ne_one

def fullRecordGapValue00352 : Nat := fullRecordGapCenterValue - 427894

theorem fullRecordGapTerm00352_eq_value :
    recordGapCenter - 427894 = fullRecordGapValue00352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00352 (fullRecordGapValue00352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00352_not_prime : ¬(recordGapCenter - 427894).Prime := by
  rw [fullRecordGapTerm00352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00352_fast_pow_mod_ne_one

def fullRecordGapValue00353 : Nat := fullRecordGapCenterValue - 427858

theorem fullRecordGapTerm00353_eq_value :
    recordGapCenter - 427858 = fullRecordGapValue00353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00353 (fullRecordGapValue00353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00353_not_prime : ¬(recordGapCenter - 427858).Prime := by
  rw [fullRecordGapTerm00353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00353_fast_pow_mod_ne_one

def fullRecordGapValue00354 : Nat := fullRecordGapCenterValue - 427852

theorem fullRecordGapTerm00354_eq_value :
    recordGapCenter - 427852 = fullRecordGapValue00354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00354 (fullRecordGapValue00354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00354_not_prime : ¬(recordGapCenter - 427852).Prime := by
  rw [fullRecordGapTerm00354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00354_fast_pow_mod_ne_one

def fullRecordGapValue00355 : Nat := fullRecordGapCenterValue - 427828

theorem fullRecordGapTerm00355_eq_value :
    recordGapCenter - 427828 = fullRecordGapValue00355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00355 (fullRecordGapValue00355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00355_not_prime : ¬(recordGapCenter - 427828).Prime := by
  rw [fullRecordGapTerm00355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00355_fast_pow_mod_ne_one

def fullRecordGapValue00356 : Nat := fullRecordGapCenterValue - 427762

theorem fullRecordGapTerm00356_eq_value :
    recordGapCenter - 427762 = fullRecordGapValue00356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00356 (fullRecordGapValue00356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00356_not_prime : ¬(recordGapCenter - 427762).Prime := by
  rw [fullRecordGapTerm00356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00356_fast_pow_mod_ne_one

def fullRecordGapValue00357 : Nat := fullRecordGapCenterValue - 427528

theorem fullRecordGapTerm00357_eq_value :
    recordGapCenter - 427528 = fullRecordGapValue00357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00357 (fullRecordGapValue00357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00357_not_prime : ¬(recordGapCenter - 427528).Prime := by
  rw [fullRecordGapTerm00357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00357_fast_pow_mod_ne_one

def fullRecordGapValue00358 : Nat := fullRecordGapCenterValue - 427474

theorem fullRecordGapTerm00358_eq_value :
    recordGapCenter - 427474 = fullRecordGapValue00358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00358 (fullRecordGapValue00358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00358_not_prime : ¬(recordGapCenter - 427474).Prime := by
  rw [fullRecordGapTerm00358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00358_fast_pow_mod_ne_one

def fullRecordGapValue00359 : Nat := fullRecordGapCenterValue - 427468

theorem fullRecordGapTerm00359_eq_value :
    recordGapCenter - 427468 = fullRecordGapValue00359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00359 (fullRecordGapValue00359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00359_not_prime : ¬(recordGapCenter - 427468).Prime := by
  rw [fullRecordGapTerm00359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00359_fast_pow_mod_ne_one

def fullRecordGapValue00360 : Nat := fullRecordGapCenterValue - 427444

theorem fullRecordGapTerm00360_eq_value :
    recordGapCenter - 427444 = fullRecordGapValue00360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00360 (fullRecordGapValue00360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00360_not_prime : ¬(recordGapCenter - 427444).Prime := by
  rw [fullRecordGapTerm00360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00360_fast_pow_mod_ne_one

def fullRecordGapValue00361 : Nat := fullRecordGapCenterValue - 427282

theorem fullRecordGapTerm00361_eq_value :
    recordGapCenter - 427282 = fullRecordGapValue00361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00361 (fullRecordGapValue00361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00361_not_prime : ¬(recordGapCenter - 427282).Prime := by
  rw [fullRecordGapTerm00361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00361_fast_pow_mod_ne_one

def fullRecordGapValue00362 : Nat := fullRecordGapCenterValue - 427254

theorem fullRecordGapTerm00362_eq_value :
    recordGapCenter - 427254 = fullRecordGapValue00362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00362 (fullRecordGapValue00362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00362_not_prime : ¬(recordGapCenter - 427254).Prime := by
  rw [fullRecordGapTerm00362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00362_fast_pow_mod_ne_one

def fullRecordGapValue00363 : Nat := fullRecordGapCenterValue - 427012

theorem fullRecordGapTerm00363_eq_value :
    recordGapCenter - 427012 = fullRecordGapValue00363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00363 (fullRecordGapValue00363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00363_not_prime : ¬(recordGapCenter - 427012).Prime := by
  rw [fullRecordGapTerm00363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00363_fast_pow_mod_ne_one

def fullRecordGapValue00364 : Nat := fullRecordGapCenterValue - 426982

theorem fullRecordGapTerm00364_eq_value :
    recordGapCenter - 426982 = fullRecordGapValue00364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00364 (fullRecordGapValue00364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00364_not_prime : ¬(recordGapCenter - 426982).Prime := by
  rw [fullRecordGapTerm00364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00364_fast_pow_mod_ne_one

def fullRecordGapValue00365 : Nat := fullRecordGapCenterValue - 426934

theorem fullRecordGapTerm00365_eq_value :
    recordGapCenter - 426934 = fullRecordGapValue00365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00365 (fullRecordGapValue00365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00365_not_prime : ¬(recordGapCenter - 426934).Prime := by
  rw [fullRecordGapTerm00365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00365_fast_pow_mod_ne_one

def fullRecordGapValue00366 : Nat := fullRecordGapCenterValue - 426898

theorem fullRecordGapTerm00366_eq_value :
    recordGapCenter - 426898 = fullRecordGapValue00366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00366 (fullRecordGapValue00366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00366_not_prime : ¬(recordGapCenter - 426898).Prime := by
  rw [fullRecordGapTerm00366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00366_fast_pow_mod_ne_one

def fullRecordGapValue00367 : Nat := fullRecordGapCenterValue - 426888

theorem fullRecordGapTerm00367_eq_value :
    recordGapCenter - 426888 = fullRecordGapValue00367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00367 (fullRecordGapValue00367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00367_not_prime : ¬(recordGapCenter - 426888).Prime := by
  rw [fullRecordGapTerm00367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00367_fast_pow_mod_ne_one

def fullRecordGapValue00368 : Nat := fullRecordGapCenterValue - 426772

theorem fullRecordGapTerm00368_eq_value :
    recordGapCenter - 426772 = fullRecordGapValue00368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00368 (fullRecordGapValue00368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00368_not_prime : ¬(recordGapCenter - 426772).Prime := by
  rw [fullRecordGapTerm00368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00368_fast_pow_mod_ne_one

def fullRecordGapValue00369 : Nat := fullRecordGapCenterValue - 426724

theorem fullRecordGapTerm00369_eq_value :
    recordGapCenter - 426724 = fullRecordGapValue00369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00369 (fullRecordGapValue00369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00369_not_prime : ¬(recordGapCenter - 426724).Prime := by
  rw [fullRecordGapTerm00369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00369_fast_pow_mod_ne_one

def fullRecordGapValue00370 : Nat := fullRecordGapCenterValue - 426534

theorem fullRecordGapTerm00370_eq_value :
    recordGapCenter - 426534 = fullRecordGapValue00370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00370 (fullRecordGapValue00370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00370_not_prime : ¬(recordGapCenter - 426534).Prime := by
  rw [fullRecordGapTerm00370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00370_fast_pow_mod_ne_one

def fullRecordGapValue00371 : Nat := fullRecordGapCenterValue - 426508

theorem fullRecordGapTerm00371_eq_value :
    recordGapCenter - 426508 = fullRecordGapValue00371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00371 (fullRecordGapValue00371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00371_not_prime : ¬(recordGapCenter - 426508).Prime := by
  rw [fullRecordGapTerm00371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00371_fast_pow_mod_ne_one

def fullRecordGapValue00372 : Nat := fullRecordGapCenterValue - 426484

theorem fullRecordGapTerm00372_eq_value :
    recordGapCenter - 426484 = fullRecordGapValue00372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00372 (fullRecordGapValue00372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00372_not_prime : ¬(recordGapCenter - 426484).Prime := by
  rw [fullRecordGapTerm00372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00372_fast_pow_mod_ne_one

def fullRecordGapValue00373 : Nat := fullRecordGapCenterValue - 426418

theorem fullRecordGapTerm00373_eq_value :
    recordGapCenter - 426418 = fullRecordGapValue00373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00373 (fullRecordGapValue00373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00373_not_prime : ¬(recordGapCenter - 426418).Prime := by
  rw [fullRecordGapTerm00373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00373_fast_pow_mod_ne_one

def fullRecordGapValue00374 : Nat := fullRecordGapCenterValue - 426414

theorem fullRecordGapTerm00374_eq_value :
    recordGapCenter - 426414 = fullRecordGapValue00374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00374 (fullRecordGapValue00374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00374_not_prime : ¬(recordGapCenter - 426414).Prime := by
  rw [fullRecordGapTerm00374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00374_fast_pow_mod_ne_one

def fullRecordGapValue00375 : Nat := fullRecordGapCenterValue - 426354

theorem fullRecordGapTerm00375_eq_value :
    recordGapCenter - 426354 = fullRecordGapValue00375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00375 (fullRecordGapValue00375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00375_not_prime : ¬(recordGapCenter - 426354).Prime := by
  rw [fullRecordGapTerm00375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00375_fast_pow_mod_ne_one

def fullRecordGapValue00376 : Nat := fullRecordGapCenterValue - 426138

theorem fullRecordGapTerm00376_eq_value :
    recordGapCenter - 426138 = fullRecordGapValue00376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00376 (fullRecordGapValue00376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00376_not_prime : ¬(recordGapCenter - 426138).Prime := by
  rw [fullRecordGapTerm00376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00376_fast_pow_mod_ne_one

def fullRecordGapValue00377 : Nat := fullRecordGapCenterValue - 426124

theorem fullRecordGapTerm00377_eq_value :
    recordGapCenter - 426124 = fullRecordGapValue00377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00377 (fullRecordGapValue00377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00377_not_prime : ¬(recordGapCenter - 426124).Prime := by
  rw [fullRecordGapTerm00377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00377_fast_pow_mod_ne_one

def fullRecordGapValue00378 : Nat := fullRecordGapCenterValue - 426004

theorem fullRecordGapTerm00378_eq_value :
    recordGapCenter - 426004 = fullRecordGapValue00378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00378 (fullRecordGapValue00378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00378_not_prime : ¬(recordGapCenter - 426004).Prime := by
  rw [fullRecordGapTerm00378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00378_fast_pow_mod_ne_one

def fullRecordGapValue00379 : Nat := fullRecordGapCenterValue - 425994

theorem fullRecordGapTerm00379_eq_value :
    recordGapCenter - 425994 = fullRecordGapValue00379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00379 (fullRecordGapValue00379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00379_not_prime : ¬(recordGapCenter - 425994).Prime := by
  rw [fullRecordGapTerm00379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00379_fast_pow_mod_ne_one

def fullRecordGapValue00380 : Nat := fullRecordGapCenterValue - 425974

theorem fullRecordGapTerm00380_eq_value :
    recordGapCenter - 425974 = fullRecordGapValue00380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00380 (fullRecordGapValue00380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00380_not_prime : ¬(recordGapCenter - 425974).Prime := by
  rw [fullRecordGapTerm00380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00380_fast_pow_mod_ne_one

def fullRecordGapValue00381 : Nat := fullRecordGapCenterValue - 425962

theorem fullRecordGapTerm00381_eq_value :
    recordGapCenter - 425962 = fullRecordGapValue00381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00381 (fullRecordGapValue00381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00381_not_prime : ¬(recordGapCenter - 425962).Prime := by
  rw [fullRecordGapTerm00381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00381_fast_pow_mod_ne_one

def fullRecordGapValue00382 : Nat := fullRecordGapCenterValue - 425848

theorem fullRecordGapTerm00382_eq_value :
    recordGapCenter - 425848 = fullRecordGapValue00382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00382 (fullRecordGapValue00382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00382_not_prime : ¬(recordGapCenter - 425848).Prime := by
  rw [fullRecordGapTerm00382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00382_fast_pow_mod_ne_one

def fullRecordGapValue00383 : Nat := fullRecordGapCenterValue - 425694

theorem fullRecordGapTerm00383_eq_value :
    recordGapCenter - 425694 = fullRecordGapValue00383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00383 (fullRecordGapValue00383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00383_not_prime : ¬(recordGapCenter - 425694).Prime := by
  rw [fullRecordGapTerm00383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00383_fast_pow_mod_ne_one

def fullRecordGapValue00384 : Nat := fullRecordGapCenterValue - 425512

theorem fullRecordGapTerm00384_eq_value :
    recordGapCenter - 425512 = fullRecordGapValue00384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00384 (fullRecordGapValue00384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00384_not_prime : ¬(recordGapCenter - 425512).Prime := by
  rw [fullRecordGapTerm00384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00384_fast_pow_mod_ne_one

def fullRecordGapValue00385 : Nat := fullRecordGapCenterValue - 425428

theorem fullRecordGapTerm00385_eq_value :
    recordGapCenter - 425428 = fullRecordGapValue00385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00385 (fullRecordGapValue00385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00385_not_prime : ¬(recordGapCenter - 425428).Prime := by
  rw [fullRecordGapTerm00385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00385_fast_pow_mod_ne_one

def fullRecordGapValue00386 : Nat := fullRecordGapCenterValue - 425338

theorem fullRecordGapTerm00386_eq_value :
    recordGapCenter - 425338 = fullRecordGapValue00386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00386 (fullRecordGapValue00386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00386_not_prime : ¬(recordGapCenter - 425338).Prime := by
  rw [fullRecordGapTerm00386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00386_fast_pow_mod_ne_one

def fullRecordGapValue00387 : Nat := fullRecordGapCenterValue - 425254

theorem fullRecordGapTerm00387_eq_value :
    recordGapCenter - 425254 = fullRecordGapValue00387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00387 (fullRecordGapValue00387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00387_not_prime : ¬(recordGapCenter - 425254).Prime := by
  rw [fullRecordGapTerm00387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00387_fast_pow_mod_ne_one

def fullRecordGapValue00388 : Nat := fullRecordGapCenterValue - 425250

theorem fullRecordGapTerm00388_eq_value :
    recordGapCenter - 425250 = fullRecordGapValue00388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00388 (fullRecordGapValue00388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00388_not_prime : ¬(recordGapCenter - 425250).Prime := by
  rw [fullRecordGapTerm00388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00388_fast_pow_mod_ne_one

def fullRecordGapValue00389 : Nat := fullRecordGapCenterValue - 425212

theorem fullRecordGapTerm00389_eq_value :
    recordGapCenter - 425212 = fullRecordGapValue00389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00389 (fullRecordGapValue00389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00389_not_prime : ¬(recordGapCenter - 425212).Prime := by
  rw [fullRecordGapTerm00389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00389_fast_pow_mod_ne_one

def fullRecordGapValue00390 : Nat := fullRecordGapCenterValue - 425164

theorem fullRecordGapTerm00390_eq_value :
    recordGapCenter - 425164 = fullRecordGapValue00390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00390 (fullRecordGapValue00390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00390_not_prime : ¬(recordGapCenter - 425164).Prime := by
  rw [fullRecordGapTerm00390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00390_fast_pow_mod_ne_one

def fullRecordGapValue00391 : Nat := fullRecordGapCenterValue - 425122

theorem fullRecordGapTerm00391_eq_value :
    recordGapCenter - 425122 = fullRecordGapValue00391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00391 (fullRecordGapValue00391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00391_not_prime : ¬(recordGapCenter - 425122).Prime := by
  rw [fullRecordGapTerm00391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00391_fast_pow_mod_ne_one

def fullRecordGapValue00392 : Nat := fullRecordGapCenterValue - 425094

theorem fullRecordGapTerm00392_eq_value :
    recordGapCenter - 425094 = fullRecordGapValue00392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00392 (fullRecordGapValue00392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00392_not_prime : ¬(recordGapCenter - 425094).Prime := by
  rw [fullRecordGapTerm00392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00392_fast_pow_mod_ne_one

def fullRecordGapValue00393 : Nat := fullRecordGapCenterValue - 425058

theorem fullRecordGapTerm00393_eq_value :
    recordGapCenter - 425058 = fullRecordGapValue00393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00393 (fullRecordGapValue00393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00393_not_prime : ¬(recordGapCenter - 425058).Prime := by
  rw [fullRecordGapTerm00393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00393_fast_pow_mod_ne_one

def fullRecordGapValue00394 : Nat := fullRecordGapCenterValue - 424828

theorem fullRecordGapTerm00394_eq_value :
    recordGapCenter - 424828 = fullRecordGapValue00394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00394 (fullRecordGapValue00394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00394_not_prime : ¬(recordGapCenter - 424828).Prime := by
  rw [fullRecordGapTerm00394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00394_fast_pow_mod_ne_one

def fullRecordGapValue00395 : Nat := fullRecordGapCenterValue - 424744

theorem fullRecordGapTerm00395_eq_value :
    recordGapCenter - 424744 = fullRecordGapValue00395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00395 (fullRecordGapValue00395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00395_not_prime : ¬(recordGapCenter - 424744).Prime := by
  rw [fullRecordGapTerm00395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00395_fast_pow_mod_ne_one

def fullRecordGapValue00396 : Nat := fullRecordGapCenterValue - 424738

theorem fullRecordGapTerm00396_eq_value :
    recordGapCenter - 424738 = fullRecordGapValue00396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00396 (fullRecordGapValue00396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00396_not_prime : ¬(recordGapCenter - 424738).Prime := by
  rw [fullRecordGapTerm00396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00396_fast_pow_mod_ne_one

def fullRecordGapValue00397 : Nat := fullRecordGapCenterValue - 424552

theorem fullRecordGapTerm00397_eq_value :
    recordGapCenter - 424552 = fullRecordGapValue00397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00397 (fullRecordGapValue00397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00397_not_prime : ¬(recordGapCenter - 424552).Prime := by
  rw [fullRecordGapTerm00397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00397_fast_pow_mod_ne_one

def fullRecordGapValue00398 : Nat := fullRecordGapCenterValue - 424492

theorem fullRecordGapTerm00398_eq_value :
    recordGapCenter - 424492 = fullRecordGapValue00398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00398 (fullRecordGapValue00398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00398_not_prime : ¬(recordGapCenter - 424492).Prime := by
  rw [fullRecordGapTerm00398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00398_fast_pow_mod_ne_one

def fullRecordGapValue00399 : Nat := fullRecordGapCenterValue - 424374

theorem fullRecordGapTerm00399_eq_value :
    recordGapCenter - 424374 = fullRecordGapValue00399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00399 (fullRecordGapValue00399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00399_not_prime : ¬(recordGapCenter - 424374).Prime := by
  rw [fullRecordGapTerm00399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00399_fast_pow_mod_ne_one

def fullRecordGapValue00400 : Nat := fullRecordGapCenterValue - 424282

theorem fullRecordGapTerm00400_eq_value :
    recordGapCenter - 424282 = fullRecordGapValue00400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00400 (fullRecordGapValue00400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00400_not_prime : ¬(recordGapCenter - 424282).Prime := by
  rw [fullRecordGapTerm00400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00400_fast_pow_mod_ne_one

def fullRecordGapValue00401 : Nat := fullRecordGapCenterValue - 424254

theorem fullRecordGapTerm00401_eq_value :
    recordGapCenter - 424254 = fullRecordGapValue00401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00401 (fullRecordGapValue00401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00401_not_prime : ¬(recordGapCenter - 424254).Prime := by
  rw [fullRecordGapTerm00401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00401_fast_pow_mod_ne_one

def fullRecordGapValue00402 : Nat := fullRecordGapCenterValue - 424234

theorem fullRecordGapTerm00402_eq_value :
    recordGapCenter - 424234 = fullRecordGapValue00402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00402 (fullRecordGapValue00402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00402_not_prime : ¬(recordGapCenter - 424234).Prime := by
  rw [fullRecordGapTerm00402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00402_fast_pow_mod_ne_one

def fullRecordGapValue00403 : Nat := fullRecordGapCenterValue - 424132

theorem fullRecordGapTerm00403_eq_value :
    recordGapCenter - 424132 = fullRecordGapValue00403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00403 (fullRecordGapValue00403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00403_not_prime : ¬(recordGapCenter - 424132).Prime := by
  rw [fullRecordGapTerm00403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00403_fast_pow_mod_ne_one

def fullRecordGapValue00404 : Nat := fullRecordGapCenterValue - 424114

theorem fullRecordGapTerm00404_eq_value :
    recordGapCenter - 424114 = fullRecordGapValue00404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00404 (fullRecordGapValue00404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00404_not_prime : ¬(recordGapCenter - 424114).Prime := by
  rw [fullRecordGapTerm00404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00404_fast_pow_mod_ne_one

def fullRecordGapValue00405 : Nat := fullRecordGapCenterValue - 423868

theorem fullRecordGapTerm00405_eq_value :
    recordGapCenter - 423868 = fullRecordGapValue00405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00405 (fullRecordGapValue00405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00405_not_prime : ¬(recordGapCenter - 423868).Prime := by
  rw [fullRecordGapTerm00405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00405_fast_pow_mod_ne_one

def fullRecordGapValue00406 : Nat := fullRecordGapCenterValue - 423784

theorem fullRecordGapTerm00406_eq_value :
    recordGapCenter - 423784 = fullRecordGapValue00406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00406 (fullRecordGapValue00406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00406_not_prime : ¬(recordGapCenter - 423784).Prime := by
  rw [fullRecordGapTerm00406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00406_fast_pow_mod_ne_one

def fullRecordGapValue00407 : Nat := fullRecordGapCenterValue - 423762

theorem fullRecordGapTerm00407_eq_value :
    recordGapCenter - 423762 = fullRecordGapValue00407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00407 (fullRecordGapValue00407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00407_not_prime : ¬(recordGapCenter - 423762).Prime := by
  rw [fullRecordGapTerm00407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00407_fast_pow_mod_ne_one

def fullRecordGapValue00408 : Nat := fullRecordGapCenterValue - 423622

theorem fullRecordGapTerm00408_eq_value :
    recordGapCenter - 423622 = fullRecordGapValue00408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00408 (fullRecordGapValue00408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00408_not_prime : ¬(recordGapCenter - 423622).Prime := by
  rw [fullRecordGapTerm00408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00408_fast_pow_mod_ne_one

def fullRecordGapValue00409 : Nat := fullRecordGapCenterValue - 423562

theorem fullRecordGapTerm00409_eq_value :
    recordGapCenter - 423562 = fullRecordGapValue00409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00409 (fullRecordGapValue00409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00409_not_prime : ¬(recordGapCenter - 423562).Prime := by
  rw [fullRecordGapTerm00409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00409_fast_pow_mod_ne_one

def fullRecordGapValue00410 : Nat := fullRecordGapCenterValue - 423532

theorem fullRecordGapTerm00410_eq_value :
    recordGapCenter - 423532 = fullRecordGapValue00410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00410 (fullRecordGapValue00410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00410_not_prime : ¬(recordGapCenter - 423532).Prime := by
  rw [fullRecordGapTerm00410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00410_fast_pow_mod_ne_one

def fullRecordGapValue00411 : Nat := fullRecordGapCenterValue - 423498

theorem fullRecordGapTerm00411_eq_value :
    recordGapCenter - 423498 = fullRecordGapValue00411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00411 (fullRecordGapValue00411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00411_not_prime : ¬(recordGapCenter - 423498).Prime := by
  rw [fullRecordGapTerm00411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00411_fast_pow_mod_ne_one

def fullRecordGapValue00412 : Nat := fullRecordGapCenterValue - 423454

theorem fullRecordGapTerm00412_eq_value :
    recordGapCenter - 423454 = fullRecordGapValue00412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00412 (fullRecordGapValue00412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00412_not_prime : ¬(recordGapCenter - 423454).Prime := by
  rw [fullRecordGapTerm00412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00412_fast_pow_mod_ne_one

def fullRecordGapValue00413 : Nat := fullRecordGapCenterValue - 423360

theorem fullRecordGapTerm00413_eq_value :
    recordGapCenter - 423360 = fullRecordGapValue00413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00413 (fullRecordGapValue00413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00413_not_prime : ¬(recordGapCenter - 423360).Prime := by
  rw [fullRecordGapTerm00413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00413_fast_pow_mod_ne_one

def fullRecordGapValue00414 : Nat := fullRecordGapCenterValue - 423352

theorem fullRecordGapTerm00414_eq_value :
    recordGapCenter - 423352 = fullRecordGapValue00414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00414 (fullRecordGapValue00414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00414_not_prime : ¬(recordGapCenter - 423352).Prime := by
  rw [fullRecordGapTerm00414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00414_fast_pow_mod_ne_one

def fullRecordGapValue00415 : Nat := fullRecordGapCenterValue - 423268

theorem fullRecordGapTerm00415_eq_value :
    recordGapCenter - 423268 = fullRecordGapValue00415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00415 (fullRecordGapValue00415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00415_not_prime : ¬(recordGapCenter - 423268).Prime := by
  rw [fullRecordGapTerm00415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00415_fast_pow_mod_ne_one

def fullRecordGapValue00416 : Nat := fullRecordGapCenterValue - 423222

theorem fullRecordGapTerm00416_eq_value :
    recordGapCenter - 423222 = fullRecordGapValue00416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00416 (fullRecordGapValue00416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00416_not_prime : ¬(recordGapCenter - 423222).Prime := by
  rw [fullRecordGapTerm00416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00416_fast_pow_mod_ne_one

def fullRecordGapValue00417 : Nat := fullRecordGapCenterValue - 423142

theorem fullRecordGapTerm00417_eq_value :
    recordGapCenter - 423142 = fullRecordGapValue00417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00417 (fullRecordGapValue00417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00417_not_prime : ¬(recordGapCenter - 423142).Prime := by
  rw [fullRecordGapTerm00417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00417_fast_pow_mod_ne_one

def fullRecordGapValue00418 : Nat := fullRecordGapCenterValue - 422854

theorem fullRecordGapTerm00418_eq_value :
    recordGapCenter - 422854 = fullRecordGapValue00418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00418 (fullRecordGapValue00418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00418_not_prime : ¬(recordGapCenter - 422854).Prime := by
  rw [fullRecordGapTerm00418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00418_fast_pow_mod_ne_one

def fullRecordGapValue00419 : Nat := fullRecordGapCenterValue - 422742

theorem fullRecordGapTerm00419_eq_value :
    recordGapCenter - 422742 = fullRecordGapValue00419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00419 (fullRecordGapValue00419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00419_not_prime : ¬(recordGapCenter - 422742).Prime := by
  rw [fullRecordGapTerm00419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00419_fast_pow_mod_ne_one

def fullRecordGapValue00420 : Nat := fullRecordGapCenterValue - 422574

theorem fullRecordGapTerm00420_eq_value :
    recordGapCenter - 422574 = fullRecordGapValue00420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00420 (fullRecordGapValue00420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00420_not_prime : ¬(recordGapCenter - 422574).Prime := by
  rw [fullRecordGapTerm00420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00420_fast_pow_mod_ne_one

def fullRecordGapValue00421 : Nat := fullRecordGapCenterValue - 422538

theorem fullRecordGapTerm00421_eq_value :
    recordGapCenter - 422538 = fullRecordGapValue00421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00421 (fullRecordGapValue00421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00421_not_prime : ¬(recordGapCenter - 422538).Prime := by
  rw [fullRecordGapTerm00421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00421_fast_pow_mod_ne_one

def fullRecordGapValue00422 : Nat := fullRecordGapCenterValue - 422482

theorem fullRecordGapTerm00422_eq_value :
    recordGapCenter - 422482 = fullRecordGapValue00422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00422 (fullRecordGapValue00422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00422_not_prime : ¬(recordGapCenter - 422482).Prime := by
  rw [fullRecordGapTerm00422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00422_fast_pow_mod_ne_one

def fullRecordGapValue00423 : Nat := fullRecordGapCenterValue - 422428

theorem fullRecordGapTerm00423_eq_value :
    recordGapCenter - 422428 = fullRecordGapValue00423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00423 (fullRecordGapValue00423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00423_not_prime : ¬(recordGapCenter - 422428).Prime := by
  rw [fullRecordGapTerm00423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00423_fast_pow_mod_ne_one

def fullRecordGapValue00424 : Nat := fullRecordGapCenterValue - 422398

theorem fullRecordGapTerm00424_eq_value :
    recordGapCenter - 422398 = fullRecordGapValue00424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00424 (fullRecordGapValue00424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00424_not_prime : ¬(recordGapCenter - 422398).Prime := by
  rw [fullRecordGapTerm00424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00424_fast_pow_mod_ne_one

def fullRecordGapValue00425 : Nat := fullRecordGapCenterValue - 422274

theorem fullRecordGapTerm00425_eq_value :
    recordGapCenter - 422274 = fullRecordGapValue00425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00425 (fullRecordGapValue00425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00425_not_prime : ¬(recordGapCenter - 422274).Prime := by
  rw [fullRecordGapTerm00425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00425_fast_pow_mod_ne_one

def fullRecordGapValue00426 : Nat := fullRecordGapCenterValue - 422194

theorem fullRecordGapTerm00426_eq_value :
    recordGapCenter - 422194 = fullRecordGapValue00426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00426 (fullRecordGapValue00426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00426_not_prime : ¬(recordGapCenter - 422194).Prime := by
  rw [fullRecordGapTerm00426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00426_fast_pow_mod_ne_one

def fullRecordGapValue00427 : Nat := fullRecordGapCenterValue - 422152

theorem fullRecordGapTerm00427_eq_value :
    recordGapCenter - 422152 = fullRecordGapValue00427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00427 (fullRecordGapValue00427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00427_not_prime : ¬(recordGapCenter - 422152).Prime := by
  rw [fullRecordGapTerm00427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00427_fast_pow_mod_ne_one

def fullRecordGapValue00428 : Nat := fullRecordGapCenterValue - 422068

theorem fullRecordGapTerm00428_eq_value :
    recordGapCenter - 422068 = fullRecordGapValue00428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00428 (fullRecordGapValue00428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00428_not_prime : ¬(recordGapCenter - 422068).Prime := by
  rw [fullRecordGapTerm00428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00428_fast_pow_mod_ne_one

def fullRecordGapValue00429 : Nat := fullRecordGapCenterValue - 422014

theorem fullRecordGapTerm00429_eq_value :
    recordGapCenter - 422014 = fullRecordGapValue00429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00429 (fullRecordGapValue00429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00429_not_prime : ¬(recordGapCenter - 422014).Prime := by
  rw [fullRecordGapTerm00429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00429_fast_pow_mod_ne_one

def fullRecordGapValue00430 : Nat := fullRecordGapCenterValue - 421878

theorem fullRecordGapTerm00430_eq_value :
    recordGapCenter - 421878 = fullRecordGapValue00430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00430 (fullRecordGapValue00430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00430_not_prime : ¬(recordGapCenter - 421878).Prime := by
  rw [fullRecordGapTerm00430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00430_fast_pow_mod_ne_one

def fullRecordGapValue00431 : Nat := fullRecordGapCenterValue - 421864

theorem fullRecordGapTerm00431_eq_value :
    recordGapCenter - 421864 = fullRecordGapValue00431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00431 (fullRecordGapValue00431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00431_not_prime : ¬(recordGapCenter - 421864).Prime := by
  rw [fullRecordGapTerm00431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00431_fast_pow_mod_ne_one

def fullRecordGapValue00432 : Nat := fullRecordGapCenterValue - 421738

theorem fullRecordGapTerm00432_eq_value :
    recordGapCenter - 421738 = fullRecordGapValue00432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00432 (fullRecordGapValue00432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00432_not_prime : ¬(recordGapCenter - 421738).Prime := by
  rw [fullRecordGapTerm00432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00432_fast_pow_mod_ne_one

def fullRecordGapValue00433 : Nat := fullRecordGapCenterValue - 421734

theorem fullRecordGapTerm00433_eq_value :
    recordGapCenter - 421734 = fullRecordGapValue00433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00433 (fullRecordGapValue00433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00433_not_prime : ¬(recordGapCenter - 421734).Prime := by
  rw [fullRecordGapTerm00433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00433_fast_pow_mod_ne_one

def fullRecordGapValue00434 : Nat := fullRecordGapCenterValue - 421714

theorem fullRecordGapTerm00434_eq_value :
    recordGapCenter - 421714 = fullRecordGapValue00434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00434 (fullRecordGapValue00434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00434_not_prime : ¬(recordGapCenter - 421714).Prime := by
  rw [fullRecordGapTerm00434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00434_fast_pow_mod_ne_one

def fullRecordGapValue00435 : Nat := fullRecordGapCenterValue - 421588

theorem fullRecordGapTerm00435_eq_value :
    recordGapCenter - 421588 = fullRecordGapValue00435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00435 (fullRecordGapValue00435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00435_not_prime : ¬(recordGapCenter - 421588).Prime := by
  rw [fullRecordGapTerm00435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00435_fast_pow_mod_ne_one

def fullRecordGapValue00436 : Nat := fullRecordGapCenterValue - 421522

theorem fullRecordGapTerm00436_eq_value :
    recordGapCenter - 421522 = fullRecordGapValue00436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00436 (fullRecordGapValue00436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00436_not_prime : ¬(recordGapCenter - 421522).Prime := by
  rw [fullRecordGapTerm00436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00436_fast_pow_mod_ne_one

def fullRecordGapValue00437 : Nat := fullRecordGapCenterValue - 421438

theorem fullRecordGapTerm00437_eq_value :
    recordGapCenter - 421438 = fullRecordGapValue00437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00437 (fullRecordGapValue00437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00437_not_prime : ¬(recordGapCenter - 421438).Prime := by
  rw [fullRecordGapTerm00437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00437_fast_pow_mod_ne_one

def fullRecordGapValue00438 : Nat := fullRecordGapCenterValue - 421242

theorem fullRecordGapTerm00438_eq_value :
    recordGapCenter - 421242 = fullRecordGapValue00438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00438 (fullRecordGapValue00438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00438_not_prime : ¬(recordGapCenter - 421242).Prime := by
  rw [fullRecordGapTerm00438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00438_fast_pow_mod_ne_one

def fullRecordGapValue00439 : Nat := fullRecordGapCenterValue - 421108

theorem fullRecordGapTerm00439_eq_value :
    recordGapCenter - 421108 = fullRecordGapValue00439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00439 (fullRecordGapValue00439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00439_not_prime : ¬(recordGapCenter - 421108).Prime := by
  rw [fullRecordGapTerm00439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00439_fast_pow_mod_ne_one

def fullRecordGapValue00440 : Nat := fullRecordGapCenterValue - 421054

theorem fullRecordGapTerm00440_eq_value :
    recordGapCenter - 421054 = fullRecordGapValue00440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00440 (fullRecordGapValue00440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00440_not_prime : ¬(recordGapCenter - 421054).Prime := by
  rw [fullRecordGapTerm00440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00440_fast_pow_mod_ne_one

def fullRecordGapValue00441 : Nat := fullRecordGapCenterValue - 421048

theorem fullRecordGapTerm00441_eq_value :
    recordGapCenter - 421048 = fullRecordGapValue00441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00441 (fullRecordGapValue00441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00441_not_prime : ¬(recordGapCenter - 421048).Prime := by
  rw [fullRecordGapTerm00441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00441_fast_pow_mod_ne_one

def fullRecordGapValue00442 : Nat := fullRecordGapCenterValue - 420982

theorem fullRecordGapTerm00442_eq_value :
    recordGapCenter - 420982 = fullRecordGapValue00442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00442 (fullRecordGapValue00442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00442_not_prime : ¬(recordGapCenter - 420982).Prime := by
  rw [fullRecordGapTerm00442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00442_fast_pow_mod_ne_one

def fullRecordGapValue00443 : Nat := fullRecordGapCenterValue - 420922

theorem fullRecordGapTerm00443_eq_value :
    recordGapCenter - 420922 = fullRecordGapValue00443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00443 (fullRecordGapValue00443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00443_not_prime : ¬(recordGapCenter - 420922).Prime := by
  rw [fullRecordGapTerm00443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00443_fast_pow_mod_ne_one

def fullRecordGapValue00444 : Nat := fullRecordGapCenterValue - 420874

theorem fullRecordGapTerm00444_eq_value :
    recordGapCenter - 420874 = fullRecordGapValue00444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00444 (fullRecordGapValue00444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00444_not_prime : ¬(recordGapCenter - 420874).Prime := by
  rw [fullRecordGapTerm00444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00444_fast_pow_mod_ne_one

def fullRecordGapValue00445 : Nat := fullRecordGapCenterValue - 420814

theorem fullRecordGapTerm00445_eq_value :
    recordGapCenter - 420814 = fullRecordGapValue00445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00445 (fullRecordGapValue00445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00445_not_prime : ¬(recordGapCenter - 420814).Prime := by
  rw [fullRecordGapTerm00445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00445_fast_pow_mod_ne_one

def fullRecordGapValue00446 : Nat := fullRecordGapCenterValue - 420802

theorem fullRecordGapTerm00446_eq_value :
    recordGapCenter - 420802 = fullRecordGapValue00446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00446 (fullRecordGapValue00446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00446_not_prime : ¬(recordGapCenter - 420802).Prime := by
  rw [fullRecordGapTerm00446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00446_fast_pow_mod_ne_one

def fullRecordGapValue00447 : Nat := fullRecordGapCenterValue - 420718

theorem fullRecordGapTerm00447_eq_value :
    recordGapCenter - 420718 = fullRecordGapValue00447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00447 (fullRecordGapValue00447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00447_not_prime : ¬(recordGapCenter - 420718).Prime := by
  rw [fullRecordGapTerm00447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00447_fast_pow_mod_ne_one

def fullRecordGapValue00448 : Nat := fullRecordGapCenterValue - 420664

theorem fullRecordGapTerm00448_eq_value :
    recordGapCenter - 420664 = fullRecordGapValue00448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00448 (fullRecordGapValue00448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00448_not_prime : ¬(recordGapCenter - 420664).Prime := by
  rw [fullRecordGapTerm00448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00448_fast_pow_mod_ne_one

def fullRecordGapValue00449 : Nat := fullRecordGapCenterValue - 420474

theorem fullRecordGapTerm00449_eq_value :
    recordGapCenter - 420474 = fullRecordGapValue00449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00449 (fullRecordGapValue00449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00449_not_prime : ¬(recordGapCenter - 420474).Prime := by
  rw [fullRecordGapTerm00449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00449_fast_pow_mod_ne_one

def fullRecordGapValue00450 : Nat := fullRecordGapCenterValue - 420388

theorem fullRecordGapTerm00450_eq_value :
    recordGapCenter - 420388 = fullRecordGapValue00450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00450 (fullRecordGapValue00450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00450_not_prime : ¬(recordGapCenter - 420388).Prime := by
  rw [fullRecordGapTerm00450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00450_fast_pow_mod_ne_one

def fullRecordGapValue00451 : Nat := fullRecordGapCenterValue - 420382

theorem fullRecordGapTerm00451_eq_value :
    recordGapCenter - 420382 = fullRecordGapValue00451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00451 (fullRecordGapValue00451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00451_not_prime : ¬(recordGapCenter - 420382).Prime := by
  rw [fullRecordGapTerm00451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00451_fast_pow_mod_ne_one

def fullRecordGapValue00452 : Nat := fullRecordGapCenterValue - 420262

theorem fullRecordGapTerm00452_eq_value :
    recordGapCenter - 420262 = fullRecordGapValue00452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00452 (fullRecordGapValue00452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00452_not_prime : ¬(recordGapCenter - 420262).Prime := by
  rw [fullRecordGapTerm00452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00452_fast_pow_mod_ne_one

def fullRecordGapValue00453 : Nat := fullRecordGapCenterValue - 420234

theorem fullRecordGapTerm00453_eq_value :
    recordGapCenter - 420234 = fullRecordGapValue00453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00453 (fullRecordGapValue00453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00453_not_prime : ¬(recordGapCenter - 420234).Prime := by
  rw [fullRecordGapTerm00453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00453_fast_pow_mod_ne_one

def fullRecordGapValue00454 : Nat := fullRecordGapCenterValue - 420088

theorem fullRecordGapTerm00454_eq_value :
    recordGapCenter - 420088 = fullRecordGapValue00454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00454 (fullRecordGapValue00454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00454_not_prime : ¬(recordGapCenter - 420088).Prime := by
  rw [fullRecordGapTerm00454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00454_fast_pow_mod_ne_one

def fullRecordGapValue00455 : Nat := fullRecordGapCenterValue - 420054

theorem fullRecordGapTerm00455_eq_value :
    recordGapCenter - 420054 = fullRecordGapValue00455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00455 (fullRecordGapValue00455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00455_not_prime : ¬(recordGapCenter - 420054).Prime := by
  rw [fullRecordGapTerm00455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00455_fast_pow_mod_ne_one

def fullRecordGapValue00456 : Nat := fullRecordGapCenterValue - 420018

theorem fullRecordGapTerm00456_eq_value :
    recordGapCenter - 420018 = fullRecordGapValue00456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00456 (fullRecordGapValue00456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00456_not_prime : ¬(recordGapCenter - 420018).Prime := by
  rw [fullRecordGapTerm00456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00456_fast_pow_mod_ne_one

def fullRecordGapValue00457 : Nat := fullRecordGapCenterValue - 420000

theorem fullRecordGapTerm00457_eq_value :
    recordGapCenter - 420000 = fullRecordGapValue00457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00457 (fullRecordGapValue00457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00457_not_prime : ¬(recordGapCenter - 420000).Prime := by
  rw [fullRecordGapTerm00457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00457_fast_pow_mod_ne_one

def fullRecordGapValue00458 : Nat := fullRecordGapCenterValue - 419982

theorem fullRecordGapTerm00458_eq_value :
    recordGapCenter - 419982 = fullRecordGapValue00458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00458 (fullRecordGapValue00458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00458_not_prime : ¬(recordGapCenter - 419982).Prime := by
  rw [fullRecordGapTerm00458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00458_fast_pow_mod_ne_one

def fullRecordGapValue00459 : Nat := fullRecordGapCenterValue - 419788

theorem fullRecordGapTerm00459_eq_value :
    recordGapCenter - 419788 = fullRecordGapValue00459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00459 (fullRecordGapValue00459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00459_not_prime : ¬(recordGapCenter - 419788).Prime := by
  rw [fullRecordGapTerm00459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00459_fast_pow_mod_ne_one

def fullRecordGapValue00460 : Nat := fullRecordGapCenterValue - 419674

theorem fullRecordGapTerm00460_eq_value :
    recordGapCenter - 419674 = fullRecordGapValue00460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00460 (fullRecordGapValue00460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00460_not_prime : ¬(recordGapCenter - 419674).Prime := by
  rw [fullRecordGapTerm00460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00460_fast_pow_mod_ne_one

def fullRecordGapValue00461 : Nat := fullRecordGapCenterValue - 419578

theorem fullRecordGapTerm00461_eq_value :
    recordGapCenter - 419578 = fullRecordGapValue00461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00461 (fullRecordGapValue00461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00461_not_prime : ¬(recordGapCenter - 419578).Prime := by
  rw [fullRecordGapTerm00461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00461_fast_pow_mod_ne_one

def fullRecordGapValue00462 : Nat := fullRecordGapCenterValue - 419464

theorem fullRecordGapTerm00462_eq_value :
    recordGapCenter - 419464 = fullRecordGapValue00462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00462 (fullRecordGapValue00462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00462_not_prime : ¬(recordGapCenter - 419464).Prime := by
  rw [fullRecordGapTerm00462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00462_fast_pow_mod_ne_one

def fullRecordGapValue00463 : Nat := fullRecordGapCenterValue - 419262

theorem fullRecordGapTerm00463_eq_value :
    recordGapCenter - 419262 = fullRecordGapValue00463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00463 (fullRecordGapValue00463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00463_not_prime : ¬(recordGapCenter - 419262).Prime := by
  rw [fullRecordGapTerm00463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00463_fast_pow_mod_ne_one

def fullRecordGapValue00464 : Nat := fullRecordGapCenterValue - 419194

theorem fullRecordGapTerm00464_eq_value :
    recordGapCenter - 419194 = fullRecordGapValue00464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00464 (fullRecordGapValue00464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00464_not_prime : ¬(recordGapCenter - 419194).Prime := by
  rw [fullRecordGapTerm00464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00464_fast_pow_mod_ne_one

def fullRecordGapValue00465 : Nat := fullRecordGapCenterValue - 419158

theorem fullRecordGapTerm00465_eq_value :
    recordGapCenter - 419158 = fullRecordGapValue00465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00465 (fullRecordGapValue00465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00465_not_prime : ¬(recordGapCenter - 419158).Prime := by
  rw [fullRecordGapTerm00465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00465_fast_pow_mod_ne_one

def fullRecordGapValue00466 : Nat := fullRecordGapCenterValue - 419142

theorem fullRecordGapTerm00466_eq_value :
    recordGapCenter - 419142 = fullRecordGapValue00466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00466 (fullRecordGapValue00466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00466_not_prime : ¬(recordGapCenter - 419142).Prime := by
  rw [fullRecordGapTerm00466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00466_fast_pow_mod_ne_one

def fullRecordGapValue00467 : Nat := fullRecordGapCenterValue - 419134

theorem fullRecordGapTerm00467_eq_value :
    recordGapCenter - 419134 = fullRecordGapValue00467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00467 (fullRecordGapValue00467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00467_not_prime : ¬(recordGapCenter - 419134).Prime := by
  rw [fullRecordGapTerm00467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00467_fast_pow_mod_ne_one

def fullRecordGapValue00468 : Nat := fullRecordGapCenterValue - 419092

theorem fullRecordGapTerm00468_eq_value :
    recordGapCenter - 419092 = fullRecordGapValue00468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00468 (fullRecordGapValue00468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00468_not_prime : ¬(recordGapCenter - 419092).Prime := by
  rw [fullRecordGapTerm00468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00468_fast_pow_mod_ne_one

def fullRecordGapValue00469 : Nat := fullRecordGapCenterValue - 419032

theorem fullRecordGapTerm00469_eq_value :
    recordGapCenter - 419032 = fullRecordGapValue00469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00469 (fullRecordGapValue00469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00469_not_prime : ¬(recordGapCenter - 419032).Prime := by
  rw [fullRecordGapTerm00469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00469_fast_pow_mod_ne_one

def fullRecordGapValue00470 : Nat := fullRecordGapCenterValue - 418974

theorem fullRecordGapTerm00470_eq_value :
    recordGapCenter - 418974 = fullRecordGapValue00470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00470 (fullRecordGapValue00470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00470_not_prime : ¬(recordGapCenter - 418974).Prime := by
  rw [fullRecordGapTerm00470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00470_fast_pow_mod_ne_one

def fullRecordGapValue00471 : Nat := fullRecordGapCenterValue - 418962

theorem fullRecordGapTerm00471_eq_value :
    recordGapCenter - 418962 = fullRecordGapValue00471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00471 (fullRecordGapValue00471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00471_not_prime : ¬(recordGapCenter - 418962).Prime := by
  rw [fullRecordGapTerm00471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00471_fast_pow_mod_ne_one

def fullRecordGapValue00472 : Nat := fullRecordGapCenterValue - 418942

theorem fullRecordGapTerm00472_eq_value :
    recordGapCenter - 418942 = fullRecordGapValue00472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00472 (fullRecordGapValue00472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00472_not_prime : ¬(recordGapCenter - 418942).Prime := by
  rw [fullRecordGapTerm00472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00472_fast_pow_mod_ne_one

def fullRecordGapValue00473 : Nat := fullRecordGapCenterValue - 418918

theorem fullRecordGapTerm00473_eq_value :
    recordGapCenter - 418918 = fullRecordGapValue00473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00473 (fullRecordGapValue00473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00473_not_prime : ¬(recordGapCenter - 418918).Prime := by
  rw [fullRecordGapTerm00473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00473_fast_pow_mod_ne_one

def fullRecordGapValue00474 : Nat := fullRecordGapCenterValue - 418732

theorem fullRecordGapTerm00474_eq_value :
    recordGapCenter - 418732 = fullRecordGapValue00474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00474 (fullRecordGapValue00474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00474_not_prime : ¬(recordGapCenter - 418732).Prime := by
  rw [fullRecordGapTerm00474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00474_fast_pow_mod_ne_one

def fullRecordGapValue00475 : Nat := fullRecordGapCenterValue - 418714

theorem fullRecordGapTerm00475_eq_value :
    recordGapCenter - 418714 = fullRecordGapValue00475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00475 (fullRecordGapValue00475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00475_not_prime : ¬(recordGapCenter - 418714).Prime := by
  rw [fullRecordGapTerm00475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00475_fast_pow_mod_ne_one

def fullRecordGapValue00476 : Nat := fullRecordGapCenterValue - 418504

theorem fullRecordGapTerm00476_eq_value :
    recordGapCenter - 418504 = fullRecordGapValue00476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00476 (fullRecordGapValue00476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00476_not_prime : ¬(recordGapCenter - 418504).Prime := by
  rw [fullRecordGapTerm00476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00476_fast_pow_mod_ne_one

def fullRecordGapValue00477 : Nat := fullRecordGapCenterValue - 418408

theorem fullRecordGapTerm00477_eq_value :
    recordGapCenter - 418408 = fullRecordGapValue00477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00477 (fullRecordGapValue00477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00477_not_prime : ¬(recordGapCenter - 418408).Prime := by
  rw [fullRecordGapTerm00477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00477_fast_pow_mod_ne_one

def fullRecordGapValue00478 : Nat := fullRecordGapCenterValue - 418402

theorem fullRecordGapTerm00478_eq_value :
    recordGapCenter - 418402 = fullRecordGapValue00478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00478 (fullRecordGapValue00478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00478_not_prime : ¬(recordGapCenter - 418402).Prime := by
  rw [fullRecordGapTerm00478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00478_fast_pow_mod_ne_one

def fullRecordGapValue00479 : Nat := fullRecordGapCenterValue - 418372

theorem fullRecordGapTerm00479_eq_value :
    recordGapCenter - 418372 = fullRecordGapValue00479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00479 (fullRecordGapValue00479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00479_not_prime : ¬(recordGapCenter - 418372).Prime := by
  rw [fullRecordGapTerm00479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00479_fast_pow_mod_ne_one

def fullRecordGapValue00480 : Nat := fullRecordGapCenterValue - 418108

theorem fullRecordGapTerm00480_eq_value :
    recordGapCenter - 418108 = fullRecordGapValue00480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00480 (fullRecordGapValue00480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00480_not_prime : ¬(recordGapCenter - 418108).Prime := by
  rw [fullRecordGapTerm00480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00480_fast_pow_mod_ne_one

def fullRecordGapValue00481 : Nat := fullRecordGapCenterValue - 418024

theorem fullRecordGapTerm00481_eq_value :
    recordGapCenter - 418024 = fullRecordGapValue00481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00481 (fullRecordGapValue00481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00481_not_prime : ¬(recordGapCenter - 418024).Prime := by
  rw [fullRecordGapTerm00481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00481_fast_pow_mod_ne_one

def fullRecordGapValue00482 : Nat := fullRecordGapCenterValue - 417892

theorem fullRecordGapTerm00482_eq_value :
    recordGapCenter - 417892 = fullRecordGapValue00482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00482 (fullRecordGapValue00482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00482_not_prime : ¬(recordGapCenter - 417892).Prime := by
  rw [fullRecordGapTerm00482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00482_fast_pow_mod_ne_one

def fullRecordGapValue00483 : Nat := fullRecordGapCenterValue - 417778

theorem fullRecordGapTerm00483_eq_value :
    recordGapCenter - 417778 = fullRecordGapValue00483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00483 (fullRecordGapValue00483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00483_not_prime : ¬(recordGapCenter - 417778).Prime := by
  rw [fullRecordGapTerm00483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00483_fast_pow_mod_ne_one

def fullRecordGapValue00484 : Nat := fullRecordGapCenterValue - 417598

theorem fullRecordGapTerm00484_eq_value :
    recordGapCenter - 417598 = fullRecordGapValue00484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00484 (fullRecordGapValue00484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00484_not_prime : ¬(recordGapCenter - 417598).Prime := by
  rw [fullRecordGapTerm00484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00484_fast_pow_mod_ne_one

def fullRecordGapValue00485 : Nat := fullRecordGapCenterValue - 417532

theorem fullRecordGapTerm00485_eq_value :
    recordGapCenter - 417532 = fullRecordGapValue00485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00485 (fullRecordGapValue00485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00485_not_prime : ¬(recordGapCenter - 417532).Prime := by
  rw [fullRecordGapTerm00485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00485_fast_pow_mod_ne_one

def fullRecordGapValue00486 : Nat := fullRecordGapCenterValue - 417442

theorem fullRecordGapTerm00486_eq_value :
    recordGapCenter - 417442 = fullRecordGapValue00486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00486 (fullRecordGapValue00486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00486_not_prime : ¬(recordGapCenter - 417442).Prime := by
  rw [fullRecordGapTerm00486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00486_fast_pow_mod_ne_one

def fullRecordGapValue00487 : Nat := fullRecordGapCenterValue - 417244

theorem fullRecordGapTerm00487_eq_value :
    recordGapCenter - 417244 = fullRecordGapValue00487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00487 (fullRecordGapValue00487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00487_not_prime : ¬(recordGapCenter - 417244).Prime := by
  rw [fullRecordGapTerm00487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00487_fast_pow_mod_ne_one

def fullRecordGapValue00488 : Nat := fullRecordGapCenterValue - 417022

theorem fullRecordGapTerm00488_eq_value :
    recordGapCenter - 417022 = fullRecordGapValue00488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00488 (fullRecordGapValue00488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00488_not_prime : ¬(recordGapCenter - 417022).Prime := by
  rw [fullRecordGapTerm00488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00488_fast_pow_mod_ne_one

def fullRecordGapValue00489 : Nat := fullRecordGapCenterValue - 416994

theorem fullRecordGapTerm00489_eq_value :
    recordGapCenter - 416994 = fullRecordGapValue00489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00489 (fullRecordGapValue00489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00489_not_prime : ¬(recordGapCenter - 416994).Prime := by
  rw [fullRecordGapTerm00489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00489_fast_pow_mod_ne_one

def fullRecordGapValue00490 : Nat := fullRecordGapCenterValue - 416824

theorem fullRecordGapTerm00490_eq_value :
    recordGapCenter - 416824 = fullRecordGapValue00490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00490 (fullRecordGapValue00490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00490_not_prime : ¬(recordGapCenter - 416824).Prime := by
  rw [fullRecordGapTerm00490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00490_fast_pow_mod_ne_one

def fullRecordGapValue00491 : Nat := fullRecordGapCenterValue - 416818

theorem fullRecordGapTerm00491_eq_value :
    recordGapCenter - 416818 = fullRecordGapValue00491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00491 (fullRecordGapValue00491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00491_not_prime : ¬(recordGapCenter - 416818).Prime := by
  rw [fullRecordGapTerm00491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00491_fast_pow_mod_ne_one

def fullRecordGapValue00492 : Nat := fullRecordGapCenterValue - 416758

theorem fullRecordGapTerm00492_eq_value :
    recordGapCenter - 416758 = fullRecordGapValue00492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00492 (fullRecordGapValue00492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00492_not_prime : ¬(recordGapCenter - 416758).Prime := by
  rw [fullRecordGapTerm00492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00492_fast_pow_mod_ne_one

def fullRecordGapValue00493 : Nat := fullRecordGapCenterValue - 416742

theorem fullRecordGapTerm00493_eq_value :
    recordGapCenter - 416742 = fullRecordGapValue00493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00493 (fullRecordGapValue00493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00493_not_prime : ¬(recordGapCenter - 416742).Prime := by
  rw [fullRecordGapTerm00493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00493_fast_pow_mod_ne_one

def fullRecordGapValue00494 : Nat := fullRecordGapCenterValue - 416562

theorem fullRecordGapTerm00494_eq_value :
    recordGapCenter - 416562 = fullRecordGapValue00494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00494 (fullRecordGapValue00494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00494_not_prime : ¬(recordGapCenter - 416562).Prime := by
  rw [fullRecordGapTerm00494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00494_fast_pow_mod_ne_one

def fullRecordGapValue00495 : Nat := fullRecordGapCenterValue - 416554

theorem fullRecordGapTerm00495_eq_value :
    recordGapCenter - 416554 = fullRecordGapValue00495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00495 (fullRecordGapValue00495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00495_not_prime : ¬(recordGapCenter - 416554).Prime := by
  rw [fullRecordGapTerm00495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00495_fast_pow_mod_ne_one

def fullRecordGapValue00496 : Nat := fullRecordGapCenterValue - 416434

theorem fullRecordGapTerm00496_eq_value :
    recordGapCenter - 416434 = fullRecordGapValue00496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00496 (fullRecordGapValue00496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00496_not_prime : ¬(recordGapCenter - 416434).Prime := by
  rw [fullRecordGapTerm00496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00496_fast_pow_mod_ne_one

def fullRecordGapValue00497 : Nat := fullRecordGapCenterValue - 416418

theorem fullRecordGapTerm00497_eq_value :
    recordGapCenter - 416418 = fullRecordGapValue00497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00497 (fullRecordGapValue00497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00497_not_prime : ¬(recordGapCenter - 416418).Prime := by
  rw [fullRecordGapTerm00497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00497_fast_pow_mod_ne_one

def fullRecordGapValue00498 : Nat := fullRecordGapCenterValue - 416334

theorem fullRecordGapTerm00498_eq_value :
    recordGapCenter - 416334 = fullRecordGapValue00498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00498 (fullRecordGapValue00498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00498_not_prime : ¬(recordGapCenter - 416334).Prime := by
  rw [fullRecordGapTerm00498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00498_fast_pow_mod_ne_one

def fullRecordGapValue00499 : Nat := fullRecordGapCenterValue - 416212

theorem fullRecordGapTerm00499_eq_value :
    recordGapCenter - 416212 = fullRecordGapValue00499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00499 (fullRecordGapValue00499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00499_not_prime : ¬(recordGapCenter - 416212).Prime := by
  rw [fullRecordGapTerm00499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00499_fast_pow_mod_ne_one

def fullRecordGapValue00500 : Nat := fullRecordGapCenterValue - 416022

theorem fullRecordGapTerm00500_eq_value :
    recordGapCenter - 416022 = fullRecordGapValue00500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00500 (fullRecordGapValue00500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00500_not_prime : ¬(recordGapCenter - 416022).Prime := by
  rw [fullRecordGapTerm00500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00500_fast_pow_mod_ne_one

def fullRecordGapValue00501 : Nat := fullRecordGapCenterValue - 415942

theorem fullRecordGapTerm00501_eq_value :
    recordGapCenter - 415942 = fullRecordGapValue00501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00501 (fullRecordGapValue00501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00501_not_prime : ¬(recordGapCenter - 415942).Prime := by
  rw [fullRecordGapTerm00501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00501_fast_pow_mod_ne_one

def fullRecordGapValue00502 : Nat := fullRecordGapCenterValue - 415924

theorem fullRecordGapTerm00502_eq_value :
    recordGapCenter - 415924 = fullRecordGapValue00502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00502 (fullRecordGapValue00502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00502_not_prime : ¬(recordGapCenter - 415924).Prime := by
  rw [fullRecordGapTerm00502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00502_fast_pow_mod_ne_one

def fullRecordGapValue00503 : Nat := fullRecordGapCenterValue - 415894

theorem fullRecordGapTerm00503_eq_value :
    recordGapCenter - 415894 = fullRecordGapValue00503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00503 (fullRecordGapValue00503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00503_not_prime : ¬(recordGapCenter - 415894).Prime := by
  rw [fullRecordGapTerm00503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00503_fast_pow_mod_ne_one

def fullRecordGapValue00504 : Nat := fullRecordGapCenterValue - 415800

theorem fullRecordGapTerm00504_eq_value :
    recordGapCenter - 415800 = fullRecordGapValue00504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00504 (fullRecordGapValue00504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00504_not_prime : ¬(recordGapCenter - 415800).Prime := by
  rw [fullRecordGapTerm00504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00504_fast_pow_mod_ne_one

def fullRecordGapValue00505 : Nat := fullRecordGapCenterValue - 415768

theorem fullRecordGapTerm00505_eq_value :
    recordGapCenter - 415768 = fullRecordGapValue00505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00505 (fullRecordGapValue00505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00505_not_prime : ¬(recordGapCenter - 415768).Prime := by
  rw [fullRecordGapTerm00505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00505_fast_pow_mod_ne_one

def fullRecordGapValue00506 : Nat := fullRecordGapCenterValue - 415594

theorem fullRecordGapTerm00506_eq_value :
    recordGapCenter - 415594 = fullRecordGapValue00506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00506 (fullRecordGapValue00506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00506_not_prime : ¬(recordGapCenter - 415594).Prime := by
  rw [fullRecordGapTerm00506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00506_fast_pow_mod_ne_one

def fullRecordGapValue00507 : Nat := fullRecordGapCenterValue - 415468

theorem fullRecordGapTerm00507_eq_value :
    recordGapCenter - 415468 = fullRecordGapValue00507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00507 (fullRecordGapValue00507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00507_not_prime : ¬(recordGapCenter - 415468).Prime := by
  rw [fullRecordGapTerm00507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00507_fast_pow_mod_ne_one

def fullRecordGapValue00508 : Nat := fullRecordGapCenterValue - 415434

theorem fullRecordGapTerm00508_eq_value :
    recordGapCenter - 415434 = fullRecordGapValue00508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00508 (fullRecordGapValue00508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00508_not_prime : ¬(recordGapCenter - 415434).Prime := by
  rw [fullRecordGapTerm00508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00508_fast_pow_mod_ne_one

def fullRecordGapValue00509 : Nat := fullRecordGapCenterValue - 415432

theorem fullRecordGapTerm00509_eq_value :
    recordGapCenter - 415432 = fullRecordGapValue00509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00509 (fullRecordGapValue00509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00509_not_prime : ¬(recordGapCenter - 415432).Prime := by
  rw [fullRecordGapTerm00509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00509_fast_pow_mod_ne_one

def fullRecordGapValue00510 : Nat := fullRecordGapCenterValue - 415258

theorem fullRecordGapTerm00510_eq_value :
    recordGapCenter - 415258 = fullRecordGapValue00510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00510 (fullRecordGapValue00510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00510_not_prime : ¬(recordGapCenter - 415258).Prime := by
  rw [fullRecordGapTerm00510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00510_fast_pow_mod_ne_one

def fullRecordGapValue00511 : Nat := fullRecordGapCenterValue - 415204

theorem fullRecordGapTerm00511_eq_value :
    recordGapCenter - 415204 = fullRecordGapValue00511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00511 (fullRecordGapValue00511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00511_not_prime : ¬(recordGapCenter - 415204).Prime := by
  rw [fullRecordGapTerm00511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00511_fast_pow_mod_ne_one

def fullRecordGapValue00512 : Nat := fullRecordGapCenterValue - 414978

theorem fullRecordGapTerm00512_eq_value :
    recordGapCenter - 414978 = fullRecordGapValue00512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00512 (fullRecordGapValue00512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00512_not_prime : ¬(recordGapCenter - 414978).Prime := by
  rw [fullRecordGapTerm00512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00512_fast_pow_mod_ne_one

end PrimeFactorUnimodality
