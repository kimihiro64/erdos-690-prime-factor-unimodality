import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue08449 : Nat := fullRecordGapCenterValue + 502616

theorem fullRecordGapTerm08449_eq_value :
    recordGapCenter + 502616 = fullRecordGapValue08449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08449 (fullRecordGapValue08449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08449_not_prime : ¬(recordGapCenter + 502616).Prime := by
  rw [fullRecordGapTerm08449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08449_fast_pow_mod_ne_one

def fullRecordGapValue08450 : Nat := fullRecordGapCenterValue + 502638

theorem fullRecordGapTerm08450_eq_value :
    recordGapCenter + 502638 = fullRecordGapValue08450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08450 (fullRecordGapValue08450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08450_not_prime : ¬(recordGapCenter + 502638).Prime := by
  rw [fullRecordGapTerm08450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08450_fast_pow_mod_ne_one

def fullRecordGapValue08451 : Nat := fullRecordGapCenterValue + 502730

theorem fullRecordGapTerm08451_eq_value :
    recordGapCenter + 502730 = fullRecordGapValue08451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08451 (fullRecordGapValue08451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08451_not_prime : ¬(recordGapCenter + 502730).Prime := by
  rw [fullRecordGapTerm08451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08451_fast_pow_mod_ne_one

def fullRecordGapValue08452 : Nat := fullRecordGapCenterValue + 502772

theorem fullRecordGapTerm08452_eq_value :
    recordGapCenter + 502772 = fullRecordGapValue08452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08452 (fullRecordGapValue08452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08452_not_prime : ¬(recordGapCenter + 502772).Prime := by
  rw [fullRecordGapTerm08452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08452_fast_pow_mod_ne_one

def fullRecordGapValue08453 : Nat := fullRecordGapCenterValue + 502910

theorem fullRecordGapTerm08453_eq_value :
    recordGapCenter + 502910 = fullRecordGapValue08453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08453 (fullRecordGapValue08453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08453_not_prime : ¬(recordGapCenter + 502910).Prime := by
  rw [fullRecordGapTerm08453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08453_fast_pow_mod_ne_one

def fullRecordGapValue08454 : Nat := fullRecordGapCenterValue + 502946

theorem fullRecordGapTerm08454_eq_value :
    recordGapCenter + 502946 = fullRecordGapValue08454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08454 (fullRecordGapValue08454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08454_not_prime : ¬(recordGapCenter + 502946).Prime := by
  rw [fullRecordGapTerm08454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08454_fast_pow_mod_ne_one

def fullRecordGapValue08455 : Nat := fullRecordGapCenterValue + 503066

theorem fullRecordGapTerm08455_eq_value :
    recordGapCenter + 503066 = fullRecordGapValue08455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08455 (fullRecordGapValue08455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08455_not_prime : ¬(recordGapCenter + 503066).Prime := by
  rw [fullRecordGapTerm08455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08455_fast_pow_mod_ne_one

def fullRecordGapValue08456 : Nat := fullRecordGapCenterValue + 503156

theorem fullRecordGapTerm08456_eq_value :
    recordGapCenter + 503156 = fullRecordGapValue08456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08456 (fullRecordGapValue08456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08456_not_prime : ¬(recordGapCenter + 503156).Prime := by
  rw [fullRecordGapTerm08456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08456_fast_pow_mod_ne_one

def fullRecordGapValue08457 : Nat := fullRecordGapCenterValue + 503252

theorem fullRecordGapTerm08457_eq_value :
    recordGapCenter + 503252 = fullRecordGapValue08457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08457 (fullRecordGapValue08457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08457_not_prime : ¬(recordGapCenter + 503252).Prime := by
  rw [fullRecordGapTerm08457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08457_fast_pow_mod_ne_one

def fullRecordGapValue08458 : Nat := fullRecordGapCenterValue + 503330

theorem fullRecordGapTerm08458_eq_value :
    recordGapCenter + 503330 = fullRecordGapValue08458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08458 (fullRecordGapValue08458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08458_not_prime : ¬(recordGapCenter + 503330).Prime := by
  rw [fullRecordGapTerm08458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08458_fast_pow_mod_ne_one

def fullRecordGapValue08459 : Nat := fullRecordGapCenterValue + 503402

theorem fullRecordGapTerm08459_eq_value :
    recordGapCenter + 503402 = fullRecordGapValue08459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08459 (fullRecordGapValue08459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08459_not_prime : ¬(recordGapCenter + 503402).Prime := by
  rw [fullRecordGapTerm08459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08459_fast_pow_mod_ne_one

def fullRecordGapValue08460 : Nat := fullRecordGapCenterValue + 503522

theorem fullRecordGapTerm08460_eq_value :
    recordGapCenter + 503522 = fullRecordGapValue08460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08460 (fullRecordGapValue08460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08460_not_prime : ¬(recordGapCenter + 503522).Prime := by
  rw [fullRecordGapTerm08460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08460_fast_pow_mod_ne_one

def fullRecordGapValue08461 : Nat := fullRecordGapCenterValue + 503582

theorem fullRecordGapTerm08461_eq_value :
    recordGapCenter + 503582 = fullRecordGapValue08461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08461 (fullRecordGapValue08461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08461_not_prime : ¬(recordGapCenter + 503582).Prime := by
  rw [fullRecordGapTerm08461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08461_fast_pow_mod_ne_one

def fullRecordGapValue08462 : Nat := fullRecordGapCenterValue + 503618

theorem fullRecordGapTerm08462_eq_value :
    recordGapCenter + 503618 = fullRecordGapValue08462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08462 (fullRecordGapValue08462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08462_not_prime : ¬(recordGapCenter + 503618).Prime := by
  rw [fullRecordGapTerm08462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08462_fast_pow_mod_ne_one

def fullRecordGapValue08463 : Nat := fullRecordGapCenterValue + 503732

theorem fullRecordGapTerm08463_eq_value :
    recordGapCenter + 503732 = fullRecordGapValue08463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08463 (fullRecordGapValue08463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08463_not_prime : ¬(recordGapCenter + 503732).Prime := by
  rw [fullRecordGapTerm08463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08463_fast_pow_mod_ne_one

def fullRecordGapValue08464 : Nat := fullRecordGapCenterValue + 503870

theorem fullRecordGapTerm08464_eq_value :
    recordGapCenter + 503870 = fullRecordGapValue08464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08464 (fullRecordGapValue08464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08464_not_prime : ¬(recordGapCenter + 503870).Prime := by
  rw [fullRecordGapTerm08464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08464_fast_pow_mod_ne_one

def fullRecordGapValue08465 : Nat := fullRecordGapCenterValue + 503912

theorem fullRecordGapTerm08465_eq_value :
    recordGapCenter + 503912 = fullRecordGapValue08465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08465 (fullRecordGapValue08465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08465_not_prime : ¬(recordGapCenter + 503912).Prime := by
  rw [fullRecordGapTerm08465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08465_fast_pow_mod_ne_one

def fullRecordGapValue08466 : Nat := fullRecordGapCenterValue + 504000

theorem fullRecordGapTerm08466_eq_value :
    recordGapCenter + 504000 = fullRecordGapValue08466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08466 (fullRecordGapValue08466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08466_not_prime : ¬(recordGapCenter + 504000).Prime := by
  rw [fullRecordGapTerm08466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08466_fast_pow_mod_ne_one

def fullRecordGapValue08467 : Nat := fullRecordGapCenterValue + 504002

theorem fullRecordGapTerm08467_eq_value :
    recordGapCenter + 504002 = fullRecordGapValue08467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08467 (fullRecordGapValue08467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08467_not_prime : ¬(recordGapCenter + 504002).Prime := by
  rw [fullRecordGapTerm08467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08467_fast_pow_mod_ne_one

def fullRecordGapValue08468 : Nat := fullRecordGapCenterValue + 504026

theorem fullRecordGapTerm08468_eq_value :
    recordGapCenter + 504026 = fullRecordGapValue08468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08468 (fullRecordGapValue08468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08468_not_prime : ¬(recordGapCenter + 504026).Prime := by
  rw [fullRecordGapTerm08468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08468_fast_pow_mod_ne_one

def fullRecordGapValue08469 : Nat := fullRecordGapCenterValue + 504210

theorem fullRecordGapTerm08469_eq_value :
    recordGapCenter + 504210 = fullRecordGapValue08469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08469 (fullRecordGapValue08469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08469_not_prime : ¬(recordGapCenter + 504210).Prime := by
  rw [fullRecordGapTerm08469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08469_fast_pow_mod_ne_one

def fullRecordGapValue08470 : Nat := fullRecordGapCenterValue + 504318

theorem fullRecordGapTerm08470_eq_value :
    recordGapCenter + 504318 = fullRecordGapValue08470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08470 (fullRecordGapValue08470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08470_not_prime : ¬(recordGapCenter + 504318).Prime := by
  rw [fullRecordGapTerm08470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08470_fast_pow_mod_ne_one

def fullRecordGapValue08471 : Nat := fullRecordGapCenterValue + 504326

theorem fullRecordGapTerm08471_eq_value :
    recordGapCenter + 504326 = fullRecordGapValue08471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08471 (fullRecordGapValue08471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08471_not_prime : ¬(recordGapCenter + 504326).Prime := by
  rw [fullRecordGapTerm08471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08471_fast_pow_mod_ne_one

def fullRecordGapValue08472 : Nat := fullRecordGapCenterValue + 504338

theorem fullRecordGapTerm08472_eq_value :
    recordGapCenter + 504338 = fullRecordGapValue08472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08472 (fullRecordGapValue08472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08472_not_prime : ¬(recordGapCenter + 504338).Prime := by
  rw [fullRecordGapTerm08472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08472_fast_pow_mod_ne_one

def fullRecordGapValue08473 : Nat := fullRecordGapCenterValue + 504362

theorem fullRecordGapTerm08473_eq_value :
    recordGapCenter + 504362 = fullRecordGapValue08473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08473 (fullRecordGapValue08473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08473_not_prime : ¬(recordGapCenter + 504362).Prime := by
  rw [fullRecordGapTerm08473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08473_fast_pow_mod_ne_one

def fullRecordGapValue08474 : Nat := fullRecordGapCenterValue + 504386

theorem fullRecordGapTerm08474_eq_value :
    recordGapCenter + 504386 = fullRecordGapValue08474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08474 (fullRecordGapValue08474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08474_not_prime : ¬(recordGapCenter + 504386).Prime := by
  rw [fullRecordGapTerm08474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08474_fast_pow_mod_ne_one

def fullRecordGapValue08475 : Nat := fullRecordGapCenterValue + 504402

theorem fullRecordGapTerm08475_eq_value :
    recordGapCenter + 504402 = fullRecordGapValue08475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08475 (fullRecordGapValue08475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08475_not_prime : ¬(recordGapCenter + 504402).Prime := by
  rw [fullRecordGapTerm08475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08475_fast_pow_mod_ne_one

def fullRecordGapValue08476 : Nat := fullRecordGapCenterValue + 504726

theorem fullRecordGapTerm08476_eq_value :
    recordGapCenter + 504726 = fullRecordGapValue08476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08476 (fullRecordGapValue08476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08476_not_prime : ¬(recordGapCenter + 504726).Prime := by
  rw [fullRecordGapTerm08476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08476_fast_pow_mod_ne_one

def fullRecordGapValue08477 : Nat := fullRecordGapCenterValue + 504782

theorem fullRecordGapTerm08477_eq_value :
    recordGapCenter + 504782 = fullRecordGapValue08477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08477 (fullRecordGapValue08477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08477_not_prime : ¬(recordGapCenter + 504782).Prime := by
  rw [fullRecordGapTerm08477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08477_fast_pow_mod_ne_one

def fullRecordGapValue08478 : Nat := fullRecordGapCenterValue + 504908

theorem fullRecordGapTerm08478_eq_value :
    recordGapCenter + 504908 = fullRecordGapValue08478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08478 (fullRecordGapValue08478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08478_not_prime : ¬(recordGapCenter + 504908).Prime := by
  rw [fullRecordGapTerm08478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08478_fast_pow_mod_ne_one

def fullRecordGapValue08479 : Nat := fullRecordGapCenterValue + 504932

theorem fullRecordGapTerm08479_eq_value :
    recordGapCenter + 504932 = fullRecordGapValue08479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08479 (fullRecordGapValue08479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08479_not_prime : ¬(recordGapCenter + 504932).Prime := by
  rw [fullRecordGapTerm08479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08479_fast_pow_mod_ne_one

def fullRecordGapValue08480 : Nat := fullRecordGapCenterValue + 504978

theorem fullRecordGapTerm08480_eq_value :
    recordGapCenter + 504978 = fullRecordGapValue08480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08480 (fullRecordGapValue08480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08480_not_prime : ¬(recordGapCenter + 504978).Prime := by
  rw [fullRecordGapTerm08480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08480_fast_pow_mod_ne_one

def fullRecordGapValue08481 : Nat := fullRecordGapCenterValue + 505016

theorem fullRecordGapTerm08481_eq_value :
    recordGapCenter + 505016 = fullRecordGapValue08481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08481 (fullRecordGapValue08481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08481_not_prime : ¬(recordGapCenter + 505016).Prime := by
  rw [fullRecordGapTerm08481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08481_fast_pow_mod_ne_one

def fullRecordGapValue08482 : Nat := fullRecordGapCenterValue + 505082

theorem fullRecordGapTerm08482_eq_value :
    recordGapCenter + 505082 = fullRecordGapValue08482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08482 (fullRecordGapValue08482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08482_not_prime : ¬(recordGapCenter + 505082).Prime := by
  rw [fullRecordGapTerm08482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08482_fast_pow_mod_ne_one

def fullRecordGapValue08483 : Nat := fullRecordGapCenterValue + 505086

theorem fullRecordGapTerm08483_eq_value :
    recordGapCenter + 505086 = fullRecordGapValue08483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08483 (fullRecordGapValue08483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08483_not_prime : ¬(recordGapCenter + 505086).Prime := by
  rw [fullRecordGapTerm08483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08483_fast_pow_mod_ne_one

def fullRecordGapValue08484 : Nat := fullRecordGapCenterValue + 505130

theorem fullRecordGapTerm08484_eq_value :
    recordGapCenter + 505130 = fullRecordGapValue08484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08484 (fullRecordGapValue08484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08484_not_prime : ¬(recordGapCenter + 505130).Prime := by
  rw [fullRecordGapTerm08484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08484_fast_pow_mod_ne_one

def fullRecordGapValue08485 : Nat := fullRecordGapCenterValue + 505166

theorem fullRecordGapTerm08485_eq_value :
    recordGapCenter + 505166 = fullRecordGapValue08485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08485 (fullRecordGapValue08485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08485_not_prime : ¬(recordGapCenter + 505166).Prime := by
  rw [fullRecordGapTerm08485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08485_fast_pow_mod_ne_one

def fullRecordGapValue08486 : Nat := fullRecordGapCenterValue + 505178

theorem fullRecordGapTerm08486_eq_value :
    recordGapCenter + 505178 = fullRecordGapValue08486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08486 (fullRecordGapValue08486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08486_not_prime : ¬(recordGapCenter + 505178).Prime := by
  rw [fullRecordGapTerm08486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08486_fast_pow_mod_ne_one

def fullRecordGapValue08487 : Nat := fullRecordGapCenterValue + 505418

theorem fullRecordGapTerm08487_eq_value :
    recordGapCenter + 505418 = fullRecordGapValue08487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08487 (fullRecordGapValue08487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08487_not_prime : ¬(recordGapCenter + 505418).Prime := by
  rw [fullRecordGapTerm08487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08487_fast_pow_mod_ne_one

def fullRecordGapValue08488 : Nat := fullRecordGapCenterValue + 505482

theorem fullRecordGapTerm08488_eq_value :
    recordGapCenter + 505482 = fullRecordGapValue08488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08488 (fullRecordGapValue08488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08488_not_prime : ¬(recordGapCenter + 505482).Prime := by
  rw [fullRecordGapTerm08488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08488_fast_pow_mod_ne_one

def fullRecordGapValue08489 : Nat := fullRecordGapCenterValue + 505646

theorem fullRecordGapTerm08489_eq_value :
    recordGapCenter + 505646 = fullRecordGapValue08489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08489 (fullRecordGapValue08489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08489_not_prime : ¬(recordGapCenter + 505646).Prime := by
  rw [fullRecordGapTerm08489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08489_fast_pow_mod_ne_one

def fullRecordGapValue08490 : Nat := fullRecordGapCenterValue + 505772

theorem fullRecordGapTerm08490_eq_value :
    recordGapCenter + 505772 = fullRecordGapValue08490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08490 (fullRecordGapValue08490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08490_not_prime : ¬(recordGapCenter + 505772).Prime := by
  rw [fullRecordGapTerm08490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08490_fast_pow_mod_ne_one

def fullRecordGapValue08491 : Nat := fullRecordGapCenterValue + 505838

theorem fullRecordGapTerm08491_eq_value :
    recordGapCenter + 505838 = fullRecordGapValue08491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08491 (fullRecordGapValue08491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08491_not_prime : ¬(recordGapCenter + 505838).Prime := by
  rw [fullRecordGapTerm08491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08491_fast_pow_mod_ne_one

def fullRecordGapValue08492 : Nat := fullRecordGapCenterValue + 505902

theorem fullRecordGapTerm08492_eq_value :
    recordGapCenter + 505902 = fullRecordGapValue08492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08492 (fullRecordGapValue08492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08492_not_prime : ¬(recordGapCenter + 505902).Prime := by
  rw [fullRecordGapTerm08492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08492_fast_pow_mod_ne_one

def fullRecordGapValue08493 : Nat := fullRecordGapCenterValue + 505928

theorem fullRecordGapTerm08493_eq_value :
    recordGapCenter + 505928 = fullRecordGapValue08493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08493 (fullRecordGapValue08493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08493_not_prime : ¬(recordGapCenter + 505928).Prime := by
  rw [fullRecordGapTerm08493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08493_fast_pow_mod_ne_one

def fullRecordGapValue08494 : Nat := fullRecordGapCenterValue + 505958

theorem fullRecordGapTerm08494_eq_value :
    recordGapCenter + 505958 = fullRecordGapValue08494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08494 (fullRecordGapValue08494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08494_not_prime : ¬(recordGapCenter + 505958).Prime := by
  rw [fullRecordGapTerm08494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08494_fast_pow_mod_ne_one

def fullRecordGapValue08495 : Nat := fullRecordGapCenterValue + 505976

theorem fullRecordGapTerm08495_eq_value :
    recordGapCenter + 505976 = fullRecordGapValue08495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08495 (fullRecordGapValue08495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08495_not_prime : ¬(recordGapCenter + 505976).Prime := by
  rw [fullRecordGapTerm08495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08495_fast_pow_mod_ne_one

def fullRecordGapValue08496 : Nat := fullRecordGapCenterValue + 506082

theorem fullRecordGapTerm08496_eq_value :
    recordGapCenter + 506082 = fullRecordGapValue08496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08496 (fullRecordGapValue08496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08496_not_prime : ¬(recordGapCenter + 506082).Prime := by
  rw [fullRecordGapTerm08496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08496_fast_pow_mod_ne_one

def fullRecordGapValue08497 : Nat := fullRecordGapCenterValue + 506126

theorem fullRecordGapTerm08497_eq_value :
    recordGapCenter + 506126 = fullRecordGapValue08497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08497 (fullRecordGapValue08497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08497_not_prime : ¬(recordGapCenter + 506126).Prime := by
  rw [fullRecordGapTerm08497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08497_fast_pow_mod_ne_one

def fullRecordGapValue08498 : Nat := fullRecordGapCenterValue + 506250

theorem fullRecordGapTerm08498_eq_value :
    recordGapCenter + 506250 = fullRecordGapValue08498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08498 (fullRecordGapValue08498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08498_not_prime : ¬(recordGapCenter + 506250).Prime := by
  rw [fullRecordGapTerm08498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08498_fast_pow_mod_ne_one

def fullRecordGapValue08499 : Nat := fullRecordGapCenterValue + 506270

theorem fullRecordGapTerm08499_eq_value :
    recordGapCenter + 506270 = fullRecordGapValue08499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08499 (fullRecordGapValue08499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08499_not_prime : ¬(recordGapCenter + 506270).Prime := by
  rw [fullRecordGapTerm08499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08499_fast_pow_mod_ne_one

def fullRecordGapValue08500 : Nat := fullRecordGapCenterValue + 506318

theorem fullRecordGapTerm08500_eq_value :
    recordGapCenter + 506318 = fullRecordGapValue08500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08500 (fullRecordGapValue08500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08500_not_prime : ¬(recordGapCenter + 506318).Prime := by
  rw [fullRecordGapTerm08500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08500_fast_pow_mod_ne_one

def fullRecordGapValue08501 : Nat := fullRecordGapCenterValue + 506406

theorem fullRecordGapTerm08501_eq_value :
    recordGapCenter + 506406 = fullRecordGapValue08501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08501 (fullRecordGapValue08501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08501_not_prime : ¬(recordGapCenter + 506406).Prime := by
  rw [fullRecordGapTerm08501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08501_fast_pow_mod_ne_one

def fullRecordGapValue08502 : Nat := fullRecordGapCenterValue + 506510

theorem fullRecordGapTerm08502_eq_value :
    recordGapCenter + 506510 = fullRecordGapValue08502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08502 (fullRecordGapValue08502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08502_not_prime : ¬(recordGapCenter + 506510).Prime := by
  rw [fullRecordGapTerm08502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08502_fast_pow_mod_ne_one

def fullRecordGapValue08503 : Nat := fullRecordGapCenterValue + 506642

theorem fullRecordGapTerm08503_eq_value :
    recordGapCenter + 506642 = fullRecordGapValue08503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08503 (fullRecordGapValue08503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08503_not_prime : ¬(recordGapCenter + 506642).Prime := by
  rw [fullRecordGapTerm08503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08503_fast_pow_mod_ne_one

def fullRecordGapValue08504 : Nat := fullRecordGapCenterValue + 506658

theorem fullRecordGapTerm08504_eq_value :
    recordGapCenter + 506658 = fullRecordGapValue08504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08504 (fullRecordGapValue08504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08504_not_prime : ¬(recordGapCenter + 506658).Prime := by
  rw [fullRecordGapTerm08504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08504_fast_pow_mod_ne_one

def fullRecordGapValue08505 : Nat := fullRecordGapCenterValue + 506696

theorem fullRecordGapTerm08505_eq_value :
    recordGapCenter + 506696 = fullRecordGapValue08505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08505 (fullRecordGapValue08505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08505_not_prime : ¬(recordGapCenter + 506696).Prime := by
  rw [fullRecordGapTerm08505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08505_fast_pow_mod_ne_one

def fullRecordGapValue08506 : Nat := fullRecordGapCenterValue + 506732

theorem fullRecordGapTerm08506_eq_value :
    recordGapCenter + 506732 = fullRecordGapValue08506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08506 (fullRecordGapValue08506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08506_not_prime : ¬(recordGapCenter + 506732).Prime := by
  rw [fullRecordGapTerm08506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08506_fast_pow_mod_ne_one

def fullRecordGapValue08507 : Nat := fullRecordGapCenterValue + 506742

theorem fullRecordGapTerm08507_eq_value :
    recordGapCenter + 506742 = fullRecordGapValue08507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08507 (fullRecordGapValue08507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08507_not_prime : ¬(recordGapCenter + 506742).Prime := by
  rw [fullRecordGapTerm08507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08507_fast_pow_mod_ne_one

def fullRecordGapValue08508 : Nat := fullRecordGapCenterValue + 506762

theorem fullRecordGapTerm08508_eq_value :
    recordGapCenter + 506762 = fullRecordGapValue08508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08508 (fullRecordGapValue08508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08508_not_prime : ¬(recordGapCenter + 506762).Prime := by
  rw [fullRecordGapTerm08508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08508_fast_pow_mod_ne_one

def fullRecordGapValue08509 : Nat := fullRecordGapCenterValue + 506852

theorem fullRecordGapTerm08509_eq_value :
    recordGapCenter + 506852 = fullRecordGapValue08509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08509 (fullRecordGapValue08509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08509_not_prime : ¬(recordGapCenter + 506852).Prime := by
  rw [fullRecordGapTerm08509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08509_fast_pow_mod_ne_one

def fullRecordGapValue08510 : Nat := fullRecordGapCenterValue + 506936

theorem fullRecordGapTerm08510_eq_value :
    recordGapCenter + 506936 = fullRecordGapValue08510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08510 (fullRecordGapValue08510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08510_not_prime : ¬(recordGapCenter + 506936).Prime := by
  rw [fullRecordGapTerm08510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08510_fast_pow_mod_ne_one

def fullRecordGapValue08511 : Nat := fullRecordGapCenterValue + 507146

theorem fullRecordGapTerm08511_eq_value :
    recordGapCenter + 507146 = fullRecordGapValue08511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08511 (fullRecordGapValue08511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08511_not_prime : ¬(recordGapCenter + 507146).Prime := by
  rw [fullRecordGapTerm08511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08511_fast_pow_mod_ne_one

def fullRecordGapValue08512 : Nat := fullRecordGapCenterValue + 507218

theorem fullRecordGapTerm08512_eq_value :
    recordGapCenter + 507218 = fullRecordGapValue08512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08512 (fullRecordGapValue08512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08512_not_prime : ¬(recordGapCenter + 507218).Prime := by
  rw [fullRecordGapTerm08512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08512_fast_pow_mod_ne_one

def fullRecordGapValue08513 : Nat := fullRecordGapCenterValue + 507230

theorem fullRecordGapTerm08513_eq_value :
    recordGapCenter + 507230 = fullRecordGapValue08513 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08513_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08513 (fullRecordGapValue08513 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08513_not_prime : ¬(recordGapCenter + 507230).Prime := by
  rw [fullRecordGapTerm08513_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08513, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08513_fast_pow_mod_ne_one

def fullRecordGapValue08514 : Nat := fullRecordGapCenterValue + 507278

theorem fullRecordGapTerm08514_eq_value :
    recordGapCenter + 507278 = fullRecordGapValue08514 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08514_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08514 (fullRecordGapValue08514 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08514_not_prime : ¬(recordGapCenter + 507278).Prime := by
  rw [fullRecordGapTerm08514_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08514, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08514_fast_pow_mod_ne_one

def fullRecordGapValue08515 : Nat := fullRecordGapCenterValue + 507302

theorem fullRecordGapTerm08515_eq_value :
    recordGapCenter + 507302 = fullRecordGapValue08515 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08515_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08515 (fullRecordGapValue08515 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08515_not_prime : ¬(recordGapCenter + 507302).Prime := by
  rw [fullRecordGapTerm08515_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08515, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08515_fast_pow_mod_ne_one

def fullRecordGapValue08516 : Nat := fullRecordGapCenterValue + 507306

theorem fullRecordGapTerm08516_eq_value :
    recordGapCenter + 507306 = fullRecordGapValue08516 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08516_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08516 (fullRecordGapValue08516 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08516_not_prime : ¬(recordGapCenter + 507306).Prime := by
  rw [fullRecordGapTerm08516_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08516, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08516_fast_pow_mod_ne_one

def fullRecordGapValue08517 : Nat := fullRecordGapCenterValue + 507308

theorem fullRecordGapTerm08517_eq_value :
    recordGapCenter + 507308 = fullRecordGapValue08517 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08517_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08517 (fullRecordGapValue08517 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08517_not_prime : ¬(recordGapCenter + 507308).Prime := by
  rw [fullRecordGapTerm08517_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08517, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08517_fast_pow_mod_ne_one

def fullRecordGapValue08518 : Nat := fullRecordGapCenterValue + 507356

theorem fullRecordGapTerm08518_eq_value :
    recordGapCenter + 507356 = fullRecordGapValue08518 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08518_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08518 (fullRecordGapValue08518 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08518_not_prime : ¬(recordGapCenter + 507356).Prime := by
  rw [fullRecordGapTerm08518_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08518, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08518_fast_pow_mod_ne_one

def fullRecordGapValue08519 : Nat := fullRecordGapCenterValue + 507482

theorem fullRecordGapTerm08519_eq_value :
    recordGapCenter + 507482 = fullRecordGapValue08519 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08519_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08519 (fullRecordGapValue08519 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08519_not_prime : ¬(recordGapCenter + 507482).Prime := by
  rw [fullRecordGapTerm08519_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08519, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08519_fast_pow_mod_ne_one

def fullRecordGapValue08520 : Nat := fullRecordGapCenterValue + 507512

theorem fullRecordGapTerm08520_eq_value :
    recordGapCenter + 507512 = fullRecordGapValue08520 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08520_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08520 (fullRecordGapValue08520 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08520_not_prime : ¬(recordGapCenter + 507512).Prime := by
  rw [fullRecordGapTerm08520_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08520, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08520_fast_pow_mod_ne_one

def fullRecordGapValue08521 : Nat := fullRecordGapCenterValue + 507770

theorem fullRecordGapTerm08521_eq_value :
    recordGapCenter + 507770 = fullRecordGapValue08521 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08521_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08521 (fullRecordGapValue08521 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08521_not_prime : ¬(recordGapCenter + 507770).Prime := by
  rw [fullRecordGapTerm08521_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08521, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08521_fast_pow_mod_ne_one

def fullRecordGapValue08522 : Nat := fullRecordGapCenterValue + 507890

theorem fullRecordGapTerm08522_eq_value :
    recordGapCenter + 507890 = fullRecordGapValue08522 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08522_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08522 (fullRecordGapValue08522 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08522_not_prime : ¬(recordGapCenter + 507890).Prime := by
  rw [fullRecordGapTerm08522_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08522, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08522_fast_pow_mod_ne_one

def fullRecordGapValue08523 : Nat := fullRecordGapCenterValue + 507938

theorem fullRecordGapTerm08523_eq_value :
    recordGapCenter + 507938 = fullRecordGapValue08523 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08523_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08523 (fullRecordGapValue08523 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08523_not_prime : ¬(recordGapCenter + 507938).Prime := by
  rw [fullRecordGapTerm08523_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08523, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08523_fast_pow_mod_ne_one

def fullRecordGapValue08524 : Nat := fullRecordGapCenterValue + 507956

theorem fullRecordGapTerm08524_eq_value :
    recordGapCenter + 507956 = fullRecordGapValue08524 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08524_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08524 (fullRecordGapValue08524 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08524_not_prime : ¬(recordGapCenter + 507956).Prime := by
  rw [fullRecordGapTerm08524_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08524, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08524_fast_pow_mod_ne_one

def fullRecordGapValue08525 : Nat := fullRecordGapCenterValue + 507986

theorem fullRecordGapTerm08525_eq_value :
    recordGapCenter + 507986 = fullRecordGapValue08525 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08525_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08525 (fullRecordGapValue08525 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08525_not_prime : ¬(recordGapCenter + 507986).Prime := by
  rw [fullRecordGapTerm08525_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08525, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08525_fast_pow_mod_ne_one

def fullRecordGapValue08526 : Nat := fullRecordGapCenterValue + 507992

theorem fullRecordGapTerm08526_eq_value :
    recordGapCenter + 507992 = fullRecordGapValue08526 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08526_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08526 (fullRecordGapValue08526 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08526_not_prime : ¬(recordGapCenter + 507992).Prime := by
  rw [fullRecordGapTerm08526_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08526, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08526_fast_pow_mod_ne_one

def fullRecordGapValue08527 : Nat := fullRecordGapCenterValue + 508032

theorem fullRecordGapTerm08527_eq_value :
    recordGapCenter + 508032 = fullRecordGapValue08527 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08527_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08527 (fullRecordGapValue08527 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08527_not_prime : ¬(recordGapCenter + 508032).Prime := by
  rw [fullRecordGapTerm08527_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08527, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08527_fast_pow_mod_ne_one

def fullRecordGapValue08528 : Nat := fullRecordGapCenterValue + 508082

theorem fullRecordGapTerm08528_eq_value :
    recordGapCenter + 508082 = fullRecordGapValue08528 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08528_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08528 (fullRecordGapValue08528 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08528_not_prime : ¬(recordGapCenter + 508082).Prime := by
  rw [fullRecordGapTerm08528_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08528, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08528_fast_pow_mod_ne_one

def fullRecordGapValue08529 : Nat := fullRecordGapCenterValue + 508166

theorem fullRecordGapTerm08529_eq_value :
    recordGapCenter + 508166 = fullRecordGapValue08529 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08529_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08529 (fullRecordGapValue08529 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08529_not_prime : ¬(recordGapCenter + 508166).Prime := by
  rw [fullRecordGapTerm08529_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08529, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08529_fast_pow_mod_ne_one

def fullRecordGapValue08530 : Nat := fullRecordGapCenterValue + 508278

theorem fullRecordGapTerm08530_eq_value :
    recordGapCenter + 508278 = fullRecordGapValue08530 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08530_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08530 (fullRecordGapValue08530 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08530_not_prime : ¬(recordGapCenter + 508278).Prime := by
  rw [fullRecordGapTerm08530_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08530, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08530_fast_pow_mod_ne_one

def fullRecordGapValue08531 : Nat := fullRecordGapCenterValue + 508418

theorem fullRecordGapTerm08531_eq_value :
    recordGapCenter + 508418 = fullRecordGapValue08531 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08531_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08531 (fullRecordGapValue08531 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08531_not_prime : ¬(recordGapCenter + 508418).Prime := by
  rw [fullRecordGapTerm08531_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08531, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08531_fast_pow_mod_ne_one

def fullRecordGapValue08532 : Nat := fullRecordGapCenterValue + 508490

theorem fullRecordGapTerm08532_eq_value :
    recordGapCenter + 508490 = fullRecordGapValue08532 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08532_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08532 (fullRecordGapValue08532 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08532_not_prime : ¬(recordGapCenter + 508490).Prime := by
  rw [fullRecordGapTerm08532_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08532, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08532_fast_pow_mod_ne_one

def fullRecordGapValue08533 : Nat := fullRecordGapCenterValue + 508506

theorem fullRecordGapTerm08533_eq_value :
    recordGapCenter + 508506 = fullRecordGapValue08533 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08533_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08533 (fullRecordGapValue08533 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08533_not_prime : ¬(recordGapCenter + 508506).Prime := by
  rw [fullRecordGapTerm08533_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08533, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08533_fast_pow_mod_ne_one

def fullRecordGapValue08534 : Nat := fullRecordGapCenterValue + 508562

theorem fullRecordGapTerm08534_eq_value :
    recordGapCenter + 508562 = fullRecordGapValue08534 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08534_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08534 (fullRecordGapValue08534 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08534_not_prime : ¬(recordGapCenter + 508562).Prime := by
  rw [fullRecordGapTerm08534_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08534, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08534_fast_pow_mod_ne_one

def fullRecordGapValue08535 : Nat := fullRecordGapCenterValue + 508616

theorem fullRecordGapTerm08535_eq_value :
    recordGapCenter + 508616 = fullRecordGapValue08535 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08535_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08535 (fullRecordGapValue08535 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08535_not_prime : ¬(recordGapCenter + 508616).Prime := by
  rw [fullRecordGapTerm08535_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08535, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08535_fast_pow_mod_ne_one

def fullRecordGapValue08536 : Nat := fullRecordGapCenterValue + 508652

theorem fullRecordGapTerm08536_eq_value :
    recordGapCenter + 508652 = fullRecordGapValue08536 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08536_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08536 (fullRecordGapValue08536 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08536_not_prime : ¬(recordGapCenter + 508652).Prime := by
  rw [fullRecordGapTerm08536_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08536, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08536_fast_pow_mod_ne_one

def fullRecordGapValue08537 : Nat := fullRecordGapCenterValue + 508670

theorem fullRecordGapTerm08537_eq_value :
    recordGapCenter + 508670 = fullRecordGapValue08537 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08537_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08537 (fullRecordGapValue08537 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08537_not_prime : ¬(recordGapCenter + 508670).Prime := by
  rw [fullRecordGapTerm08537_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08537, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08537_fast_pow_mod_ne_one

def fullRecordGapValue08538 : Nat := fullRecordGapCenterValue + 508712

theorem fullRecordGapTerm08538_eq_value :
    recordGapCenter + 508712 = fullRecordGapValue08538 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08538_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08538 (fullRecordGapValue08538 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08538_not_prime : ¬(recordGapCenter + 508712).Prime := by
  rw [fullRecordGapTerm08538_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08538, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08538_fast_pow_mod_ne_one

def fullRecordGapValue08539 : Nat := fullRecordGapCenterValue + 508722

theorem fullRecordGapTerm08539_eq_value :
    recordGapCenter + 508722 = fullRecordGapValue08539 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08539_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08539 (fullRecordGapValue08539 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08539_not_prime : ¬(recordGapCenter + 508722).Prime := by
  rw [fullRecordGapTerm08539_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08539, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08539_fast_pow_mod_ne_one

def fullRecordGapValue08540 : Nat := fullRecordGapCenterValue + 508730

theorem fullRecordGapTerm08540_eq_value :
    recordGapCenter + 508730 = fullRecordGapValue08540 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08540_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08540 (fullRecordGapValue08540 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08540_not_prime : ¬(recordGapCenter + 508730).Prime := by
  rw [fullRecordGapTerm08540_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08540, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08540_fast_pow_mod_ne_one

def fullRecordGapValue08541 : Nat := fullRecordGapCenterValue + 508758

theorem fullRecordGapTerm08541_eq_value :
    recordGapCenter + 508758 = fullRecordGapValue08541 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08541_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08541 (fullRecordGapValue08541 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08541_not_prime : ¬(recordGapCenter + 508758).Prime := by
  rw [fullRecordGapTerm08541_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08541, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08541_fast_pow_mod_ne_one

def fullRecordGapValue08542 : Nat := fullRecordGapCenterValue + 508778

theorem fullRecordGapTerm08542_eq_value :
    recordGapCenter + 508778 = fullRecordGapValue08542 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08542_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08542 (fullRecordGapValue08542 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08542_not_prime : ¬(recordGapCenter + 508778).Prime := by
  rw [fullRecordGapTerm08542_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08542, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08542_fast_pow_mod_ne_one

def fullRecordGapValue08543 : Nat := fullRecordGapCenterValue + 508866

theorem fullRecordGapTerm08543_eq_value :
    recordGapCenter + 508866 = fullRecordGapValue08543 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08543_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08543 (fullRecordGapValue08543 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08543_not_prime : ¬(recordGapCenter + 508866).Prime := by
  rw [fullRecordGapTerm08543_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08543, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08543_fast_pow_mod_ne_one

def fullRecordGapValue08544 : Nat := fullRecordGapCenterValue + 508868

theorem fullRecordGapTerm08544_eq_value :
    recordGapCenter + 508868 = fullRecordGapValue08544 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08544_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08544 (fullRecordGapValue08544 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08544_not_prime : ¬(recordGapCenter + 508868).Prime := by
  rw [fullRecordGapTerm08544_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08544, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08544_fast_pow_mod_ne_one

def fullRecordGapValue08545 : Nat := fullRecordGapCenterValue + 509372

theorem fullRecordGapTerm08545_eq_value :
    recordGapCenter + 509372 = fullRecordGapValue08545 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08545_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08545 (fullRecordGapValue08545 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08545_not_prime : ¬(recordGapCenter + 509372).Prime := by
  rw [fullRecordGapTerm08545_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08545, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08545_fast_pow_mod_ne_one

def fullRecordGapValue08546 : Nat := fullRecordGapCenterValue + 509426

theorem fullRecordGapTerm08546_eq_value :
    recordGapCenter + 509426 = fullRecordGapValue08546 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08546_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08546 (fullRecordGapValue08546 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08546_not_prime : ¬(recordGapCenter + 509426).Prime := by
  rw [fullRecordGapTerm08546_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08546, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08546_fast_pow_mod_ne_one

def fullRecordGapValue08547 : Nat := fullRecordGapCenterValue + 509462

theorem fullRecordGapTerm08547_eq_value :
    recordGapCenter + 509462 = fullRecordGapValue08547 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08547_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08547 (fullRecordGapValue08547 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08547_not_prime : ¬(recordGapCenter + 509462).Prime := by
  rw [fullRecordGapTerm08547_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08547, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08547_fast_pow_mod_ne_one

def fullRecordGapValue08548 : Nat := fullRecordGapCenterValue + 509672

theorem fullRecordGapTerm08548_eq_value :
    recordGapCenter + 509672 = fullRecordGapValue08548 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08548_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08548 (fullRecordGapValue08548 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08548_not_prime : ¬(recordGapCenter + 509672).Prime := by
  rw [fullRecordGapTerm08548_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08548, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08548_fast_pow_mod_ne_one

def fullRecordGapValue08549 : Nat := fullRecordGapCenterValue + 509766

theorem fullRecordGapTerm08549_eq_value :
    recordGapCenter + 509766 = fullRecordGapValue08549 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08549_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08549 (fullRecordGapValue08549 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08549_not_prime : ¬(recordGapCenter + 509766).Prime := by
  rw [fullRecordGapTerm08549_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08549, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08549_fast_pow_mod_ne_one

def fullRecordGapValue08550 : Nat := fullRecordGapCenterValue + 509822

theorem fullRecordGapTerm08550_eq_value :
    recordGapCenter + 509822 = fullRecordGapValue08550 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08550_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08550 (fullRecordGapValue08550 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08550_not_prime : ¬(recordGapCenter + 509822).Prime := by
  rw [fullRecordGapTerm08550_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08550, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08550_fast_pow_mod_ne_one

def fullRecordGapValue08551 : Nat := fullRecordGapCenterValue + 509862

theorem fullRecordGapTerm08551_eq_value :
    recordGapCenter + 509862 = fullRecordGapValue08551 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08551_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08551 (fullRecordGapValue08551 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08551_not_prime : ¬(recordGapCenter + 509862).Prime := by
  rw [fullRecordGapTerm08551_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08551, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08551_fast_pow_mod_ne_one

def fullRecordGapValue08552 : Nat := fullRecordGapCenterValue + 509918

theorem fullRecordGapTerm08552_eq_value :
    recordGapCenter + 509918 = fullRecordGapValue08552 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08552_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08552 (fullRecordGapValue08552 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08552_not_prime : ¬(recordGapCenter + 509918).Prime := by
  rw [fullRecordGapTerm08552_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08552, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08552_fast_pow_mod_ne_one

def fullRecordGapValue08553 : Nat := fullRecordGapCenterValue + 509946

theorem fullRecordGapTerm08553_eq_value :
    recordGapCenter + 509946 = fullRecordGapValue08553 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08553_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08553 (fullRecordGapValue08553 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08553_not_prime : ¬(recordGapCenter + 509946).Prime := by
  rw [fullRecordGapTerm08553_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08553, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08553_fast_pow_mod_ne_one

def fullRecordGapValue08554 : Nat := fullRecordGapCenterValue + 509948

theorem fullRecordGapTerm08554_eq_value :
    recordGapCenter + 509948 = fullRecordGapValue08554 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08554_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08554 (fullRecordGapValue08554 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08554_not_prime : ¬(recordGapCenter + 509948).Prime := by
  rw [fullRecordGapTerm08554_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08554, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08554_fast_pow_mod_ne_one

def fullRecordGapValue08555 : Nat := fullRecordGapCenterValue + 509972

theorem fullRecordGapTerm08555_eq_value :
    recordGapCenter + 509972 = fullRecordGapValue08555 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08555_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08555 (fullRecordGapValue08555 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08555_not_prime : ¬(recordGapCenter + 509972).Prime := by
  rw [fullRecordGapTerm08555_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08555, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08555_fast_pow_mod_ne_one

def fullRecordGapValue08556 : Nat := fullRecordGapCenterValue + 510038

theorem fullRecordGapTerm08556_eq_value :
    recordGapCenter + 510038 = fullRecordGapValue08556 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08556_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08556 (fullRecordGapValue08556 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08556_not_prime : ¬(recordGapCenter + 510038).Prime := by
  rw [fullRecordGapTerm08556_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08556, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08556_fast_pow_mod_ne_one

def fullRecordGapValue08557 : Nat := fullRecordGapCenterValue + 510086

theorem fullRecordGapTerm08557_eq_value :
    recordGapCenter + 510086 = fullRecordGapValue08557 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08557_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08557 (fullRecordGapValue08557 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08557_not_prime : ¬(recordGapCenter + 510086).Prime := by
  rw [fullRecordGapTerm08557_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08557, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08557_fast_pow_mod_ne_one

def fullRecordGapValue08558 : Nat := fullRecordGapCenterValue + 510126

theorem fullRecordGapTerm08558_eq_value :
    recordGapCenter + 510126 = fullRecordGapValue08558 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08558_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08558 (fullRecordGapValue08558 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08558_not_prime : ¬(recordGapCenter + 510126).Prime := by
  rw [fullRecordGapTerm08558_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08558, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08558_fast_pow_mod_ne_one

def fullRecordGapValue08559 : Nat := fullRecordGapCenterValue + 510266

theorem fullRecordGapTerm08559_eq_value :
    recordGapCenter + 510266 = fullRecordGapValue08559 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08559_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08559 (fullRecordGapValue08559 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08559_not_prime : ¬(recordGapCenter + 510266).Prime := by
  rw [fullRecordGapTerm08559_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08559, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08559_fast_pow_mod_ne_one

def fullRecordGapValue08560 : Nat := fullRecordGapCenterValue + 510300

theorem fullRecordGapTerm08560_eq_value :
    recordGapCenter + 510300 = fullRecordGapValue08560 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08560_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08560 (fullRecordGapValue08560 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08560_not_prime : ¬(recordGapCenter + 510300).Prime := by
  rw [fullRecordGapTerm08560_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08560, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08560_fast_pow_mod_ne_one

def fullRecordGapValue08561 : Nat := fullRecordGapCenterValue + 510332

theorem fullRecordGapTerm08561_eq_value :
    recordGapCenter + 510332 = fullRecordGapValue08561 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08561_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08561 (fullRecordGapValue08561 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08561_not_prime : ¬(recordGapCenter + 510332).Prime := by
  rw [fullRecordGapTerm08561_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08561, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08561_fast_pow_mod_ne_one

def fullRecordGapValue08562 : Nat := fullRecordGapCenterValue + 510366

theorem fullRecordGapTerm08562_eq_value :
    recordGapCenter + 510366 = fullRecordGapValue08562 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08562_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08562 (fullRecordGapValue08562 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08562_not_prime : ¬(recordGapCenter + 510366).Prime := by
  rw [fullRecordGapTerm08562_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08562, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08562_fast_pow_mod_ne_one

def fullRecordGapValue08563 : Nat := fullRecordGapCenterValue + 510386

theorem fullRecordGapTerm08563_eq_value :
    recordGapCenter + 510386 = fullRecordGapValue08563 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08563_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08563 (fullRecordGapValue08563 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08563_not_prime : ¬(recordGapCenter + 510386).Prime := by
  rw [fullRecordGapTerm08563_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08563, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08563_fast_pow_mod_ne_one

def fullRecordGapValue08564 : Nat := fullRecordGapCenterValue + 510392

theorem fullRecordGapTerm08564_eq_value :
    recordGapCenter + 510392 = fullRecordGapValue08564 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08564_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08564 (fullRecordGapValue08564 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08564_not_prime : ¬(recordGapCenter + 510392).Prime := by
  rw [fullRecordGapTerm08564_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08564, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08564_fast_pow_mod_ne_one

def fullRecordGapValue08565 : Nat := fullRecordGapCenterValue + 510428

theorem fullRecordGapTerm08565_eq_value :
    recordGapCenter + 510428 = fullRecordGapValue08565 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08565_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08565 (fullRecordGapValue08565 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08565_not_prime : ¬(recordGapCenter + 510428).Prime := by
  rw [fullRecordGapTerm08565_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08565, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08565_fast_pow_mod_ne_one

def fullRecordGapValue08566 : Nat := fullRecordGapCenterValue + 510470

theorem fullRecordGapTerm08566_eq_value :
    recordGapCenter + 510470 = fullRecordGapValue08566 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08566_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08566 (fullRecordGapValue08566 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08566_not_prime : ¬(recordGapCenter + 510470).Prime := by
  rw [fullRecordGapTerm08566_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08566, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08566_fast_pow_mod_ne_one

def fullRecordGapValue08567 : Nat := fullRecordGapCenterValue + 510522

theorem fullRecordGapTerm08567_eq_value :
    recordGapCenter + 510522 = fullRecordGapValue08567 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08567_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08567 (fullRecordGapValue08567 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08567_not_prime : ¬(recordGapCenter + 510522).Prime := by
  rw [fullRecordGapTerm08567_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08567, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08567_fast_pow_mod_ne_one

def fullRecordGapValue08568 : Nat := fullRecordGapCenterValue + 510546

theorem fullRecordGapTerm08568_eq_value :
    recordGapCenter + 510546 = fullRecordGapValue08568 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08568_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08568 (fullRecordGapValue08568 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08568_not_prime : ¬(recordGapCenter + 510546).Prime := by
  rw [fullRecordGapTerm08568_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08568, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08568_fast_pow_mod_ne_one

def fullRecordGapValue08569 : Nat := fullRecordGapCenterValue + 510590

theorem fullRecordGapTerm08569_eq_value :
    recordGapCenter + 510590 = fullRecordGapValue08569 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08569_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08569 (fullRecordGapValue08569 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08569_not_prime : ¬(recordGapCenter + 510590).Prime := by
  rw [fullRecordGapTerm08569_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08569, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08569_fast_pow_mod_ne_one

def fullRecordGapValue08570 : Nat := fullRecordGapCenterValue + 510618

theorem fullRecordGapTerm08570_eq_value :
    recordGapCenter + 510618 = fullRecordGapValue08570 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08570_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08570 (fullRecordGapValue08570 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08570_not_prime : ¬(recordGapCenter + 510618).Prime := by
  rw [fullRecordGapTerm08570_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08570, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08570_fast_pow_mod_ne_one

def fullRecordGapValue08571 : Nat := fullRecordGapCenterValue + 510710

theorem fullRecordGapTerm08571_eq_value :
    recordGapCenter + 510710 = fullRecordGapValue08571 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08571_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08571 (fullRecordGapValue08571 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08571_not_prime : ¬(recordGapCenter + 510710).Prime := by
  rw [fullRecordGapTerm08571_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08571, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08571_fast_pow_mod_ne_one

def fullRecordGapValue08572 : Nat := fullRecordGapCenterValue + 510722

theorem fullRecordGapTerm08572_eq_value :
    recordGapCenter + 510722 = fullRecordGapValue08572 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08572_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08572 (fullRecordGapValue08572 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08572_not_prime : ¬(recordGapCenter + 510722).Prime := by
  rw [fullRecordGapTerm08572_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08572, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08572_fast_pow_mod_ne_one

def fullRecordGapValue08573 : Nat := fullRecordGapCenterValue + 510728

theorem fullRecordGapTerm08573_eq_value :
    recordGapCenter + 510728 = fullRecordGapValue08573 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08573_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08573 (fullRecordGapValue08573 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08573_not_prime : ¬(recordGapCenter + 510728).Prime := by
  rw [fullRecordGapTerm08573_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08573, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08573_fast_pow_mod_ne_one

def fullRecordGapValue08574 : Nat := fullRecordGapCenterValue + 510812

theorem fullRecordGapTerm08574_eq_value :
    recordGapCenter + 510812 = fullRecordGapValue08574 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08574_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08574 (fullRecordGapValue08574 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08574_not_prime : ¬(recordGapCenter + 510812).Prime := by
  rw [fullRecordGapTerm08574_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08574, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08574_fast_pow_mod_ne_one

def fullRecordGapValue08575 : Nat := fullRecordGapCenterValue + 510998

theorem fullRecordGapTerm08575_eq_value :
    recordGapCenter + 510998 = fullRecordGapValue08575 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08575_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08575 (fullRecordGapValue08575 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08575_not_prime : ¬(recordGapCenter + 510998).Prime := by
  rw [fullRecordGapTerm08575_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08575, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08575_fast_pow_mod_ne_one

def fullRecordGapValue08576 : Nat := fullRecordGapCenterValue + 511022

theorem fullRecordGapTerm08576_eq_value :
    recordGapCenter + 511022 = fullRecordGapValue08576 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08576_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08576 (fullRecordGapValue08576 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08576_not_prime : ¬(recordGapCenter + 511022).Prime := by
  rw [fullRecordGapTerm08576_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08576, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08576_fast_pow_mod_ne_one

def fullRecordGapValue08577 : Nat := fullRecordGapCenterValue + 511052

theorem fullRecordGapTerm08577_eq_value :
    recordGapCenter + 511052 = fullRecordGapValue08577 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08577_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08577 (fullRecordGapValue08577 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08577_not_prime : ¬(recordGapCenter + 511052).Prime := by
  rw [fullRecordGapTerm08577_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08577, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08577_fast_pow_mod_ne_one

def fullRecordGapValue08578 : Nat := fullRecordGapCenterValue + 511142

theorem fullRecordGapTerm08578_eq_value :
    recordGapCenter + 511142 = fullRecordGapValue08578 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08578_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08578 (fullRecordGapValue08578 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08578_not_prime : ¬(recordGapCenter + 511142).Prime := by
  rw [fullRecordGapTerm08578_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08578, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08578_fast_pow_mod_ne_one

def fullRecordGapValue08579 : Nat := fullRecordGapCenterValue + 511178

theorem fullRecordGapTerm08579_eq_value :
    recordGapCenter + 511178 = fullRecordGapValue08579 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08579_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08579 (fullRecordGapValue08579 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08579_not_prime : ¬(recordGapCenter + 511178).Prime := by
  rw [fullRecordGapTerm08579_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08579, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08579_fast_pow_mod_ne_one

def fullRecordGapValue08580 : Nat := fullRecordGapCenterValue + 511278

theorem fullRecordGapTerm08580_eq_value :
    recordGapCenter + 511278 = fullRecordGapValue08580 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08580_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08580 (fullRecordGapValue08580 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08580_not_prime : ¬(recordGapCenter + 511278).Prime := by
  rw [fullRecordGapTerm08580_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08580, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08580_fast_pow_mod_ne_one

def fullRecordGapValue08581 : Nat := fullRecordGapCenterValue + 511422

theorem fullRecordGapTerm08581_eq_value :
    recordGapCenter + 511422 = fullRecordGapValue08581 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08581_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08581 (fullRecordGapValue08581 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08581_not_prime : ¬(recordGapCenter + 511422).Prime := by
  rw [fullRecordGapTerm08581_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08581, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08581_fast_pow_mod_ne_one

def fullRecordGapValue08582 : Nat := fullRecordGapCenterValue + 511458

theorem fullRecordGapTerm08582_eq_value :
    recordGapCenter + 511458 = fullRecordGapValue08582 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08582_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08582 (fullRecordGapValue08582 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08582_not_prime : ¬(recordGapCenter + 511458).Prime := by
  rw [fullRecordGapTerm08582_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08582, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08582_fast_pow_mod_ne_one

def fullRecordGapValue08583 : Nat := fullRecordGapCenterValue + 511508

theorem fullRecordGapTerm08583_eq_value :
    recordGapCenter + 511508 = fullRecordGapValue08583 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08583_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08583 (fullRecordGapValue08583 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08583_not_prime : ¬(recordGapCenter + 511508).Prime := by
  rw [fullRecordGapTerm08583_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08583, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08583_fast_pow_mod_ne_one

def fullRecordGapValue08584 : Nat := fullRecordGapCenterValue + 511652

theorem fullRecordGapTerm08584_eq_value :
    recordGapCenter + 511652 = fullRecordGapValue08584 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08584_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08584 (fullRecordGapValue08584 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08584_not_prime : ¬(recordGapCenter + 511652).Prime := by
  rw [fullRecordGapTerm08584_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08584, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08584_fast_pow_mod_ne_one

def fullRecordGapValue08585 : Nat := fullRecordGapCenterValue + 511718

theorem fullRecordGapTerm08585_eq_value :
    recordGapCenter + 511718 = fullRecordGapValue08585 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08585_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08585 (fullRecordGapValue08585 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08585_not_prime : ¬(recordGapCenter + 511718).Prime := by
  rw [fullRecordGapTerm08585_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08585, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08585_fast_pow_mod_ne_one

def fullRecordGapValue08586 : Nat := fullRecordGapCenterValue + 511838

theorem fullRecordGapTerm08586_eq_value :
    recordGapCenter + 511838 = fullRecordGapValue08586 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08586_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08586 (fullRecordGapValue08586 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08586_not_prime : ¬(recordGapCenter + 511838).Prime := by
  rw [fullRecordGapTerm08586_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08586, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08586_fast_pow_mod_ne_one

def fullRecordGapValue08587 : Nat := fullRecordGapCenterValue + 511878

theorem fullRecordGapTerm08587_eq_value :
    recordGapCenter + 511878 = fullRecordGapValue08587 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08587_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08587 (fullRecordGapValue08587 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08587_not_prime : ¬(recordGapCenter + 511878).Prime := by
  rw [fullRecordGapTerm08587_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08587, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08587_fast_pow_mod_ne_one

def fullRecordGapValue08588 : Nat := fullRecordGapCenterValue + 511976

theorem fullRecordGapTerm08588_eq_value :
    recordGapCenter + 511976 = fullRecordGapValue08588 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08588_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08588 (fullRecordGapValue08588 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08588_not_prime : ¬(recordGapCenter + 511976).Prime := by
  rw [fullRecordGapTerm08588_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08588, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08588_fast_pow_mod_ne_one

def fullRecordGapValue08589 : Nat := fullRecordGapCenterValue + 512030

theorem fullRecordGapTerm08589_eq_value :
    recordGapCenter + 512030 = fullRecordGapValue08589 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08589_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08589 (fullRecordGapValue08589 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08589_not_prime : ¬(recordGapCenter + 512030).Prime := by
  rw [fullRecordGapTerm08589_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08589, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08589_fast_pow_mod_ne_one

def fullRecordGapValue08590 : Nat := fullRecordGapCenterValue + 512166

theorem fullRecordGapTerm08590_eq_value :
    recordGapCenter + 512166 = fullRecordGapValue08590 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08590_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08590 (fullRecordGapValue08590 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08590_not_prime : ¬(recordGapCenter + 512166).Prime := by
  rw [fullRecordGapTerm08590_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08590, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08590_fast_pow_mod_ne_one

def fullRecordGapValue08591 : Nat := fullRecordGapCenterValue + 512186

theorem fullRecordGapTerm08591_eq_value :
    recordGapCenter + 512186 = fullRecordGapValue08591 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08591_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08591 (fullRecordGapValue08591 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08591_not_prime : ¬(recordGapCenter + 512186).Prime := by
  rw [fullRecordGapTerm08591_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08591, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08591_fast_pow_mod_ne_one

def fullRecordGapValue08592 : Nat := fullRecordGapCenterValue + 512390

theorem fullRecordGapTerm08592_eq_value :
    recordGapCenter + 512390 = fullRecordGapValue08592 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08592_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08592 (fullRecordGapValue08592 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08592_not_prime : ¬(recordGapCenter + 512390).Prime := by
  rw [fullRecordGapTerm08592_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08592, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08592_fast_pow_mod_ne_one

def fullRecordGapValue08593 : Nat := fullRecordGapCenterValue + 512396

theorem fullRecordGapTerm08593_eq_value :
    recordGapCenter + 512396 = fullRecordGapValue08593 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08593_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08593 (fullRecordGapValue08593 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08593_not_prime : ¬(recordGapCenter + 512396).Prime := by
  rw [fullRecordGapTerm08593_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08593, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08593_fast_pow_mod_ne_one

def fullRecordGapValue08594 : Nat := fullRecordGapCenterValue + 512438

theorem fullRecordGapTerm08594_eq_value :
    recordGapCenter + 512438 = fullRecordGapValue08594 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08594_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08594 (fullRecordGapValue08594 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08594_not_prime : ¬(recordGapCenter + 512438).Prime := by
  rw [fullRecordGapTerm08594_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08594, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08594_fast_pow_mod_ne_one

def fullRecordGapValue08595 : Nat := fullRecordGapCenterValue + 512466

theorem fullRecordGapTerm08595_eq_value :
    recordGapCenter + 512466 = fullRecordGapValue08595 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08595_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08595 (fullRecordGapValue08595 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08595_not_prime : ¬(recordGapCenter + 512466).Prime := by
  rw [fullRecordGapTerm08595_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08595, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08595_fast_pow_mod_ne_one

def fullRecordGapValue08596 : Nat := fullRecordGapCenterValue + 512558

theorem fullRecordGapTerm08596_eq_value :
    recordGapCenter + 512558 = fullRecordGapValue08596 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08596_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08596 (fullRecordGapValue08596 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08596_not_prime : ¬(recordGapCenter + 512558).Prime := by
  rw [fullRecordGapTerm08596_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08596, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08596_fast_pow_mod_ne_one

def fullRecordGapValue08597 : Nat := fullRecordGapCenterValue + 512562

theorem fullRecordGapTerm08597_eq_value :
    recordGapCenter + 512562 = fullRecordGapValue08597 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08597_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08597 (fullRecordGapValue08597 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08597_not_prime : ¬(recordGapCenter + 512562).Prime := by
  rw [fullRecordGapTerm08597_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08597, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08597_fast_pow_mod_ne_one

def fullRecordGapValue08598 : Nat := fullRecordGapCenterValue + 512570

theorem fullRecordGapTerm08598_eq_value :
    recordGapCenter + 512570 = fullRecordGapValue08598 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08598_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08598 (fullRecordGapValue08598 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08598_not_prime : ¬(recordGapCenter + 512570).Prime := by
  rw [fullRecordGapTerm08598_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08598, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08598_fast_pow_mod_ne_one

def fullRecordGapValue08599 : Nat := fullRecordGapCenterValue + 512612

theorem fullRecordGapTerm08599_eq_value :
    recordGapCenter + 512612 = fullRecordGapValue08599 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08599_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08599 (fullRecordGapValue08599 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08599_not_prime : ¬(recordGapCenter + 512612).Prime := by
  rw [fullRecordGapTerm08599_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08599, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08599_fast_pow_mod_ne_one

def fullRecordGapValue08600 : Nat := fullRecordGapCenterValue + 512726

theorem fullRecordGapTerm08600_eq_value :
    recordGapCenter + 512726 = fullRecordGapValue08600 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08600_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08600 (fullRecordGapValue08600 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08600_not_prime : ¬(recordGapCenter + 512726).Prime := by
  rw [fullRecordGapTerm08600_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08600, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08600_fast_pow_mod_ne_one

def fullRecordGapValue08601 : Nat := fullRecordGapCenterValue + 512922

theorem fullRecordGapTerm08601_eq_value :
    recordGapCenter + 512922 = fullRecordGapValue08601 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08601_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08601 (fullRecordGapValue08601 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08601_not_prime : ¬(recordGapCenter + 512922).Prime := by
  rw [fullRecordGapTerm08601_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08601, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08601_fast_pow_mod_ne_one

def fullRecordGapValue08602 : Nat := fullRecordGapCenterValue + 513122

theorem fullRecordGapTerm08602_eq_value :
    recordGapCenter + 513122 = fullRecordGapValue08602 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08602_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08602 (fullRecordGapValue08602 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08602_not_prime : ¬(recordGapCenter + 513122).Prime := by
  rw [fullRecordGapTerm08602_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08602, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08602_fast_pow_mod_ne_one

def fullRecordGapValue08603 : Nat := fullRecordGapCenterValue + 513138

theorem fullRecordGapTerm08603_eq_value :
    recordGapCenter + 513138 = fullRecordGapValue08603 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08603_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08603 (fullRecordGapValue08603 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08603_not_prime : ¬(recordGapCenter + 513138).Prime := by
  rw [fullRecordGapTerm08603_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08603, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08603_fast_pow_mod_ne_one

def fullRecordGapValue08604 : Nat := fullRecordGapCenterValue + 513158

theorem fullRecordGapTerm08604_eq_value :
    recordGapCenter + 513158 = fullRecordGapValue08604 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08604_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08604 (fullRecordGapValue08604 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08604_not_prime : ¬(recordGapCenter + 513158).Prime := by
  rw [fullRecordGapTerm08604_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08604, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08604_fast_pow_mod_ne_one

def fullRecordGapValue08605 : Nat := fullRecordGapCenterValue + 513186

theorem fullRecordGapTerm08605_eq_value :
    recordGapCenter + 513186 = fullRecordGapValue08605 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08605_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08605 (fullRecordGapValue08605 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08605_not_prime : ¬(recordGapCenter + 513186).Prime := by
  rw [fullRecordGapTerm08605_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08605, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08605_fast_pow_mod_ne_one

def fullRecordGapValue08606 : Nat := fullRecordGapCenterValue + 513290

theorem fullRecordGapTerm08606_eq_value :
    recordGapCenter + 513290 = fullRecordGapValue08606 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08606_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08606 (fullRecordGapValue08606 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08606_not_prime : ¬(recordGapCenter + 513290).Prime := by
  rw [fullRecordGapTerm08606_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08606, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08606_fast_pow_mod_ne_one

def fullRecordGapValue08607 : Nat := fullRecordGapCenterValue + 513308

theorem fullRecordGapTerm08607_eq_value :
    recordGapCenter + 513308 = fullRecordGapValue08607 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08607_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08607 (fullRecordGapValue08607 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08607_not_prime : ¬(recordGapCenter + 513308).Prime := by
  rw [fullRecordGapTerm08607_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08607, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08607_fast_pow_mod_ne_one

def fullRecordGapValue08608 : Nat := fullRecordGapCenterValue + 513426

theorem fullRecordGapTerm08608_eq_value :
    recordGapCenter + 513426 = fullRecordGapValue08608 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08608_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08608 (fullRecordGapValue08608 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08608_not_prime : ¬(recordGapCenter + 513426).Prime := by
  rw [fullRecordGapTerm08608_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08608, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08608_fast_pow_mod_ne_one

def fullRecordGapValue08609 : Nat := fullRecordGapCenterValue + 513446

theorem fullRecordGapTerm08609_eq_value :
    recordGapCenter + 513446 = fullRecordGapValue08609 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08609_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08609 (fullRecordGapValue08609 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08609_not_prime : ¬(recordGapCenter + 513446).Prime := by
  rw [fullRecordGapTerm08609_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08609, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08609_fast_pow_mod_ne_one

def fullRecordGapValue08610 : Nat := fullRecordGapCenterValue + 513626

theorem fullRecordGapTerm08610_eq_value :
    recordGapCenter + 513626 = fullRecordGapValue08610 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08610_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08610 (fullRecordGapValue08610 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08610_not_prime : ¬(recordGapCenter + 513626).Prime := by
  rw [fullRecordGapTerm08610_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08610, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08610_fast_pow_mod_ne_one

def fullRecordGapValue08611 : Nat := fullRecordGapCenterValue + 513726

theorem fullRecordGapTerm08611_eq_value :
    recordGapCenter + 513726 = fullRecordGapValue08611 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08611_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08611 (fullRecordGapValue08611 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08611_not_prime : ¬(recordGapCenter + 513726).Prime := by
  rw [fullRecordGapTerm08611_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08611, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08611_fast_pow_mod_ne_one

def fullRecordGapValue08612 : Nat := fullRecordGapCenterValue + 513746

theorem fullRecordGapTerm08612_eq_value :
    recordGapCenter + 513746 = fullRecordGapValue08612 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08612_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08612 (fullRecordGapValue08612 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08612_not_prime : ¬(recordGapCenter + 513746).Prime := by
  rw [fullRecordGapTerm08612_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08612, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08612_fast_pow_mod_ne_one

def fullRecordGapValue08613 : Nat := fullRecordGapCenterValue + 513830

theorem fullRecordGapTerm08613_eq_value :
    recordGapCenter + 513830 = fullRecordGapValue08613 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08613_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08613 (fullRecordGapValue08613 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08613_not_prime : ¬(recordGapCenter + 513830).Prime := by
  rw [fullRecordGapTerm08613_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08613, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08613_fast_pow_mod_ne_one

def fullRecordGapValue08614 : Nat := fullRecordGapCenterValue + 513908

theorem fullRecordGapTerm08614_eq_value :
    recordGapCenter + 513908 = fullRecordGapValue08614 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08614_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08614 (fullRecordGapValue08614 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08614_not_prime : ¬(recordGapCenter + 513908).Prime := by
  rw [fullRecordGapTerm08614_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08614, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08614_fast_pow_mod_ne_one

def fullRecordGapValue08615 : Nat := fullRecordGapCenterValue + 513966

theorem fullRecordGapTerm08615_eq_value :
    recordGapCenter + 513966 = fullRecordGapValue08615 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08615_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08615 (fullRecordGapValue08615 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08615_not_prime : ¬(recordGapCenter + 513966).Prime := by
  rw [fullRecordGapTerm08615_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08615, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08615_fast_pow_mod_ne_one

def fullRecordGapValue08616 : Nat := fullRecordGapCenterValue + 514106

theorem fullRecordGapTerm08616_eq_value :
    recordGapCenter + 514106 = fullRecordGapValue08616 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08616_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08616 (fullRecordGapValue08616 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08616_not_prime : ¬(recordGapCenter + 514106).Prime := by
  rw [fullRecordGapTerm08616_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08616, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08616_fast_pow_mod_ne_one

def fullRecordGapValue08617 : Nat := fullRecordGapCenterValue + 514196

theorem fullRecordGapTerm08617_eq_value :
    recordGapCenter + 514196 = fullRecordGapValue08617 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08617_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08617 (fullRecordGapValue08617 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08617_not_prime : ¬(recordGapCenter + 514196).Prime := by
  rw [fullRecordGapTerm08617_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08617, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08617_fast_pow_mod_ne_one

def fullRecordGapValue08618 : Nat := fullRecordGapCenterValue + 514218

theorem fullRecordGapTerm08618_eq_value :
    recordGapCenter + 514218 = fullRecordGapValue08618 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08618_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08618 (fullRecordGapValue08618 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08618_not_prime : ¬(recordGapCenter + 514218).Prime := by
  rw [fullRecordGapTerm08618_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08618, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08618_fast_pow_mod_ne_one

def fullRecordGapValue08619 : Nat := fullRecordGapCenterValue + 514322

theorem fullRecordGapTerm08619_eq_value :
    recordGapCenter + 514322 = fullRecordGapValue08619 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08619_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08619 (fullRecordGapValue08619 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08619_not_prime : ¬(recordGapCenter + 514322).Prime := by
  rw [fullRecordGapTerm08619_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08619, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08619_fast_pow_mod_ne_one

def fullRecordGapValue08620 : Nat := fullRecordGapCenterValue + 514370

theorem fullRecordGapTerm08620_eq_value :
    recordGapCenter + 514370 = fullRecordGapValue08620 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08620_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08620 (fullRecordGapValue08620 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08620_not_prime : ¬(recordGapCenter + 514370).Prime := by
  rw [fullRecordGapTerm08620_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08620, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08620_fast_pow_mod_ne_one

def fullRecordGapValue08621 : Nat := fullRecordGapCenterValue + 514442

theorem fullRecordGapTerm08621_eq_value :
    recordGapCenter + 514442 = fullRecordGapValue08621 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08621_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08621 (fullRecordGapValue08621 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08621_not_prime : ¬(recordGapCenter + 514442).Prime := by
  rw [fullRecordGapTerm08621_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08621, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08621_fast_pow_mod_ne_one

def fullRecordGapValue08622 : Nat := fullRecordGapCenterValue + 514500

theorem fullRecordGapTerm08622_eq_value :
    recordGapCenter + 514500 = fullRecordGapValue08622 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08622_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08622 (fullRecordGapValue08622 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08622_not_prime : ¬(recordGapCenter + 514500).Prime := by
  rw [fullRecordGapTerm08622_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08622, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08622_fast_pow_mod_ne_one

def fullRecordGapValue08623 : Nat := fullRecordGapCenterValue + 514526

theorem fullRecordGapTerm08623_eq_value :
    recordGapCenter + 514526 = fullRecordGapValue08623 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08623_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08623 (fullRecordGapValue08623 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08623_not_prime : ¬(recordGapCenter + 514526).Prime := by
  rw [fullRecordGapTerm08623_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08623, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08623_fast_pow_mod_ne_one

def fullRecordGapValue08624 : Nat := fullRecordGapCenterValue + 514616

theorem fullRecordGapTerm08624_eq_value :
    recordGapCenter + 514616 = fullRecordGapValue08624 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08624_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08624 (fullRecordGapValue08624 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08624_not_prime : ¬(recordGapCenter + 514616).Prime := by
  rw [fullRecordGapTerm08624_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08624, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08624_fast_pow_mod_ne_one

def fullRecordGapValue08625 : Nat := fullRecordGapCenterValue + 514622

theorem fullRecordGapTerm08625_eq_value :
    recordGapCenter + 514622 = fullRecordGapValue08625 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08625_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08625 (fullRecordGapValue08625 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08625_not_prime : ¬(recordGapCenter + 514622).Prime := by
  rw [fullRecordGapTerm08625_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08625, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08625_fast_pow_mod_ne_one

def fullRecordGapValue08626 : Nat := fullRecordGapCenterValue + 514652

theorem fullRecordGapTerm08626_eq_value :
    recordGapCenter + 514652 = fullRecordGapValue08626 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08626_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08626 (fullRecordGapValue08626 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08626_not_prime : ¬(recordGapCenter + 514652).Prime := by
  rw [fullRecordGapTerm08626_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08626, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08626_fast_pow_mod_ne_one

def fullRecordGapValue08627 : Nat := fullRecordGapCenterValue + 514676

theorem fullRecordGapTerm08627_eq_value :
    recordGapCenter + 514676 = fullRecordGapValue08627 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08627_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08627 (fullRecordGapValue08627 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08627_not_prime : ¬(recordGapCenter + 514676).Prime := by
  rw [fullRecordGapTerm08627_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08627, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08627_fast_pow_mod_ne_one

def fullRecordGapValue08628 : Nat := fullRecordGapCenterValue + 514742

theorem fullRecordGapTerm08628_eq_value :
    recordGapCenter + 514742 = fullRecordGapValue08628 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08628_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08628 (fullRecordGapValue08628 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08628_not_prime : ¬(recordGapCenter + 514742).Prime := by
  rw [fullRecordGapTerm08628_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08628, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08628_fast_pow_mod_ne_one

def fullRecordGapValue08629 : Nat := fullRecordGapCenterValue + 514868

theorem fullRecordGapTerm08629_eq_value :
    recordGapCenter + 514868 = fullRecordGapValue08629 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08629_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08629 (fullRecordGapValue08629 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08629_not_prime : ¬(recordGapCenter + 514868).Prime := by
  rw [fullRecordGapTerm08629_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08629, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08629_fast_pow_mod_ne_one

def fullRecordGapValue08630 : Nat := fullRecordGapCenterValue + 515022

theorem fullRecordGapTerm08630_eq_value :
    recordGapCenter + 515022 = fullRecordGapValue08630 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08630_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08630 (fullRecordGapValue08630 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08630_not_prime : ¬(recordGapCenter + 515022).Prime := by
  rw [fullRecordGapTerm08630_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08630, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08630_fast_pow_mod_ne_one

def fullRecordGapValue08631 : Nat := fullRecordGapCenterValue + 515048

theorem fullRecordGapTerm08631_eq_value :
    recordGapCenter + 515048 = fullRecordGapValue08631 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08631_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08631 (fullRecordGapValue08631 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08631_not_prime : ¬(recordGapCenter + 515048).Prime := by
  rw [fullRecordGapTerm08631_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08631, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08631_fast_pow_mod_ne_one

def fullRecordGapValue08632 : Nat := fullRecordGapCenterValue + 515058

theorem fullRecordGapTerm08632_eq_value :
    recordGapCenter + 515058 = fullRecordGapValue08632 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08632_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08632 (fullRecordGapValue08632 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08632_not_prime : ¬(recordGapCenter + 515058).Prime := by
  rw [fullRecordGapTerm08632_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08632, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08632_fast_pow_mod_ne_one

def fullRecordGapValue08633 : Nat := fullRecordGapCenterValue + 515078

theorem fullRecordGapTerm08633_eq_value :
    recordGapCenter + 515078 = fullRecordGapValue08633 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08633_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08633 (fullRecordGapValue08633 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08633_not_prime : ¬(recordGapCenter + 515078).Prime := by
  rw [fullRecordGapTerm08633_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08633, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08633_fast_pow_mod_ne_one

def fullRecordGapValue08634 : Nat := fullRecordGapCenterValue + 515118

theorem fullRecordGapTerm08634_eq_value :
    recordGapCenter + 515118 = fullRecordGapValue08634 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08634_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08634 (fullRecordGapValue08634 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08634_not_prime : ¬(recordGapCenter + 515118).Prime := by
  rw [fullRecordGapTerm08634_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08634, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08634_fast_pow_mod_ne_one

def fullRecordGapValue08635 : Nat := fullRecordGapCenterValue + 515210

theorem fullRecordGapTerm08635_eq_value :
    recordGapCenter + 515210 = fullRecordGapValue08635 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08635_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08635 (fullRecordGapValue08635 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08635_not_prime : ¬(recordGapCenter + 515210).Prime := by
  rw [fullRecordGapTerm08635_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08635, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08635_fast_pow_mod_ne_one

def fullRecordGapValue08636 : Nat := fullRecordGapCenterValue + 515252

theorem fullRecordGapTerm08636_eq_value :
    recordGapCenter + 515252 = fullRecordGapValue08636 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08636_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08636 (fullRecordGapValue08636 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08636_not_prime : ¬(recordGapCenter + 515252).Prime := by
  rw [fullRecordGapTerm08636_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08636, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08636_fast_pow_mod_ne_one

def fullRecordGapValue08637 : Nat := fullRecordGapCenterValue + 515426

theorem fullRecordGapTerm08637_eq_value :
    recordGapCenter + 515426 = fullRecordGapValue08637 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08637_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08637 (fullRecordGapValue08637 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08637_not_prime : ¬(recordGapCenter + 515426).Prime := by
  rw [fullRecordGapTerm08637_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08637, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08637_fast_pow_mod_ne_one

def fullRecordGapValue08638 : Nat := fullRecordGapCenterValue + 515492

theorem fullRecordGapTerm08638_eq_value :
    recordGapCenter + 515492 = fullRecordGapValue08638 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08638_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08638 (fullRecordGapValue08638 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08638_not_prime : ¬(recordGapCenter + 515492).Prime := by
  rw [fullRecordGapTerm08638_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08638, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08638_fast_pow_mod_ne_one

def fullRecordGapValue08639 : Nat := fullRecordGapCenterValue + 515510

theorem fullRecordGapTerm08639_eq_value :
    recordGapCenter + 515510 = fullRecordGapValue08639 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08639_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08639 (fullRecordGapValue08639 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08639_not_prime : ¬(recordGapCenter + 515510).Prime := by
  rw [fullRecordGapTerm08639_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08639, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08639_fast_pow_mod_ne_one

def fullRecordGapValue08640 : Nat := fullRecordGapCenterValue + 515946

theorem fullRecordGapTerm08640_eq_value :
    recordGapCenter + 515946 = fullRecordGapValue08640 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08640_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08640 (fullRecordGapValue08640 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08640_not_prime : ¬(recordGapCenter + 515946).Prime := by
  rw [fullRecordGapTerm08640_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08640, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08640_fast_pow_mod_ne_one

def fullRecordGapValue08641 : Nat := fullRecordGapCenterValue + 516038

theorem fullRecordGapTerm08641_eq_value :
    recordGapCenter + 516038 = fullRecordGapValue08641 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08641_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08641 (fullRecordGapValue08641 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08641_not_prime : ¬(recordGapCenter + 516038).Prime := by
  rw [fullRecordGapTerm08641_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08641, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08641_fast_pow_mod_ne_one

def fullRecordGapValue08642 : Nat := fullRecordGapCenterValue + 516092

theorem fullRecordGapTerm08642_eq_value :
    recordGapCenter + 516092 = fullRecordGapValue08642 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08642_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08642 (fullRecordGapValue08642 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08642_not_prime : ¬(recordGapCenter + 516092).Prime := by
  rw [fullRecordGapTerm08642_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08642, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08642_fast_pow_mod_ne_one

def fullRecordGapValue08643 : Nat := fullRecordGapCenterValue + 516096

theorem fullRecordGapTerm08643_eq_value :
    recordGapCenter + 516096 = fullRecordGapValue08643 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08643_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08643 (fullRecordGapValue08643 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08643_not_prime : ¬(recordGapCenter + 516096).Prime := by
  rw [fullRecordGapTerm08643_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08643, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08643_fast_pow_mod_ne_one

def fullRecordGapValue08644 : Nat := fullRecordGapCenterValue + 516332

theorem fullRecordGapTerm08644_eq_value :
    recordGapCenter + 516332 = fullRecordGapValue08644 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08644_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08644 (fullRecordGapValue08644 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08644_not_prime : ¬(recordGapCenter + 516332).Prime := by
  rw [fullRecordGapTerm08644_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08644, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08644_fast_pow_mod_ne_one

def fullRecordGapValue08645 : Nat := fullRecordGapCenterValue + 516462

theorem fullRecordGapTerm08645_eq_value :
    recordGapCenter + 516462 = fullRecordGapValue08645 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08645_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08645 (fullRecordGapValue08645 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08645_not_prime : ¬(recordGapCenter + 516462).Prime := by
  rw [fullRecordGapTerm08645_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08645, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08645_fast_pow_mod_ne_one

def fullRecordGapValue08646 : Nat := fullRecordGapCenterValue + 516938

theorem fullRecordGapTerm08646_eq_value :
    recordGapCenter + 516938 = fullRecordGapValue08646 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08646_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08646 (fullRecordGapValue08646 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08646_not_prime : ¬(recordGapCenter + 516938).Prime := by
  rw [fullRecordGapTerm08646_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08646, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08646_fast_pow_mod_ne_one

def fullRecordGapValue08647 : Nat := fullRecordGapCenterValue + 516968

theorem fullRecordGapTerm08647_eq_value :
    recordGapCenter + 516968 = fullRecordGapValue08647 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08647_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08647 (fullRecordGapValue08647 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08647_not_prime : ¬(recordGapCenter + 516968).Prime := by
  rw [fullRecordGapTerm08647_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08647, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08647_fast_pow_mod_ne_one

def fullRecordGapValue08648 : Nat := fullRecordGapCenterValue + 517052

theorem fullRecordGapTerm08648_eq_value :
    recordGapCenter + 517052 = fullRecordGapValue08648 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08648_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08648 (fullRecordGapValue08648 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08648_not_prime : ¬(recordGapCenter + 517052).Prime := by
  rw [fullRecordGapTerm08648_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08648, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08648_fast_pow_mod_ne_one

def fullRecordGapValue08649 : Nat := fullRecordGapCenterValue + 517148

theorem fullRecordGapTerm08649_eq_value :
    recordGapCenter + 517148 = fullRecordGapValue08649 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08649_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08649 (fullRecordGapValue08649 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08649_not_prime : ¬(recordGapCenter + 517148).Prime := by
  rw [fullRecordGapTerm08649_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08649, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08649_fast_pow_mod_ne_one

def fullRecordGapValue08650 : Nat := fullRecordGapCenterValue + 517206

theorem fullRecordGapTerm08650_eq_value :
    recordGapCenter + 517206 = fullRecordGapValue08650 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08650_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08650 (fullRecordGapValue08650 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08650_not_prime : ¬(recordGapCenter + 517206).Prime := by
  rw [fullRecordGapTerm08650_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08650, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08650_fast_pow_mod_ne_one

def fullRecordGapValue08651 : Nat := fullRecordGapCenterValue + 517226

theorem fullRecordGapTerm08651_eq_value :
    recordGapCenter + 517226 = fullRecordGapValue08651 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08651_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08651 (fullRecordGapValue08651 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08651_not_prime : ¬(recordGapCenter + 517226).Prime := by
  rw [fullRecordGapTerm08651_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08651, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08651_fast_pow_mod_ne_one

def fullRecordGapValue08652 : Nat := fullRecordGapCenterValue + 517346

theorem fullRecordGapTerm08652_eq_value :
    recordGapCenter + 517346 = fullRecordGapValue08652 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08652_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08652 (fullRecordGapValue08652 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08652_not_prime : ¬(recordGapCenter + 517346).Prime := by
  rw [fullRecordGapTerm08652_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08652, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08652_fast_pow_mod_ne_one

def fullRecordGapValue08653 : Nat := fullRecordGapCenterValue + 517490

theorem fullRecordGapTerm08653_eq_value :
    recordGapCenter + 517490 = fullRecordGapValue08653 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08653_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08653 (fullRecordGapValue08653 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08653_not_prime : ¬(recordGapCenter + 517490).Prime := by
  rw [fullRecordGapTerm08653_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08653, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08653_fast_pow_mod_ne_one

def fullRecordGapValue08654 : Nat := fullRecordGapCenterValue + 517596

theorem fullRecordGapTerm08654_eq_value :
    recordGapCenter + 517596 = fullRecordGapValue08654 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08654_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08654 (fullRecordGapValue08654 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08654_not_prime : ¬(recordGapCenter + 517596).Prime := by
  rw [fullRecordGapTerm08654_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08654, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08654_fast_pow_mod_ne_one

def fullRecordGapValue08655 : Nat := fullRecordGapCenterValue + 517742

theorem fullRecordGapTerm08655_eq_value :
    recordGapCenter + 517742 = fullRecordGapValue08655 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08655_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08655 (fullRecordGapValue08655 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08655_not_prime : ¬(recordGapCenter + 517742).Prime := by
  rw [fullRecordGapTerm08655_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08655, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08655_fast_pow_mod_ne_one

def fullRecordGapValue08656 : Nat := fullRecordGapCenterValue + 517746

theorem fullRecordGapTerm08656_eq_value :
    recordGapCenter + 517746 = fullRecordGapValue08656 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08656_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08656 (fullRecordGapValue08656 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08656_not_prime : ¬(recordGapCenter + 517746).Prime := by
  rw [fullRecordGapTerm08656_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08656, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08656_fast_pow_mod_ne_one

def fullRecordGapValue08657 : Nat := fullRecordGapCenterValue + 517758

theorem fullRecordGapTerm08657_eq_value :
    recordGapCenter + 517758 = fullRecordGapValue08657 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08657_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08657 (fullRecordGapValue08657 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08657_not_prime : ¬(recordGapCenter + 517758).Prime := by
  rw [fullRecordGapTerm08657_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08657, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08657_fast_pow_mod_ne_one

def fullRecordGapValue08658 : Nat := fullRecordGapCenterValue + 517812

theorem fullRecordGapTerm08658_eq_value :
    recordGapCenter + 517812 = fullRecordGapValue08658 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08658_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08658 (fullRecordGapValue08658 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08658_not_prime : ¬(recordGapCenter + 517812).Prime := by
  rw [fullRecordGapTerm08658_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08658, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08658_fast_pow_mod_ne_one

def fullRecordGapValue08659 : Nat := fullRecordGapCenterValue + 517938

theorem fullRecordGapTerm08659_eq_value :
    recordGapCenter + 517938 = fullRecordGapValue08659 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08659_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08659 (fullRecordGapValue08659 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08659_not_prime : ¬(recordGapCenter + 517938).Prime := by
  rw [fullRecordGapTerm08659_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08659, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08659_fast_pow_mod_ne_one

def fullRecordGapValue08660 : Nat := fullRecordGapCenterValue + 517970

theorem fullRecordGapTerm08660_eq_value :
    recordGapCenter + 517970 = fullRecordGapValue08660 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08660_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08660 (fullRecordGapValue08660 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08660_not_prime : ¬(recordGapCenter + 517970).Prime := by
  rw [fullRecordGapTerm08660_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08660, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08660_fast_pow_mod_ne_one

def fullRecordGapValue08661 : Nat := fullRecordGapCenterValue + 517988

theorem fullRecordGapTerm08661_eq_value :
    recordGapCenter + 517988 = fullRecordGapValue08661 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08661_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08661 (fullRecordGapValue08661 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08661_not_prime : ¬(recordGapCenter + 517988).Prime := by
  rw [fullRecordGapTerm08661_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08661, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08661_fast_pow_mod_ne_one

def fullRecordGapValue08662 : Nat := fullRecordGapCenterValue + 518018

theorem fullRecordGapTerm08662_eq_value :
    recordGapCenter + 518018 = fullRecordGapValue08662 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08662_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08662 (fullRecordGapValue08662 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08662_not_prime : ¬(recordGapCenter + 518018).Prime := by
  rw [fullRecordGapTerm08662_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08662, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08662_fast_pow_mod_ne_one

def fullRecordGapValue08663 : Nat := fullRecordGapCenterValue + 518036

theorem fullRecordGapTerm08663_eq_value :
    recordGapCenter + 518036 = fullRecordGapValue08663 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08663_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08663 (fullRecordGapValue08663 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08663_not_prime : ¬(recordGapCenter + 518036).Prime := by
  rw [fullRecordGapTerm08663_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08663, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08663_fast_pow_mod_ne_one

def fullRecordGapValue08664 : Nat := fullRecordGapCenterValue + 518106

theorem fullRecordGapTerm08664_eq_value :
    recordGapCenter + 518106 = fullRecordGapValue08664 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08664_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08664 (fullRecordGapValue08664 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08664_not_prime : ¬(recordGapCenter + 518106).Prime := by
  rw [fullRecordGapTerm08664_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08664, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08664_fast_pow_mod_ne_one

def fullRecordGapValue08665 : Nat := fullRecordGapCenterValue + 518108

theorem fullRecordGapTerm08665_eq_value :
    recordGapCenter + 518108 = fullRecordGapValue08665 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08665_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08665 (fullRecordGapValue08665 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08665_not_prime : ¬(recordGapCenter + 518108).Prime := by
  rw [fullRecordGapTerm08665_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08665, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08665_fast_pow_mod_ne_one

def fullRecordGapValue08666 : Nat := fullRecordGapCenterValue + 518142

theorem fullRecordGapTerm08666_eq_value :
    recordGapCenter + 518142 = fullRecordGapValue08666 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08666_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08666 (fullRecordGapValue08666 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08666_not_prime : ¬(recordGapCenter + 518142).Prime := by
  rw [fullRecordGapTerm08666_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08666, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08666_fast_pow_mod_ne_one

def fullRecordGapValue08667 : Nat := fullRecordGapCenterValue + 518156

theorem fullRecordGapTerm08667_eq_value :
    recordGapCenter + 518156 = fullRecordGapValue08667 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08667_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08667 (fullRecordGapValue08667 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08667_not_prime : ¬(recordGapCenter + 518156).Prime := by
  rw [fullRecordGapTerm08667_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08667, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08667_fast_pow_mod_ne_one

def fullRecordGapValue08668 : Nat := fullRecordGapCenterValue + 518226

theorem fullRecordGapTerm08668_eq_value :
    recordGapCenter + 518226 = fullRecordGapValue08668 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08668_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08668 (fullRecordGapValue08668 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08668_not_prime : ¬(recordGapCenter + 518226).Prime := by
  rw [fullRecordGapTerm08668_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08668, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08668_fast_pow_mod_ne_one

def fullRecordGapValue08669 : Nat := fullRecordGapCenterValue + 518246

theorem fullRecordGapTerm08669_eq_value :
    recordGapCenter + 518246 = fullRecordGapValue08669 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08669_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08669 (fullRecordGapValue08669 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08669_not_prime : ¬(recordGapCenter + 518246).Prime := by
  rw [fullRecordGapTerm08669_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08669, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08669_fast_pow_mod_ne_one

def fullRecordGapValue08670 : Nat := fullRecordGapCenterValue + 518268

theorem fullRecordGapTerm08670_eq_value :
    recordGapCenter + 518268 = fullRecordGapValue08670 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08670_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08670 (fullRecordGapValue08670 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08670_not_prime : ¬(recordGapCenter + 518268).Prime := by
  rw [fullRecordGapTerm08670_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08670, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08670_fast_pow_mod_ne_one

def fullRecordGapValue08671 : Nat := fullRecordGapCenterValue + 518270

theorem fullRecordGapTerm08671_eq_value :
    recordGapCenter + 518270 = fullRecordGapValue08671 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08671_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08671 (fullRecordGapValue08671 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08671_not_prime : ¬(recordGapCenter + 518270).Prime := by
  rw [fullRecordGapTerm08671_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08671, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08671_fast_pow_mod_ne_one

def fullRecordGapValue08672 : Nat := fullRecordGapCenterValue + 518318

theorem fullRecordGapTerm08672_eq_value :
    recordGapCenter + 518318 = fullRecordGapValue08672 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08672_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08672 (fullRecordGapValue08672 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08672_not_prime : ¬(recordGapCenter + 518318).Prime := by
  rw [fullRecordGapTerm08672_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08672, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08672_fast_pow_mod_ne_one

def fullRecordGapValue08673 : Nat := fullRecordGapCenterValue + 518390

theorem fullRecordGapTerm08673_eq_value :
    recordGapCenter + 518390 = fullRecordGapValue08673 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08673_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08673 (fullRecordGapValue08673 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08673_not_prime : ¬(recordGapCenter + 518390).Prime := by
  rw [fullRecordGapTerm08673_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08673, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08673_fast_pow_mod_ne_one

def fullRecordGapValue08674 : Nat := fullRecordGapCenterValue + 518400

theorem fullRecordGapTerm08674_eq_value :
    recordGapCenter + 518400 = fullRecordGapValue08674 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08674_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08674 (fullRecordGapValue08674 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08674_not_prime : ¬(recordGapCenter + 518400).Prime := by
  rw [fullRecordGapTerm08674_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08674, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08674_fast_pow_mod_ne_one

def fullRecordGapValue08675 : Nat := fullRecordGapCenterValue + 518402

theorem fullRecordGapTerm08675_eq_value :
    recordGapCenter + 518402 = fullRecordGapValue08675 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08675_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08675 (fullRecordGapValue08675 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08675_not_prime : ¬(recordGapCenter + 518402).Prime := by
  rw [fullRecordGapTerm08675_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08675, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08675_fast_pow_mod_ne_one

def fullRecordGapValue08676 : Nat := fullRecordGapCenterValue + 518438

theorem fullRecordGapTerm08676_eq_value :
    recordGapCenter + 518438 = fullRecordGapValue08676 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08676_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08676 (fullRecordGapValue08676 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08676_not_prime : ¬(recordGapCenter + 518438).Prime := by
  rw [fullRecordGapTerm08676_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08676, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08676_fast_pow_mod_ne_one

def fullRecordGapValue08677 : Nat := fullRecordGapCenterValue + 518616

theorem fullRecordGapTerm08677_eq_value :
    recordGapCenter + 518616 = fullRecordGapValue08677 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08677_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08677 (fullRecordGapValue08677 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08677_not_prime : ¬(recordGapCenter + 518616).Prime := by
  rw [fullRecordGapTerm08677_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08677, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08677_fast_pow_mod_ne_one

def fullRecordGapValue08678 : Nat := fullRecordGapCenterValue + 518676

theorem fullRecordGapTerm08678_eq_value :
    recordGapCenter + 518676 = fullRecordGapValue08678 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08678_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08678 (fullRecordGapValue08678 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08678_not_prime : ¬(recordGapCenter + 518676).Prime := by
  rw [fullRecordGapTerm08678_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08678, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08678_fast_pow_mod_ne_one

def fullRecordGapValue08679 : Nat := fullRecordGapCenterValue + 518906

theorem fullRecordGapTerm08679_eq_value :
    recordGapCenter + 518906 = fullRecordGapValue08679 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08679_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08679 (fullRecordGapValue08679 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08679_not_prime : ¬(recordGapCenter + 518906).Prime := by
  rw [fullRecordGapTerm08679_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08679, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08679_fast_pow_mod_ne_one

def fullRecordGapValue08680 : Nat := fullRecordGapCenterValue + 518918

theorem fullRecordGapTerm08680_eq_value :
    recordGapCenter + 518918 = fullRecordGapValue08680 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08680_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08680 (fullRecordGapValue08680 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08680_not_prime : ¬(recordGapCenter + 518918).Prime := by
  rw [fullRecordGapTerm08680_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08680, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08680_fast_pow_mod_ne_one

def fullRecordGapValue08681 : Nat := fullRecordGapCenterValue + 518948

theorem fullRecordGapTerm08681_eq_value :
    recordGapCenter + 518948 = fullRecordGapValue08681 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08681_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08681 (fullRecordGapValue08681 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08681_not_prime : ¬(recordGapCenter + 518948).Prime := by
  rw [fullRecordGapTerm08681_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08681, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08681_fast_pow_mod_ne_one

def fullRecordGapValue08682 : Nat := fullRecordGapCenterValue + 519006

theorem fullRecordGapTerm08682_eq_value :
    recordGapCenter + 519006 = fullRecordGapValue08682 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08682_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08682 (fullRecordGapValue08682 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08682_not_prime : ¬(recordGapCenter + 519006).Prime := by
  rw [fullRecordGapTerm08682_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08682, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08682_fast_pow_mod_ne_one

def fullRecordGapValue08683 : Nat := fullRecordGapCenterValue + 519032

theorem fullRecordGapTerm08683_eq_value :
    recordGapCenter + 519032 = fullRecordGapValue08683 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08683_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08683 (fullRecordGapValue08683 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08683_not_prime : ¬(recordGapCenter + 519032).Prime := by
  rw [fullRecordGapTerm08683_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08683, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08683_fast_pow_mod_ne_one

def fullRecordGapValue08684 : Nat := fullRecordGapCenterValue + 519062

theorem fullRecordGapTerm08684_eq_value :
    recordGapCenter + 519062 = fullRecordGapValue08684 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08684_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08684 (fullRecordGapValue08684 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08684_not_prime : ¬(recordGapCenter + 519062).Prime := by
  rw [fullRecordGapTerm08684_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08684, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08684_fast_pow_mod_ne_one

def fullRecordGapValue08685 : Nat := fullRecordGapCenterValue + 519128

theorem fullRecordGapTerm08685_eq_value :
    recordGapCenter + 519128 = fullRecordGapValue08685 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08685_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08685 (fullRecordGapValue08685 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08685_not_prime : ¬(recordGapCenter + 519128).Prime := by
  rw [fullRecordGapTerm08685_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08685, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08685_fast_pow_mod_ne_one

def fullRecordGapValue08686 : Nat := fullRecordGapCenterValue + 519206

theorem fullRecordGapTerm08686_eq_value :
    recordGapCenter + 519206 = fullRecordGapValue08686 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08686_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08686 (fullRecordGapValue08686 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08686_not_prime : ¬(recordGapCenter + 519206).Prime := by
  rw [fullRecordGapTerm08686_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08686, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08686_fast_pow_mod_ne_one

def fullRecordGapValue08687 : Nat := fullRecordGapCenterValue + 519410

theorem fullRecordGapTerm08687_eq_value :
    recordGapCenter + 519410 = fullRecordGapValue08687 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08687_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08687 (fullRecordGapValue08687 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08687_not_prime : ¬(recordGapCenter + 519410).Prime := by
  rw [fullRecordGapTerm08687_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08687, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08687_fast_pow_mod_ne_one

def fullRecordGapValue08688 : Nat := fullRecordGapCenterValue + 519446

theorem fullRecordGapTerm08688_eq_value :
    recordGapCenter + 519446 = fullRecordGapValue08688 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08688_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08688 (fullRecordGapValue08688 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08688_not_prime : ¬(recordGapCenter + 519446).Prime := by
  rw [fullRecordGapTerm08688_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08688, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08688_fast_pow_mod_ne_one

def fullRecordGapValue08689 : Nat := fullRecordGapCenterValue + 519668

theorem fullRecordGapTerm08689_eq_value :
    recordGapCenter + 519668 = fullRecordGapValue08689 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08689_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08689 (fullRecordGapValue08689 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08689_not_prime : ¬(recordGapCenter + 519668).Prime := by
  rw [fullRecordGapTerm08689_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08689, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08689_fast_pow_mod_ne_one

def fullRecordGapValue08690 : Nat := fullRecordGapCenterValue + 519710

theorem fullRecordGapTerm08690_eq_value :
    recordGapCenter + 519710 = fullRecordGapValue08690 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08690_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08690 (fullRecordGapValue08690 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08690_not_prime : ¬(recordGapCenter + 519710).Prime := by
  rw [fullRecordGapTerm08690_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08690, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08690_fast_pow_mod_ne_one

def fullRecordGapValue08691 : Nat := fullRecordGapCenterValue + 519752

theorem fullRecordGapTerm08691_eq_value :
    recordGapCenter + 519752 = fullRecordGapValue08691 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08691_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08691 (fullRecordGapValue08691 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08691_not_prime : ¬(recordGapCenter + 519752).Prime := by
  rw [fullRecordGapTerm08691_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08691, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08691_fast_pow_mod_ne_one

def fullRecordGapValue08692 : Nat := fullRecordGapCenterValue + 519852

theorem fullRecordGapTerm08692_eq_value :
    recordGapCenter + 519852 = fullRecordGapValue08692 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08692_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08692 (fullRecordGapValue08692 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08692_not_prime : ¬(recordGapCenter + 519852).Prime := by
  rw [fullRecordGapTerm08692_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08692, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08692_fast_pow_mod_ne_one

def fullRecordGapValue08693 : Nat := fullRecordGapCenterValue + 520046

theorem fullRecordGapTerm08693_eq_value :
    recordGapCenter + 520046 = fullRecordGapValue08693 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08693_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08693 (fullRecordGapValue08693 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08693_not_prime : ¬(recordGapCenter + 520046).Prime := by
  rw [fullRecordGapTerm08693_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08693, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08693_fast_pow_mod_ne_one

def fullRecordGapValue08694 : Nat := fullRecordGapCenterValue + 520062

theorem fullRecordGapTerm08694_eq_value :
    recordGapCenter + 520062 = fullRecordGapValue08694 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08694_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08694 (fullRecordGapValue08694 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08694_not_prime : ¬(recordGapCenter + 520062).Prime := by
  rw [fullRecordGapTerm08694_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08694, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08694_fast_pow_mod_ne_one

def fullRecordGapValue08695 : Nat := fullRecordGapCenterValue + 520088

theorem fullRecordGapTerm08695_eq_value :
    recordGapCenter + 520088 = fullRecordGapValue08695 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08695_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08695 (fullRecordGapValue08695 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08695_not_prime : ¬(recordGapCenter + 520088).Prime := by
  rw [fullRecordGapTerm08695_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08695, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08695_fast_pow_mod_ne_one

def fullRecordGapValue08696 : Nat := fullRecordGapCenterValue + 520158

theorem fullRecordGapTerm08696_eq_value :
    recordGapCenter + 520158 = fullRecordGapValue08696 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08696_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08696 (fullRecordGapValue08696 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08696_not_prime : ¬(recordGapCenter + 520158).Prime := by
  rw [fullRecordGapTerm08696_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08696, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08696_fast_pow_mod_ne_one

def fullRecordGapValue08697 : Nat := fullRecordGapCenterValue + 520266

theorem fullRecordGapTerm08697_eq_value :
    recordGapCenter + 520266 = fullRecordGapValue08697 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08697_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08697 (fullRecordGapValue08697 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08697_not_prime : ¬(recordGapCenter + 520266).Prime := by
  rw [fullRecordGapTerm08697_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08697, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08697_fast_pow_mod_ne_one

def fullRecordGapValue08698 : Nat := fullRecordGapCenterValue + 520292

theorem fullRecordGapTerm08698_eq_value :
    recordGapCenter + 520292 = fullRecordGapValue08698 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08698_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08698 (fullRecordGapValue08698 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08698_not_prime : ¬(recordGapCenter + 520292).Prime := by
  rw [fullRecordGapTerm08698_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08698, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08698_fast_pow_mod_ne_one

def fullRecordGapValue08699 : Nat := fullRecordGapCenterValue + 520458

theorem fullRecordGapTerm08699_eq_value :
    recordGapCenter + 520458 = fullRecordGapValue08699 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08699_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08699 (fullRecordGapValue08699 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08699_not_prime : ¬(recordGapCenter + 520458).Prime := by
  rw [fullRecordGapTerm08699_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08699, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08699_fast_pow_mod_ne_one

def fullRecordGapValue08700 : Nat := fullRecordGapCenterValue + 520508

theorem fullRecordGapTerm08700_eq_value :
    recordGapCenter + 520508 = fullRecordGapValue08700 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08700_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08700 (fullRecordGapValue08700 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08700_not_prime : ¬(recordGapCenter + 520508).Prime := by
  rw [fullRecordGapTerm08700_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08700, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08700_fast_pow_mod_ne_one

def fullRecordGapValue08701 : Nat := fullRecordGapCenterValue + 520518

theorem fullRecordGapTerm08701_eq_value :
    recordGapCenter + 520518 = fullRecordGapValue08701 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08701_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08701 (fullRecordGapValue08701 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08701_not_prime : ¬(recordGapCenter + 520518).Prime := by
  rw [fullRecordGapTerm08701_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08701, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08701_fast_pow_mod_ne_one

def fullRecordGapValue08702 : Nat := fullRecordGapCenterValue + 520602

theorem fullRecordGapTerm08702_eq_value :
    recordGapCenter + 520602 = fullRecordGapValue08702 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08702_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08702 (fullRecordGapValue08702 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08702_not_prime : ¬(recordGapCenter + 520602).Prime := by
  rw [fullRecordGapTerm08702_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08702, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08702_fast_pow_mod_ne_one

def fullRecordGapValue08703 : Nat := fullRecordGapCenterValue + 520658

theorem fullRecordGapTerm08703_eq_value :
    recordGapCenter + 520658 = fullRecordGapValue08703 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08703_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08703 (fullRecordGapValue08703 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08703_not_prime : ¬(recordGapCenter + 520658).Prime := by
  rw [fullRecordGapTerm08703_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08703, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08703_fast_pow_mod_ne_one

def fullRecordGapValue08704 : Nat := fullRecordGapCenterValue + 520808

theorem fullRecordGapTerm08704_eq_value :
    recordGapCenter + 520808 = fullRecordGapValue08704 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08704_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08704 (fullRecordGapValue08704 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08704_not_prime : ¬(recordGapCenter + 520808).Prime := by
  rw [fullRecordGapTerm08704_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08704, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08704_fast_pow_mod_ne_one

end PrimeFactorUnimodality
