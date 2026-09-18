import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue01281 : Nat := fullRecordGapCenterValue - 353482

theorem fullRecordGapTerm01281_eq_value :
    recordGapCenter - 353482 = fullRecordGapValue01281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01281 (fullRecordGapValue01281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01281_not_prime : ¬(recordGapCenter - 353482).Prime := by
  rw [fullRecordGapTerm01281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01281_fast_pow_mod_ne_one

def fullRecordGapValue01282 : Nat := fullRecordGapCenterValue - 353454

theorem fullRecordGapTerm01282_eq_value :
    recordGapCenter - 353454 = fullRecordGapValue01282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01282 (fullRecordGapValue01282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01282_not_prime : ¬(recordGapCenter - 353454).Prime := by
  rw [fullRecordGapTerm01282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01282_fast_pow_mod_ne_one

def fullRecordGapValue01283 : Nat := fullRecordGapCenterValue - 353422

theorem fullRecordGapTerm01283_eq_value :
    recordGapCenter - 353422 = fullRecordGapValue01283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01283 (fullRecordGapValue01283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01283_not_prime : ¬(recordGapCenter - 353422).Prime := by
  rw [fullRecordGapTerm01283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01283_fast_pow_mod_ne_one

def fullRecordGapValue01284 : Nat := fullRecordGapCenterValue - 353308

theorem fullRecordGapTerm01284_eq_value :
    recordGapCenter - 353308 = fullRecordGapValue01284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01284 (fullRecordGapValue01284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01284_not_prime : ¬(recordGapCenter - 353308).Prime := by
  rw [fullRecordGapTerm01284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01284_fast_pow_mod_ne_one

def fullRecordGapValue01285 : Nat := fullRecordGapCenterValue - 353194

theorem fullRecordGapTerm01285_eq_value :
    recordGapCenter - 353194 = fullRecordGapValue01285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01285 (fullRecordGapValue01285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01285_not_prime : ¬(recordGapCenter - 353194).Prime := by
  rw [fullRecordGapTerm01285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01285_fast_pow_mod_ne_one

def fullRecordGapValue01286 : Nat := fullRecordGapCenterValue - 353062

theorem fullRecordGapTerm01286_eq_value :
    recordGapCenter - 353062 = fullRecordGapValue01286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01286 (fullRecordGapValue01286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01286_not_prime : ¬(recordGapCenter - 353062).Prime := by
  rw [fullRecordGapTerm01286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01286_fast_pow_mod_ne_one

def fullRecordGapValue01287 : Nat := fullRecordGapCenterValue - 352984

theorem fullRecordGapTerm01287_eq_value :
    recordGapCenter - 352984 = fullRecordGapValue01287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01287 (fullRecordGapValue01287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01287_not_prime : ¬(recordGapCenter - 352984).Prime := by
  rw [fullRecordGapTerm01287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01287_fast_pow_mod_ne_one

def fullRecordGapValue01288 : Nat := fullRecordGapCenterValue - 352722

theorem fullRecordGapTerm01288_eq_value :
    recordGapCenter - 352722 = fullRecordGapValue01288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01288 (fullRecordGapValue01288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01288_not_prime : ¬(recordGapCenter - 352722).Prime := by
  rw [fullRecordGapTerm01288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01288_fast_pow_mod_ne_one

def fullRecordGapValue01289 : Nat := fullRecordGapCenterValue - 352714

theorem fullRecordGapTerm01289_eq_value :
    recordGapCenter - 352714 = fullRecordGapValue01289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01289 (fullRecordGapValue01289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01289_not_prime : ¬(recordGapCenter - 352714).Prime := by
  rw [fullRecordGapTerm01289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01289_fast_pow_mod_ne_one

def fullRecordGapValue01290 : Nat := fullRecordGapCenterValue - 352468

theorem fullRecordGapTerm01290_eq_value :
    recordGapCenter - 352468 = fullRecordGapValue01290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01290 (fullRecordGapValue01290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01290_not_prime : ¬(recordGapCenter - 352468).Prime := by
  rw [fullRecordGapTerm01290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01290_fast_pow_mod_ne_one

def fullRecordGapValue01291 : Nat := fullRecordGapCenterValue - 352414

theorem fullRecordGapTerm01291_eq_value :
    recordGapCenter - 352414 = fullRecordGapValue01291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01291 (fullRecordGapValue01291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01291_not_prime : ¬(recordGapCenter - 352414).Prime := by
  rw [fullRecordGapTerm01291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01291_fast_pow_mod_ne_one

def fullRecordGapValue01292 : Nat := fullRecordGapCenterValue - 352362

theorem fullRecordGapTerm01292_eq_value :
    recordGapCenter - 352362 = fullRecordGapValue01292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01292 (fullRecordGapValue01292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01292_not_prime : ¬(recordGapCenter - 352362).Prime := by
  rw [fullRecordGapTerm01292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01292_fast_pow_mod_ne_one

def fullRecordGapValue01293 : Nat := fullRecordGapCenterValue - 352258

theorem fullRecordGapTerm01293_eq_value :
    recordGapCenter - 352258 = fullRecordGapValue01293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01293 (fullRecordGapValue01293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01293_not_prime : ¬(recordGapCenter - 352258).Prime := by
  rw [fullRecordGapTerm01293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01293_fast_pow_mod_ne_one

def fullRecordGapValue01294 : Nat := fullRecordGapCenterValue - 352174

theorem fullRecordGapTerm01294_eq_value :
    recordGapCenter - 352174 = fullRecordGapValue01294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01294 (fullRecordGapValue01294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01294_not_prime : ¬(recordGapCenter - 352174).Prime := by
  rw [fullRecordGapTerm01294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01294_fast_pow_mod_ne_one

def fullRecordGapValue01295 : Nat := fullRecordGapCenterValue - 352168

theorem fullRecordGapTerm01295_eq_value :
    recordGapCenter - 352168 = fullRecordGapValue01295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01295 (fullRecordGapValue01295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01295_not_prime : ¬(recordGapCenter - 352168).Prime := by
  rw [fullRecordGapTerm01295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01295_fast_pow_mod_ne_one

def fullRecordGapValue01296 : Nat := fullRecordGapCenterValue - 352162

theorem fullRecordGapTerm01296_eq_value :
    recordGapCenter - 352162 = fullRecordGapValue01296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01296 (fullRecordGapValue01296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01296_not_prime : ¬(recordGapCenter - 352162).Prime := by
  rw [fullRecordGapTerm01296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01296_fast_pow_mod_ne_one

def fullRecordGapValue01297 : Nat := fullRecordGapCenterValue - 352074

theorem fullRecordGapTerm01297_eq_value :
    recordGapCenter - 352074 = fullRecordGapValue01297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01297 (fullRecordGapValue01297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01297_not_prime : ¬(recordGapCenter - 352074).Prime := by
  rw [fullRecordGapTerm01297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01297_fast_pow_mod_ne_one

def fullRecordGapValue01298 : Nat := fullRecordGapCenterValue - 352000

theorem fullRecordGapTerm01298_eq_value :
    recordGapCenter - 352000 = fullRecordGapValue01298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01298 (fullRecordGapValue01298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01298_not_prime : ¬(recordGapCenter - 352000).Prime := by
  rw [fullRecordGapTerm01298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01298_fast_pow_mod_ne_one

def fullRecordGapValue01299 : Nat := fullRecordGapCenterValue - 351958

theorem fullRecordGapTerm01299_eq_value :
    recordGapCenter - 351958 = fullRecordGapValue01299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01299 (fullRecordGapValue01299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01299_not_prime : ¬(recordGapCenter - 351958).Prime := by
  rw [fullRecordGapTerm01299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01299_fast_pow_mod_ne_one

def fullRecordGapValue01300 : Nat := fullRecordGapCenterValue - 351942

theorem fullRecordGapTerm01300_eq_value :
    recordGapCenter - 351942 = fullRecordGapValue01300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01300 (fullRecordGapValue01300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01300_not_prime : ¬(recordGapCenter - 351942).Prime := by
  rw [fullRecordGapTerm01300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01300_fast_pow_mod_ne_one

def fullRecordGapValue01301 : Nat := fullRecordGapCenterValue - 351892

theorem fullRecordGapTerm01301_eq_value :
    recordGapCenter - 351892 = fullRecordGapValue01301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01301 (fullRecordGapValue01301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01301_not_prime : ¬(recordGapCenter - 351892).Prime := by
  rw [fullRecordGapTerm01301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01301_fast_pow_mod_ne_one

def fullRecordGapValue01302 : Nat := fullRecordGapCenterValue - 351658

theorem fullRecordGapTerm01302_eq_value :
    recordGapCenter - 351658 = fullRecordGapValue01302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01302 (fullRecordGapValue01302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01302_not_prime : ¬(recordGapCenter - 351658).Prime := by
  rw [fullRecordGapTerm01302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01302_fast_pow_mod_ne_one

def fullRecordGapValue01303 : Nat := fullRecordGapCenterValue - 351622

theorem fullRecordGapTerm01303_eq_value :
    recordGapCenter - 351622 = fullRecordGapValue01303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01303 (fullRecordGapValue01303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01303_not_prime : ¬(recordGapCenter - 351622).Prime := by
  rw [fullRecordGapTerm01303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01303_fast_pow_mod_ne_one

def fullRecordGapValue01304 : Nat := fullRecordGapCenterValue - 351544

theorem fullRecordGapTerm01304_eq_value :
    recordGapCenter - 351544 = fullRecordGapValue01304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01304 (fullRecordGapValue01304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01304_not_prime : ¬(recordGapCenter - 351544).Prime := by
  rw [fullRecordGapTerm01304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01304_fast_pow_mod_ne_one

def fullRecordGapValue01305 : Nat := fullRecordGapCenterValue - 351514

theorem fullRecordGapTerm01305_eq_value :
    recordGapCenter - 351514 = fullRecordGapValue01305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01305 (fullRecordGapValue01305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01305_not_prime : ¬(recordGapCenter - 351514).Prime := by
  rw [fullRecordGapTerm01305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01305_fast_pow_mod_ne_one

def fullRecordGapValue01306 : Nat := fullRecordGapCenterValue - 351474

theorem fullRecordGapTerm01306_eq_value :
    recordGapCenter - 351474 = fullRecordGapValue01306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01306 (fullRecordGapValue01306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01306_not_prime : ¬(recordGapCenter - 351474).Prime := by
  rw [fullRecordGapTerm01306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01306_fast_pow_mod_ne_one

def fullRecordGapValue01307 : Nat := fullRecordGapCenterValue - 351402

theorem fullRecordGapTerm01307_eq_value :
    recordGapCenter - 351402 = fullRecordGapValue01307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01307 (fullRecordGapValue01307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01307_not_prime : ¬(recordGapCenter - 351402).Prime := by
  rw [fullRecordGapTerm01307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01307_fast_pow_mod_ne_one

def fullRecordGapValue01308 : Nat := fullRecordGapCenterValue - 351304

theorem fullRecordGapTerm01308_eq_value :
    recordGapCenter - 351304 = fullRecordGapValue01308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01308 (fullRecordGapValue01308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01308_not_prime : ¬(recordGapCenter - 351304).Prime := by
  rw [fullRecordGapTerm01308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01308_fast_pow_mod_ne_one

def fullRecordGapValue01309 : Nat := fullRecordGapCenterValue - 351294

theorem fullRecordGapTerm01309_eq_value :
    recordGapCenter - 351294 = fullRecordGapValue01309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01309 (fullRecordGapValue01309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01309_not_prime : ¬(recordGapCenter - 351294).Prime := by
  rw [fullRecordGapTerm01309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01309_fast_pow_mod_ne_one

def fullRecordGapValue01310 : Nat := fullRecordGapCenterValue - 351262

theorem fullRecordGapTerm01310_eq_value :
    recordGapCenter - 351262 = fullRecordGapValue01310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01310 (fullRecordGapValue01310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01310_not_prime : ¬(recordGapCenter - 351262).Prime := by
  rw [fullRecordGapTerm01310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01310_fast_pow_mod_ne_one

def fullRecordGapValue01311 : Nat := fullRecordGapCenterValue - 351244

theorem fullRecordGapTerm01311_eq_value :
    recordGapCenter - 351244 = fullRecordGapValue01311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01311 (fullRecordGapValue01311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01311_not_prime : ¬(recordGapCenter - 351244).Prime := by
  rw [fullRecordGapTerm01311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01311_fast_pow_mod_ne_one

def fullRecordGapValue01312 : Nat := fullRecordGapCenterValue - 351112

theorem fullRecordGapTerm01312_eq_value :
    recordGapCenter - 351112 = fullRecordGapValue01312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01312 (fullRecordGapValue01312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01312_not_prime : ¬(recordGapCenter - 351112).Prime := by
  rw [fullRecordGapTerm01312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01312_fast_pow_mod_ne_one

def fullRecordGapValue01313 : Nat := fullRecordGapCenterValue - 350884

theorem fullRecordGapTerm01313_eq_value :
    recordGapCenter - 350884 = fullRecordGapValue01313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01313 (fullRecordGapValue01313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01313_not_prime : ¬(recordGapCenter - 350884).Prime := by
  rw [fullRecordGapTerm01313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01313_fast_pow_mod_ne_one

def fullRecordGapValue01314 : Nat := fullRecordGapCenterValue - 350788

theorem fullRecordGapTerm01314_eq_value :
    recordGapCenter - 350788 = fullRecordGapValue01314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01314 (fullRecordGapValue01314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01314_not_prime : ¬(recordGapCenter - 350788).Prime := by
  rw [fullRecordGapTerm01314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01314_fast_pow_mod_ne_one

def fullRecordGapValue01315 : Nat := fullRecordGapCenterValue - 350698

theorem fullRecordGapTerm01315_eq_value :
    recordGapCenter - 350698 = fullRecordGapValue01315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01315 (fullRecordGapValue01315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01315_not_prime : ¬(recordGapCenter - 350698).Prime := by
  rw [fullRecordGapTerm01315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01315_fast_pow_mod_ne_one

def fullRecordGapValue01316 : Nat := fullRecordGapCenterValue - 350634

theorem fullRecordGapTerm01316_eq_value :
    recordGapCenter - 350634 = fullRecordGapValue01316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01316 (fullRecordGapValue01316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01316_not_prime : ¬(recordGapCenter - 350634).Prime := by
  rw [fullRecordGapTerm01316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01316_fast_pow_mod_ne_one

def fullRecordGapValue01317 : Nat := fullRecordGapCenterValue - 350572

theorem fullRecordGapTerm01317_eq_value :
    recordGapCenter - 350572 = fullRecordGapValue01317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01317 (fullRecordGapValue01317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01317_not_prime : ¬(recordGapCenter - 350572).Prime := by
  rw [fullRecordGapTerm01317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01317_fast_pow_mod_ne_one

def fullRecordGapValue01318 : Nat := fullRecordGapCenterValue - 350524

theorem fullRecordGapTerm01318_eq_value :
    recordGapCenter - 350524 = fullRecordGapValue01318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01318 (fullRecordGapValue01318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01318_not_prime : ¬(recordGapCenter - 350524).Prime := by
  rw [fullRecordGapTerm01318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01318_fast_pow_mod_ne_one

def fullRecordGapValue01319 : Nat := fullRecordGapCenterValue - 350502

theorem fullRecordGapTerm01319_eq_value :
    recordGapCenter - 350502 = fullRecordGapValue01319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01319 (fullRecordGapValue01319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01319_not_prime : ¬(recordGapCenter - 350502).Prime := by
  rw [fullRecordGapTerm01319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01319_fast_pow_mod_ne_one

def fullRecordGapValue01320 : Nat := fullRecordGapCenterValue - 350418

theorem fullRecordGapTerm01320_eq_value :
    recordGapCenter - 350418 = fullRecordGapValue01320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01320 (fullRecordGapValue01320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01320_not_prime : ¬(recordGapCenter - 350418).Prime := by
  rw [fullRecordGapTerm01320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01320_fast_pow_mod_ne_one

def fullRecordGapValue01321 : Nat := fullRecordGapCenterValue - 350214

theorem fullRecordGapTerm01321_eq_value :
    recordGapCenter - 350214 = fullRecordGapValue01321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01321 (fullRecordGapValue01321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01321_not_prime : ¬(recordGapCenter - 350214).Prime := by
  rw [fullRecordGapTerm01321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01321_fast_pow_mod_ne_one

def fullRecordGapValue01322 : Nat := fullRecordGapCenterValue - 349978

theorem fullRecordGapTerm01322_eq_value :
    recordGapCenter - 349978 = fullRecordGapValue01322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01322 (fullRecordGapValue01322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01322_not_prime : ¬(recordGapCenter - 349978).Prime := by
  rw [fullRecordGapTerm01322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01322_fast_pow_mod_ne_one

def fullRecordGapValue01323 : Nat := fullRecordGapCenterValue - 349918

theorem fullRecordGapTerm01323_eq_value :
    recordGapCenter - 349918 = fullRecordGapValue01323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01323 (fullRecordGapValue01323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01323_not_prime : ¬(recordGapCenter - 349918).Prime := by
  rw [fullRecordGapTerm01323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01323_fast_pow_mod_ne_one

def fullRecordGapValue01324 : Nat := fullRecordGapCenterValue - 349834

theorem fullRecordGapTerm01324_eq_value :
    recordGapCenter - 349834 = fullRecordGapValue01324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01324 (fullRecordGapValue01324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01324_not_prime : ¬(recordGapCenter - 349834).Prime := by
  rw [fullRecordGapTerm01324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01324_fast_pow_mod_ne_one

def fullRecordGapValue01325 : Nat := fullRecordGapCenterValue - 349732

theorem fullRecordGapTerm01325_eq_value :
    recordGapCenter - 349732 = fullRecordGapValue01325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01325 (fullRecordGapValue01325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01325_not_prime : ¬(recordGapCenter - 349732).Prime := by
  rw [fullRecordGapTerm01325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01325_fast_pow_mod_ne_one

def fullRecordGapValue01326 : Nat := fullRecordGapCenterValue - 349708

theorem fullRecordGapTerm01326_eq_value :
    recordGapCenter - 349708 = fullRecordGapValue01326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01326 (fullRecordGapValue01326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01326_not_prime : ¬(recordGapCenter - 349708).Prime := by
  rw [fullRecordGapTerm01326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01326_fast_pow_mod_ne_one

def fullRecordGapValue01327 : Nat := fullRecordGapCenterValue - 349702

theorem fullRecordGapTerm01327_eq_value :
    recordGapCenter - 349702 = fullRecordGapValue01327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01327 (fullRecordGapValue01327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01327_not_prime : ¬(recordGapCenter - 349702).Prime := by
  rw [fullRecordGapTerm01327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01327_fast_pow_mod_ne_one

def fullRecordGapValue01328 : Nat := fullRecordGapCenterValue - 349642

theorem fullRecordGapTerm01328_eq_value :
    recordGapCenter - 349642 = fullRecordGapValue01328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01328 (fullRecordGapValue01328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01328_not_prime : ¬(recordGapCenter - 349642).Prime := by
  rw [fullRecordGapTerm01328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01328_fast_pow_mod_ne_one

def fullRecordGapValue01329 : Nat := fullRecordGapCenterValue - 349534

theorem fullRecordGapTerm01329_eq_value :
    recordGapCenter - 349534 = fullRecordGapValue01329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01329 (fullRecordGapValue01329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01329_not_prime : ¬(recordGapCenter - 349534).Prime := by
  rw [fullRecordGapTerm01329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01329_fast_pow_mod_ne_one

def fullRecordGapValue01330 : Nat := fullRecordGapCenterValue - 349498

theorem fullRecordGapTerm01330_eq_value :
    recordGapCenter - 349498 = fullRecordGapValue01330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01330 (fullRecordGapValue01330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01330_not_prime : ¬(recordGapCenter - 349498).Prime := by
  rw [fullRecordGapTerm01330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01330_fast_pow_mod_ne_one

def fullRecordGapValue01331 : Nat := fullRecordGapCenterValue - 349302

theorem fullRecordGapTerm01331_eq_value :
    recordGapCenter - 349302 = fullRecordGapValue01331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01331 (fullRecordGapValue01331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01331_not_prime : ¬(recordGapCenter - 349302).Prime := by
  rw [fullRecordGapTerm01331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01331_fast_pow_mod_ne_one

def fullRecordGapValue01332 : Nat := fullRecordGapCenterValue - 349288

theorem fullRecordGapTerm01332_eq_value :
    recordGapCenter - 349288 = fullRecordGapValue01332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01332 (fullRecordGapValue01332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01332_not_prime : ¬(recordGapCenter - 349288).Prime := by
  rw [fullRecordGapTerm01332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01332_fast_pow_mod_ne_one

def fullRecordGapValue01333 : Nat := fullRecordGapCenterValue - 349272

theorem fullRecordGapTerm01333_eq_value :
    recordGapCenter - 349272 = fullRecordGapValue01333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01333 (fullRecordGapValue01333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01333_not_prime : ¬(recordGapCenter - 349272).Prime := by
  rw [fullRecordGapTerm01333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01333_fast_pow_mod_ne_one

def fullRecordGapValue01334 : Nat := fullRecordGapCenterValue - 349242

theorem fullRecordGapTerm01334_eq_value :
    recordGapCenter - 349242 = fullRecordGapValue01334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01334 (fullRecordGapValue01334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01334_not_prime : ¬(recordGapCenter - 349242).Prime := by
  rw [fullRecordGapTerm01334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01334_fast_pow_mod_ne_one

def fullRecordGapValue01335 : Nat := fullRecordGapCenterValue - 349234

theorem fullRecordGapTerm01335_eq_value :
    recordGapCenter - 349234 = fullRecordGapValue01335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01335 (fullRecordGapValue01335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01335_not_prime : ¬(recordGapCenter - 349234).Prime := by
  rw [fullRecordGapTerm01335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01335_fast_pow_mod_ne_one

def fullRecordGapValue01336 : Nat := fullRecordGapCenterValue - 349198

theorem fullRecordGapTerm01336_eq_value :
    recordGapCenter - 349198 = fullRecordGapValue01336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01336 (fullRecordGapValue01336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01336_not_prime : ¬(recordGapCenter - 349198).Prime := by
  rw [fullRecordGapTerm01336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01336_fast_pow_mod_ne_one

def fullRecordGapValue01337 : Nat := fullRecordGapCenterValue - 349194

theorem fullRecordGapTerm01337_eq_value :
    recordGapCenter - 349194 = fullRecordGapValue01337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01337 (fullRecordGapValue01337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01337_not_prime : ¬(recordGapCenter - 349194).Prime := by
  rw [fullRecordGapTerm01337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01337_fast_pow_mod_ne_one

def fullRecordGapValue01338 : Nat := fullRecordGapCenterValue - 349192

theorem fullRecordGapTerm01338_eq_value :
    recordGapCenter - 349192 = fullRecordGapValue01338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01338 (fullRecordGapValue01338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01338_not_prime : ¬(recordGapCenter - 349192).Prime := by
  rw [fullRecordGapTerm01338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01338_fast_pow_mod_ne_one

def fullRecordGapValue01339 : Nat := fullRecordGapCenterValue - 349054

theorem fullRecordGapTerm01339_eq_value :
    recordGapCenter - 349054 = fullRecordGapValue01339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01339 (fullRecordGapValue01339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01339_not_prime : ¬(recordGapCenter - 349054).Prime := by
  rw [fullRecordGapTerm01339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01339_fast_pow_mod_ne_one

def fullRecordGapValue01340 : Nat := fullRecordGapCenterValue - 348904

theorem fullRecordGapTerm01340_eq_value :
    recordGapCenter - 348904 = fullRecordGapValue01340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01340 (fullRecordGapValue01340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01340_not_prime : ¬(recordGapCenter - 348904).Prime := by
  rw [fullRecordGapTerm01340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01340_fast_pow_mod_ne_one

def fullRecordGapValue01341 : Nat := fullRecordGapCenterValue - 348892

theorem fullRecordGapTerm01341_eq_value :
    recordGapCenter - 348892 = fullRecordGapValue01341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01341 (fullRecordGapValue01341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01341_not_prime : ¬(recordGapCenter - 348892).Prime := by
  rw [fullRecordGapTerm01341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01341_fast_pow_mod_ne_one

def fullRecordGapValue01342 : Nat := fullRecordGapCenterValue - 348882

theorem fullRecordGapTerm01342_eq_value :
    recordGapCenter - 348882 = fullRecordGapValue01342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01342 (fullRecordGapValue01342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01342_not_prime : ¬(recordGapCenter - 348882).Prime := by
  rw [fullRecordGapTerm01342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01342_fast_pow_mod_ne_one

def fullRecordGapValue01343 : Nat := fullRecordGapCenterValue - 348724

theorem fullRecordGapTerm01343_eq_value :
    recordGapCenter - 348724 = fullRecordGapValue01343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01343 (fullRecordGapValue01343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01343_not_prime : ¬(recordGapCenter - 348724).Prime := by
  rw [fullRecordGapTerm01343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01343_fast_pow_mod_ne_one

def fullRecordGapValue01344 : Nat := fullRecordGapCenterValue - 348562

theorem fullRecordGapTerm01344_eq_value :
    recordGapCenter - 348562 = fullRecordGapValue01344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01344 (fullRecordGapValue01344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01344_not_prime : ¬(recordGapCenter - 348562).Prime := by
  rw [fullRecordGapTerm01344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01344_fast_pow_mod_ne_one

def fullRecordGapValue01345 : Nat := fullRecordGapCenterValue - 348438

theorem fullRecordGapTerm01345_eq_value :
    recordGapCenter - 348438 = fullRecordGapValue01345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01345 (fullRecordGapValue01345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01345_not_prime : ¬(recordGapCenter - 348438).Prime := by
  rw [fullRecordGapTerm01345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01345_fast_pow_mod_ne_one

def fullRecordGapValue01346 : Nat := fullRecordGapCenterValue - 348298

theorem fullRecordGapTerm01346_eq_value :
    recordGapCenter - 348298 = fullRecordGapValue01346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01346 (fullRecordGapValue01346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01346_not_prime : ¬(recordGapCenter - 348298).Prime := by
  rw [fullRecordGapTerm01346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01346_fast_pow_mod_ne_one

def fullRecordGapValue01347 : Nat := fullRecordGapCenterValue - 348294

theorem fullRecordGapTerm01347_eq_value :
    recordGapCenter - 348294 = fullRecordGapValue01347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01347 (fullRecordGapValue01347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01347_not_prime : ¬(recordGapCenter - 348294).Prime := by
  rw [fullRecordGapTerm01347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01347_fast_pow_mod_ne_one

def fullRecordGapValue01348 : Nat := fullRecordGapCenterValue - 348148

theorem fullRecordGapTerm01348_eq_value :
    recordGapCenter - 348148 = fullRecordGapValue01348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01348 (fullRecordGapValue01348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01348_not_prime : ¬(recordGapCenter - 348148).Prime := by
  rw [fullRecordGapTerm01348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01348_fast_pow_mod_ne_one

def fullRecordGapValue01349 : Nat := fullRecordGapCenterValue - 348078

theorem fullRecordGapTerm01349_eq_value :
    recordGapCenter - 348078 = fullRecordGapValue01349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01349 (fullRecordGapValue01349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01349_not_prime : ¬(recordGapCenter - 348078).Prime := by
  rw [fullRecordGapTerm01349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01349_fast_pow_mod_ne_one

def fullRecordGapValue01350 : Nat := fullRecordGapCenterValue - 348052

theorem fullRecordGapTerm01350_eq_value :
    recordGapCenter - 348052 = fullRecordGapValue01350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01350 (fullRecordGapValue01350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01350_not_prime : ¬(recordGapCenter - 348052).Prime := by
  rw [fullRecordGapTerm01350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01350_fast_pow_mod_ne_one

def fullRecordGapValue01351 : Nat := fullRecordGapCenterValue - 347938

theorem fullRecordGapTerm01351_eq_value :
    recordGapCenter - 347938 = fullRecordGapValue01351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01351 (fullRecordGapValue01351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01351_not_prime : ¬(recordGapCenter - 347938).Prime := by
  rw [fullRecordGapTerm01351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01351_fast_pow_mod_ne_one

def fullRecordGapValue01352 : Nat := fullRecordGapCenterValue - 347848

theorem fullRecordGapTerm01352_eq_value :
    recordGapCenter - 347848 = fullRecordGapValue01352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01352 (fullRecordGapValue01352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01352_not_prime : ¬(recordGapCenter - 347848).Prime := by
  rw [fullRecordGapTerm01352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01352_fast_pow_mod_ne_one

def fullRecordGapValue01353 : Nat := fullRecordGapCenterValue - 347818

theorem fullRecordGapTerm01353_eq_value :
    recordGapCenter - 347818 = fullRecordGapValue01353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01353 (fullRecordGapValue01353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01353_not_prime : ¬(recordGapCenter - 347818).Prime := by
  rw [fullRecordGapTerm01353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01353_fast_pow_mod_ne_one

def fullRecordGapValue01354 : Nat := fullRecordGapCenterValue - 347734

theorem fullRecordGapTerm01354_eq_value :
    recordGapCenter - 347734 = fullRecordGapValue01354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01354 (fullRecordGapValue01354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01354_not_prime : ¬(recordGapCenter - 347734).Prime := by
  rw [fullRecordGapTerm01354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01354_fast_pow_mod_ne_one

def fullRecordGapValue01355 : Nat := fullRecordGapCenterValue - 347722

theorem fullRecordGapTerm01355_eq_value :
    recordGapCenter - 347722 = fullRecordGapValue01355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01355 (fullRecordGapValue01355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01355_not_prime : ¬(recordGapCenter - 347722).Prime := by
  rw [fullRecordGapTerm01355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01355_fast_pow_mod_ne_one

def fullRecordGapValue01356 : Nat := fullRecordGapCenterValue - 347682

theorem fullRecordGapTerm01356_eq_value :
    recordGapCenter - 347682 = fullRecordGapValue01356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01356 (fullRecordGapValue01356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01356_not_prime : ¬(recordGapCenter - 347682).Prime := by
  rw [fullRecordGapTerm01356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01356_fast_pow_mod_ne_one

def fullRecordGapValue01357 : Nat := fullRecordGapCenterValue - 347554

theorem fullRecordGapTerm01357_eq_value :
    recordGapCenter - 347554 = fullRecordGapValue01357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01357 (fullRecordGapValue01357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01357_not_prime : ¬(recordGapCenter - 347554).Prime := by
  rw [fullRecordGapTerm01357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01357_fast_pow_mod_ne_one

def fullRecordGapValue01358 : Nat := fullRecordGapCenterValue - 347482

theorem fullRecordGapTerm01358_eq_value :
    recordGapCenter - 347482 = fullRecordGapValue01358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01358 (fullRecordGapValue01358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01358_not_prime : ¬(recordGapCenter - 347482).Prime := by
  rw [fullRecordGapTerm01358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01358_fast_pow_mod_ne_one

def fullRecordGapValue01359 : Nat := fullRecordGapCenterValue - 347458

theorem fullRecordGapTerm01359_eq_value :
    recordGapCenter - 347458 = fullRecordGapValue01359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01359 (fullRecordGapValue01359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01359_not_prime : ¬(recordGapCenter - 347458).Prime := by
  rw [fullRecordGapTerm01359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01359_fast_pow_mod_ne_one

def fullRecordGapValue01360 : Nat := fullRecordGapCenterValue - 347394

theorem fullRecordGapTerm01360_eq_value :
    recordGapCenter - 347394 = fullRecordGapValue01360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01360 (fullRecordGapValue01360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01360_not_prime : ¬(recordGapCenter - 347394).Prime := by
  rw [fullRecordGapTerm01360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01360_fast_pow_mod_ne_one

def fullRecordGapValue01361 : Nat := fullRecordGapCenterValue - 347224

theorem fullRecordGapTerm01361_eq_value :
    recordGapCenter - 347224 = fullRecordGapValue01361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01361 (fullRecordGapValue01361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01361_not_prime : ¬(recordGapCenter - 347224).Prime := by
  rw [fullRecordGapTerm01361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01361_fast_pow_mod_ne_one

def fullRecordGapValue01362 : Nat := fullRecordGapCenterValue - 347128

theorem fullRecordGapTerm01362_eq_value :
    recordGapCenter - 347128 = fullRecordGapValue01362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01362 (fullRecordGapValue01362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01362_not_prime : ¬(recordGapCenter - 347128).Prime := by
  rw [fullRecordGapTerm01362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01362_fast_pow_mod_ne_one

def fullRecordGapValue01363 : Nat := fullRecordGapCenterValue - 347034

theorem fullRecordGapTerm01363_eq_value :
    recordGapCenter - 347034 = fullRecordGapValue01363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01363 (fullRecordGapValue01363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01363_not_prime : ¬(recordGapCenter - 347034).Prime := by
  rw [fullRecordGapTerm01363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01363_fast_pow_mod_ne_one

def fullRecordGapValue01364 : Nat := fullRecordGapCenterValue - 346972

theorem fullRecordGapTerm01364_eq_value :
    recordGapCenter - 346972 = fullRecordGapValue01364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01364 (fullRecordGapValue01364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01364_not_prime : ¬(recordGapCenter - 346972).Prime := by
  rw [fullRecordGapTerm01364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01364_fast_pow_mod_ne_one

def fullRecordGapValue01365 : Nat := fullRecordGapCenterValue - 346722

theorem fullRecordGapTerm01365_eq_value :
    recordGapCenter - 346722 = fullRecordGapValue01365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01365 (fullRecordGapValue01365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01365_not_prime : ¬(recordGapCenter - 346722).Prime := by
  rw [fullRecordGapTerm01365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01365_fast_pow_mod_ne_one

def fullRecordGapValue01366 : Nat := fullRecordGapCenterValue - 346714

theorem fullRecordGapTerm01366_eq_value :
    recordGapCenter - 346714 = fullRecordGapValue01366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01366 (fullRecordGapValue01366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01366_not_prime : ¬(recordGapCenter - 346714).Prime := by
  rw [fullRecordGapTerm01366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01366_fast_pow_mod_ne_one

def fullRecordGapValue01367 : Nat := fullRecordGapCenterValue - 346638

theorem fullRecordGapTerm01367_eq_value :
    recordGapCenter - 346638 = fullRecordGapValue01367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01367 (fullRecordGapValue01367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01367_not_prime : ¬(recordGapCenter - 346638).Prime := by
  rw [fullRecordGapTerm01367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01367_fast_pow_mod_ne_one

def fullRecordGapValue01368 : Nat := fullRecordGapCenterValue - 346618

theorem fullRecordGapTerm01368_eq_value :
    recordGapCenter - 346618 = fullRecordGapValue01368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01368 (fullRecordGapValue01368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01368_not_prime : ¬(recordGapCenter - 346618).Prime := by
  rw [fullRecordGapTerm01368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01368_fast_pow_mod_ne_one

def fullRecordGapValue01369 : Nat := fullRecordGapCenterValue - 346552

theorem fullRecordGapTerm01369_eq_value :
    recordGapCenter - 346552 = fullRecordGapValue01369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01369 (fullRecordGapValue01369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01369_not_prime : ¬(recordGapCenter - 346552).Prime := by
  rw [fullRecordGapTerm01369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01369_fast_pow_mod_ne_one

def fullRecordGapValue01370 : Nat := fullRecordGapCenterValue - 346348

theorem fullRecordGapTerm01370_eq_value :
    recordGapCenter - 346348 = fullRecordGapValue01370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01370 (fullRecordGapValue01370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01370_not_prime : ¬(recordGapCenter - 346348).Prime := by
  rw [fullRecordGapTerm01370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01370_fast_pow_mod_ne_one

def fullRecordGapValue01371 : Nat := fullRecordGapCenterValue - 346282

theorem fullRecordGapTerm01371_eq_value :
    recordGapCenter - 346282 = fullRecordGapValue01371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01371 (fullRecordGapValue01371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01371_not_prime : ¬(recordGapCenter - 346282).Prime := by
  rw [fullRecordGapTerm01371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01371_fast_pow_mod_ne_one

def fullRecordGapValue01372 : Nat := fullRecordGapCenterValue - 346168

theorem fullRecordGapTerm01372_eq_value :
    recordGapCenter - 346168 = fullRecordGapValue01372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01372 (fullRecordGapValue01372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01372_not_prime : ¬(recordGapCenter - 346168).Prime := by
  rw [fullRecordGapTerm01372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01372_fast_pow_mod_ne_one

def fullRecordGapValue01373 : Nat := fullRecordGapCenterValue - 346162

theorem fullRecordGapTerm01373_eq_value :
    recordGapCenter - 346162 = fullRecordGapValue01373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01373 (fullRecordGapValue01373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01373_not_prime : ¬(recordGapCenter - 346162).Prime := by
  rw [fullRecordGapTerm01373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01373_fast_pow_mod_ne_one

def fullRecordGapValue01374 : Nat := fullRecordGapCenterValue - 346078

theorem fullRecordGapTerm01374_eq_value :
    recordGapCenter - 346078 = fullRecordGapValue01374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01374 (fullRecordGapValue01374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01374_not_prime : ¬(recordGapCenter - 346078).Prime := by
  rw [fullRecordGapTerm01374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01374_fast_pow_mod_ne_one

def fullRecordGapValue01375 : Nat := fullRecordGapCenterValue - 346002

theorem fullRecordGapTerm01375_eq_value :
    recordGapCenter - 346002 = fullRecordGapValue01375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01375 (fullRecordGapValue01375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01375_not_prime : ¬(recordGapCenter - 346002).Prime := by
  rw [fullRecordGapTerm01375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01375_fast_pow_mod_ne_one

def fullRecordGapValue01376 : Nat := fullRecordGapCenterValue - 345964

theorem fullRecordGapTerm01376_eq_value :
    recordGapCenter - 345964 = fullRecordGapValue01376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01376 (fullRecordGapValue01376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01376_not_prime : ¬(recordGapCenter - 345964).Prime := by
  rw [fullRecordGapTerm01376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01376_fast_pow_mod_ne_one

def fullRecordGapValue01377 : Nat := fullRecordGapCenterValue - 345784

theorem fullRecordGapTerm01377_eq_value :
    recordGapCenter - 345784 = fullRecordGapValue01377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01377 (fullRecordGapValue01377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01377_not_prime : ¬(recordGapCenter - 345784).Prime := by
  rw [fullRecordGapTerm01377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01377_fast_pow_mod_ne_one

def fullRecordGapValue01378 : Nat := fullRecordGapCenterValue - 345754

theorem fullRecordGapTerm01378_eq_value :
    recordGapCenter - 345754 = fullRecordGapValue01378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01378 (fullRecordGapValue01378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01378_not_prime : ¬(recordGapCenter - 345754).Prime := by
  rw [fullRecordGapTerm01378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01378_fast_pow_mod_ne_one

def fullRecordGapValue01379 : Nat := fullRecordGapCenterValue - 345744

theorem fullRecordGapTerm01379_eq_value :
    recordGapCenter - 345744 = fullRecordGapValue01379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01379 (fullRecordGapValue01379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01379_not_prime : ¬(recordGapCenter - 345744).Prime := by
  rw [fullRecordGapTerm01379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01379_fast_pow_mod_ne_one

def fullRecordGapValue01380 : Nat := fullRecordGapCenterValue - 345742

theorem fullRecordGapTerm01380_eq_value :
    recordGapCenter - 345742 = fullRecordGapValue01380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01380 (fullRecordGapValue01380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01380_not_prime : ¬(recordGapCenter - 345742).Prime := by
  rw [fullRecordGapTerm01380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01380_fast_pow_mod_ne_one

def fullRecordGapValue01381 : Nat := fullRecordGapCenterValue - 345718

theorem fullRecordGapTerm01381_eq_value :
    recordGapCenter - 345718 = fullRecordGapValue01381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01381 (fullRecordGapValue01381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01381_not_prime : ¬(recordGapCenter - 345718).Prime := by
  rw [fullRecordGapTerm01381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01381_fast_pow_mod_ne_one

def fullRecordGapValue01382 : Nat := fullRecordGapCenterValue - 345658

theorem fullRecordGapTerm01382_eq_value :
    recordGapCenter - 345658 = fullRecordGapValue01382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01382 (fullRecordGapValue01382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01382_not_prime : ¬(recordGapCenter - 345658).Prime := by
  rw [fullRecordGapTerm01382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01382_fast_pow_mod_ne_one

def fullRecordGapValue01383 : Nat := fullRecordGapCenterValue - 345652

theorem fullRecordGapTerm01383_eq_value :
    recordGapCenter - 345652 = fullRecordGapValue01383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01383 (fullRecordGapValue01383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01383_not_prime : ¬(recordGapCenter - 345652).Prime := by
  rw [fullRecordGapTerm01383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01383_fast_pow_mod_ne_one

def fullRecordGapValue01384 : Nat := fullRecordGapCenterValue - 345600

theorem fullRecordGapTerm01384_eq_value :
    recordGapCenter - 345600 = fullRecordGapValue01384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01384 (fullRecordGapValue01384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01384_not_prime : ¬(recordGapCenter - 345600).Prime := by
  rw [fullRecordGapTerm01384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01384_fast_pow_mod_ne_one

def fullRecordGapValue01385 : Nat := fullRecordGapCenterValue - 345354

theorem fullRecordGapTerm01385_eq_value :
    recordGapCenter - 345354 = fullRecordGapValue01385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01385 (fullRecordGapValue01385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01385_not_prime : ¬(recordGapCenter - 345354).Prime := by
  rw [fullRecordGapTerm01385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01385_fast_pow_mod_ne_one

def fullRecordGapValue01386 : Nat := fullRecordGapCenterValue - 345342

theorem fullRecordGapTerm01386_eq_value :
    recordGapCenter - 345342 = fullRecordGapValue01386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01386 (fullRecordGapValue01386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01386_not_prime : ¬(recordGapCenter - 345342).Prime := by
  rw [fullRecordGapTerm01386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01386_fast_pow_mod_ne_one

def fullRecordGapValue01387 : Nat := fullRecordGapCenterValue - 345292

theorem fullRecordGapTerm01387_eq_value :
    recordGapCenter - 345292 = fullRecordGapValue01387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01387 (fullRecordGapValue01387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01387_not_prime : ¬(recordGapCenter - 345292).Prime := by
  rw [fullRecordGapTerm01387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01387_fast_pow_mod_ne_one

def fullRecordGapValue01388 : Nat := fullRecordGapCenterValue - 345244

theorem fullRecordGapTerm01388_eq_value :
    recordGapCenter - 345244 = fullRecordGapValue01388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01388 (fullRecordGapValue01388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01388_not_prime : ¬(recordGapCenter - 345244).Prime := by
  rw [fullRecordGapTerm01388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01388_fast_pow_mod_ne_one

def fullRecordGapValue01389 : Nat := fullRecordGapCenterValue - 345208

theorem fullRecordGapTerm01389_eq_value :
    recordGapCenter - 345208 = fullRecordGapValue01389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01389 (fullRecordGapValue01389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01389_not_prime : ¬(recordGapCenter - 345208).Prime := by
  rw [fullRecordGapTerm01389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01389_fast_pow_mod_ne_one

def fullRecordGapValue01390 : Nat := fullRecordGapCenterValue - 345174

theorem fullRecordGapTerm01390_eq_value :
    recordGapCenter - 345174 = fullRecordGapValue01390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01390 (fullRecordGapValue01390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01390_not_prime : ¬(recordGapCenter - 345174).Prime := by
  rw [fullRecordGapTerm01390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01390_fast_pow_mod_ne_one

def fullRecordGapValue01391 : Nat := fullRecordGapCenterValue - 345172

theorem fullRecordGapTerm01391_eq_value :
    recordGapCenter - 345172 = fullRecordGapValue01391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01391 (fullRecordGapValue01391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01391_not_prime : ¬(recordGapCenter - 345172).Prime := by
  rw [fullRecordGapTerm01391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01391_fast_pow_mod_ne_one

def fullRecordGapValue01392 : Nat := fullRecordGapCenterValue - 345064

theorem fullRecordGapTerm01392_eq_value :
    recordGapCenter - 345064 = fullRecordGapValue01392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01392 (fullRecordGapValue01392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01392_not_prime : ¬(recordGapCenter - 345064).Prime := by
  rw [fullRecordGapTerm01392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01392_fast_pow_mod_ne_one

def fullRecordGapValue01393 : Nat := fullRecordGapCenterValue - 345034

theorem fullRecordGapTerm01393_eq_value :
    recordGapCenter - 345034 = fullRecordGapValue01393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01393 (fullRecordGapValue01393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01393_not_prime : ¬(recordGapCenter - 345034).Prime := by
  rw [fullRecordGapTerm01393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01393_fast_pow_mod_ne_one

def fullRecordGapValue01394 : Nat := fullRecordGapCenterValue - 345018

theorem fullRecordGapTerm01394_eq_value :
    recordGapCenter - 345018 = fullRecordGapValue01394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01394 (fullRecordGapValue01394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01394_not_prime : ¬(recordGapCenter - 345018).Prime := by
  rw [fullRecordGapTerm01394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01394_fast_pow_mod_ne_one

def fullRecordGapValue01395 : Nat := fullRecordGapCenterValue - 344958

theorem fullRecordGapTerm01395_eq_value :
    recordGapCenter - 344958 = fullRecordGapValue01395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01395 (fullRecordGapValue01395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01395_not_prime : ¬(recordGapCenter - 344958).Prime := by
  rw [fullRecordGapTerm01395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01395_fast_pow_mod_ne_one

def fullRecordGapValue01396 : Nat := fullRecordGapCenterValue - 344922

theorem fullRecordGapTerm01396_eq_value :
    recordGapCenter - 344922 = fullRecordGapValue01396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01396 (fullRecordGapValue01396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01396_not_prime : ¬(recordGapCenter - 344922).Prime := by
  rw [fullRecordGapTerm01396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01396_fast_pow_mod_ne_one

def fullRecordGapValue01397 : Nat := fullRecordGapCenterValue - 344742

theorem fullRecordGapTerm01397_eq_value :
    recordGapCenter - 344742 = fullRecordGapValue01397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01397 (fullRecordGapValue01397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01397_not_prime : ¬(recordGapCenter - 344742).Prime := by
  rw [fullRecordGapTerm01397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01397_fast_pow_mod_ne_one

def fullRecordGapValue01398 : Nat := fullRecordGapCenterValue - 344662

theorem fullRecordGapTerm01398_eq_value :
    recordGapCenter - 344662 = fullRecordGapValue01398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01398 (fullRecordGapValue01398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01398_not_prime : ¬(recordGapCenter - 344662).Prime := by
  rw [fullRecordGapTerm01398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01398_fast_pow_mod_ne_one

def fullRecordGapValue01399 : Nat := fullRecordGapCenterValue - 344644

theorem fullRecordGapTerm01399_eq_value :
    recordGapCenter - 344644 = fullRecordGapValue01399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01399 (fullRecordGapValue01399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01399_not_prime : ¬(recordGapCenter - 344644).Prime := by
  rw [fullRecordGapTerm01399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01399_fast_pow_mod_ne_one

def fullRecordGapValue01400 : Nat := fullRecordGapCenterValue - 344614

theorem fullRecordGapTerm01400_eq_value :
    recordGapCenter - 344614 = fullRecordGapValue01400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01400 (fullRecordGapValue01400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01400_not_prime : ¬(recordGapCenter - 344614).Prime := by
  rw [fullRecordGapTerm01400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01400_fast_pow_mod_ne_one

def fullRecordGapValue01401 : Nat := fullRecordGapCenterValue - 344572

theorem fullRecordGapTerm01401_eq_value :
    recordGapCenter - 344572 = fullRecordGapValue01401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01401 (fullRecordGapValue01401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01401_not_prime : ¬(recordGapCenter - 344572).Prime := by
  rw [fullRecordGapTerm01401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01401_fast_pow_mod_ne_one

def fullRecordGapValue01402 : Nat := fullRecordGapCenterValue - 344518

theorem fullRecordGapTerm01402_eq_value :
    recordGapCenter - 344518 = fullRecordGapValue01402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01402 (fullRecordGapValue01402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01402_not_prime : ¬(recordGapCenter - 344518).Prime := by
  rw [fullRecordGapTerm01402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01402_fast_pow_mod_ne_one

def fullRecordGapValue01403 : Nat := fullRecordGapCenterValue - 344452

theorem fullRecordGapTerm01403_eq_value :
    recordGapCenter - 344452 = fullRecordGapValue01403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01403 (fullRecordGapValue01403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01403_not_prime : ¬(recordGapCenter - 344452).Prime := by
  rw [fullRecordGapTerm01403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01403_fast_pow_mod_ne_one

def fullRecordGapValue01404 : Nat := fullRecordGapCenterValue - 344334

theorem fullRecordGapTerm01404_eq_value :
    recordGapCenter - 344334 = fullRecordGapValue01404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01404 (fullRecordGapValue01404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01404_not_prime : ¬(recordGapCenter - 344334).Prime := by
  rw [fullRecordGapTerm01404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01404_fast_pow_mod_ne_one

def fullRecordGapValue01405 : Nat := fullRecordGapCenterValue - 344332

theorem fullRecordGapTerm01405_eq_value :
    recordGapCenter - 344332 = fullRecordGapValue01405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01405 (fullRecordGapValue01405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01405_not_prime : ¬(recordGapCenter - 344332).Prime := by
  rw [fullRecordGapTerm01405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01405_fast_pow_mod_ne_one

def fullRecordGapValue01406 : Nat := fullRecordGapCenterValue - 344308

theorem fullRecordGapTerm01406_eq_value :
    recordGapCenter - 344308 = fullRecordGapValue01406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01406 (fullRecordGapValue01406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01406_not_prime : ¬(recordGapCenter - 344308).Prime := by
  rw [fullRecordGapTerm01406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01406_fast_pow_mod_ne_one

def fullRecordGapValue01407 : Nat := fullRecordGapCenterValue - 344298

theorem fullRecordGapTerm01407_eq_value :
    recordGapCenter - 344298 = fullRecordGapValue01407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01407 (fullRecordGapValue01407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01407_not_prime : ¬(recordGapCenter - 344298).Prime := by
  rw [fullRecordGapTerm01407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01407_fast_pow_mod_ne_one

def fullRecordGapValue01408 : Nat := fullRecordGapCenterValue - 344064

theorem fullRecordGapTerm01408_eq_value :
    recordGapCenter - 344064 = fullRecordGapValue01408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01408 (fullRecordGapValue01408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01408_not_prime : ¬(recordGapCenter - 344064).Prime := by
  rw [fullRecordGapTerm01408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01408_fast_pow_mod_ne_one

def fullRecordGapValue01409 : Nat := fullRecordGapCenterValue - 343762

theorem fullRecordGapTerm01409_eq_value :
    recordGapCenter - 343762 = fullRecordGapValue01409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01409 (fullRecordGapValue01409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01409_not_prime : ¬(recordGapCenter - 343762).Prime := by
  rw [fullRecordGapTerm01409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01409_fast_pow_mod_ne_one

def fullRecordGapValue01410 : Nat := fullRecordGapCenterValue - 343738

theorem fullRecordGapTerm01410_eq_value :
    recordGapCenter - 343738 = fullRecordGapValue01410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01410 (fullRecordGapValue01410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01410_not_prime : ¬(recordGapCenter - 343738).Prime := by
  rw [fullRecordGapTerm01410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01410_fast_pow_mod_ne_one

def fullRecordGapValue01411 : Nat := fullRecordGapCenterValue - 343614

theorem fullRecordGapTerm01411_eq_value :
    recordGapCenter - 343614 = fullRecordGapValue01411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01411 (fullRecordGapValue01411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01411_not_prime : ¬(recordGapCenter - 343614).Prime := by
  rw [fullRecordGapTerm01411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01411_fast_pow_mod_ne_one

def fullRecordGapValue01412 : Nat := fullRecordGapCenterValue - 343612

theorem fullRecordGapTerm01412_eq_value :
    recordGapCenter - 343612 = fullRecordGapValue01412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01412 (fullRecordGapValue01412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01412_not_prime : ¬(recordGapCenter - 343612).Prime := by
  rw [fullRecordGapTerm01412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01412_fast_pow_mod_ne_one

def fullRecordGapValue01413 : Nat := fullRecordGapCenterValue - 343522

theorem fullRecordGapTerm01413_eq_value :
    recordGapCenter - 343522 = fullRecordGapValue01413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01413 (fullRecordGapValue01413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01413_not_prime : ¬(recordGapCenter - 343522).Prime := by
  rw [fullRecordGapTerm01413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01413_fast_pow_mod_ne_one

def fullRecordGapValue01414 : Nat := fullRecordGapCenterValue - 343318

theorem fullRecordGapTerm01414_eq_value :
    recordGapCenter - 343318 = fullRecordGapValue01414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01414 (fullRecordGapValue01414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01414_not_prime : ¬(recordGapCenter - 343318).Prime := by
  rw [fullRecordGapTerm01414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01414_fast_pow_mod_ne_one

def fullRecordGapValue01415 : Nat := fullRecordGapCenterValue - 342898

theorem fullRecordGapTerm01415_eq_value :
    recordGapCenter - 342898 = fullRecordGapValue01415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01415 (fullRecordGapValue01415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01415_not_prime : ¬(recordGapCenter - 342898).Prime := by
  rw [fullRecordGapTerm01415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01415_fast_pow_mod_ne_one

def fullRecordGapValue01416 : Nat := fullRecordGapCenterValue - 342682

theorem fullRecordGapTerm01416_eq_value :
    recordGapCenter - 342682 = fullRecordGapValue01416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01416 (fullRecordGapValue01416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01416_not_prime : ¬(recordGapCenter - 342682).Prime := by
  rw [fullRecordGapTerm01416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01416_fast_pow_mod_ne_one

def fullRecordGapValue01417 : Nat := fullRecordGapCenterValue - 342634

theorem fullRecordGapTerm01417_eq_value :
    recordGapCenter - 342634 = fullRecordGapValue01417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01417 (fullRecordGapValue01417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01417_not_prime : ¬(recordGapCenter - 342634).Prime := by
  rw [fullRecordGapTerm01417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01417_fast_pow_mod_ne_one

def fullRecordGapValue01418 : Nat := fullRecordGapCenterValue - 342534

theorem fullRecordGapTerm01418_eq_value :
    recordGapCenter - 342534 = fullRecordGapValue01418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01418 (fullRecordGapValue01418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01418_not_prime : ¬(recordGapCenter - 342534).Prime := by
  rw [fullRecordGapTerm01418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01418_fast_pow_mod_ne_one

def fullRecordGapValue01419 : Nat := fullRecordGapCenterValue - 342508

theorem fullRecordGapTerm01419_eq_value :
    recordGapCenter - 342508 = fullRecordGapValue01419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01419 (fullRecordGapValue01419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01419_not_prime : ¬(recordGapCenter - 342508).Prime := by
  rw [fullRecordGapTerm01419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01419_fast_pow_mod_ne_one

def fullRecordGapValue01420 : Nat := fullRecordGapCenterValue - 342502

theorem fullRecordGapTerm01420_eq_value :
    recordGapCenter - 342502 = fullRecordGapValue01420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01420 (fullRecordGapValue01420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01420_not_prime : ¬(recordGapCenter - 342502).Prime := by
  rw [fullRecordGapTerm01420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01420_fast_pow_mod_ne_one

def fullRecordGapValue01421 : Nat := fullRecordGapCenterValue - 342484

theorem fullRecordGapTerm01421_eq_value :
    recordGapCenter - 342484 = fullRecordGapValue01421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01421 (fullRecordGapValue01421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01421_not_prime : ¬(recordGapCenter - 342484).Prime := by
  rw [fullRecordGapTerm01421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01421_fast_pow_mod_ne_one

def fullRecordGapValue01422 : Nat := fullRecordGapCenterValue - 342438

theorem fullRecordGapTerm01422_eq_value :
    recordGapCenter - 342438 = fullRecordGapValue01422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01422 (fullRecordGapValue01422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01422_not_prime : ¬(recordGapCenter - 342438).Prime := by
  rw [fullRecordGapTerm01422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01422_fast_pow_mod_ne_one

def fullRecordGapValue01423 : Nat := fullRecordGapCenterValue - 342388

theorem fullRecordGapTerm01423_eq_value :
    recordGapCenter - 342388 = fullRecordGapValue01423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01423 (fullRecordGapValue01423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01423_not_prime : ¬(recordGapCenter - 342388).Prime := by
  rw [fullRecordGapTerm01423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01423_fast_pow_mod_ne_one

def fullRecordGapValue01424 : Nat := fullRecordGapCenterValue - 342124

theorem fullRecordGapTerm01424_eq_value :
    recordGapCenter - 342124 = fullRecordGapValue01424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01424 (fullRecordGapValue01424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01424_not_prime : ¬(recordGapCenter - 342124).Prime := by
  rw [fullRecordGapTerm01424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01424_fast_pow_mod_ne_one

def fullRecordGapValue01425 : Nat := fullRecordGapCenterValue - 342094

theorem fullRecordGapTerm01425_eq_value :
    recordGapCenter - 342094 = fullRecordGapValue01425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01425 (fullRecordGapValue01425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01425_not_prime : ¬(recordGapCenter - 342094).Prime := by
  rw [fullRecordGapTerm01425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01425_fast_pow_mod_ne_one

def fullRecordGapValue01426 : Nat := fullRecordGapCenterValue - 342052

theorem fullRecordGapTerm01426_eq_value :
    recordGapCenter - 342052 = fullRecordGapValue01426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01426 (fullRecordGapValue01426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01426_not_prime : ¬(recordGapCenter - 342052).Prime := by
  rw [fullRecordGapTerm01426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01426_fast_pow_mod_ne_one

def fullRecordGapValue01427 : Nat := fullRecordGapCenterValue - 341914

theorem fullRecordGapTerm01427_eq_value :
    recordGapCenter - 341914 = fullRecordGapValue01427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01427 (fullRecordGapValue01427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01427_not_prime : ¬(recordGapCenter - 341914).Prime := by
  rw [fullRecordGapTerm01427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01427_fast_pow_mod_ne_one

def fullRecordGapValue01428 : Nat := fullRecordGapCenterValue - 341898

theorem fullRecordGapTerm01428_eq_value :
    recordGapCenter - 341898 = fullRecordGapValue01428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01428 (fullRecordGapValue01428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01428_not_prime : ¬(recordGapCenter - 341898).Prime := by
  rw [fullRecordGapTerm01428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01428_fast_pow_mod_ne_one

def fullRecordGapValue01429 : Nat := fullRecordGapCenterValue - 341854

theorem fullRecordGapTerm01429_eq_value :
    recordGapCenter - 341854 = fullRecordGapValue01429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01429 (fullRecordGapValue01429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01429_not_prime : ¬(recordGapCenter - 341854).Prime := by
  rw [fullRecordGapTerm01429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01429_fast_pow_mod_ne_one

def fullRecordGapValue01430 : Nat := fullRecordGapCenterValue - 341812

theorem fullRecordGapTerm01430_eq_value :
    recordGapCenter - 341812 = fullRecordGapValue01430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01430 (fullRecordGapValue01430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01430_not_prime : ¬(recordGapCenter - 341812).Prime := by
  rw [fullRecordGapTerm01430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01430_fast_pow_mod_ne_one

def fullRecordGapValue01431 : Nat := fullRecordGapCenterValue - 341742

theorem fullRecordGapTerm01431_eq_value :
    recordGapCenter - 341742 = fullRecordGapValue01431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01431 (fullRecordGapValue01431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01431_not_prime : ¬(recordGapCenter - 341742).Prime := by
  rw [fullRecordGapTerm01431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01431_fast_pow_mod_ne_one

def fullRecordGapValue01432 : Nat := fullRecordGapCenterValue - 341358

theorem fullRecordGapTerm01432_eq_value :
    recordGapCenter - 341358 = fullRecordGapValue01432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01432 (fullRecordGapValue01432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01432_not_prime : ¬(recordGapCenter - 341358).Prime := by
  rw [fullRecordGapTerm01432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01432_fast_pow_mod_ne_one

def fullRecordGapValue01433 : Nat := fullRecordGapCenterValue - 341338

theorem fullRecordGapTerm01433_eq_value :
    recordGapCenter - 341338 = fullRecordGapValue01433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01433 (fullRecordGapValue01433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01433_not_prime : ¬(recordGapCenter - 341338).Prime := by
  rw [fullRecordGapTerm01433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01433_fast_pow_mod_ne_one

def fullRecordGapValue01434 : Nat := fullRecordGapCenterValue - 341218

theorem fullRecordGapTerm01434_eq_value :
    recordGapCenter - 341218 = fullRecordGapValue01434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01434 (fullRecordGapValue01434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01434_not_prime : ¬(recordGapCenter - 341218).Prime := by
  rw [fullRecordGapTerm01434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01434_fast_pow_mod_ne_one

def fullRecordGapValue01435 : Nat := fullRecordGapCenterValue - 341212

theorem fullRecordGapTerm01435_eq_value :
    recordGapCenter - 341212 = fullRecordGapValue01435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01435 (fullRecordGapValue01435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01435_not_prime : ¬(recordGapCenter - 341212).Prime := by
  rw [fullRecordGapTerm01435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01435_fast_pow_mod_ne_one

def fullRecordGapValue01436 : Nat := fullRecordGapCenterValue - 341142

theorem fullRecordGapTerm01436_eq_value :
    recordGapCenter - 341142 = fullRecordGapValue01436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01436 (fullRecordGapValue01436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01436_not_prime : ¬(recordGapCenter - 341142).Prime := by
  rw [fullRecordGapTerm01436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01436_fast_pow_mod_ne_one

def fullRecordGapValue01437 : Nat := fullRecordGapCenterValue - 341058

theorem fullRecordGapTerm01437_eq_value :
    recordGapCenter - 341058 = fullRecordGapValue01437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01437 (fullRecordGapValue01437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01437_not_prime : ¬(recordGapCenter - 341058).Prime := by
  rw [fullRecordGapTerm01437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01437_fast_pow_mod_ne_one

def fullRecordGapValue01438 : Nat := fullRecordGapCenterValue - 340972

theorem fullRecordGapTerm01438_eq_value :
    recordGapCenter - 340972 = fullRecordGapValue01438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01438 (fullRecordGapValue01438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01438_not_prime : ¬(recordGapCenter - 340972).Prime := by
  rw [fullRecordGapTerm01438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01438_fast_pow_mod_ne_one

def fullRecordGapValue01439 : Nat := fullRecordGapCenterValue - 340962

theorem fullRecordGapTerm01439_eq_value :
    recordGapCenter - 340962 = fullRecordGapValue01439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01439 (fullRecordGapValue01439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01439_not_prime : ¬(recordGapCenter - 340962).Prime := by
  rw [fullRecordGapTerm01439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01439_fast_pow_mod_ne_one

def fullRecordGapValue01440 : Nat := fullRecordGapCenterValue - 340878

theorem fullRecordGapTerm01440_eq_value :
    recordGapCenter - 340878 = fullRecordGapValue01440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01440 (fullRecordGapValue01440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01440_not_prime : ¬(recordGapCenter - 340878).Prime := by
  rw [fullRecordGapTerm01440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01440_fast_pow_mod_ne_one

def fullRecordGapValue01441 : Nat := fullRecordGapCenterValue - 340854

theorem fullRecordGapTerm01441_eq_value :
    recordGapCenter - 340854 = fullRecordGapValue01441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01441 (fullRecordGapValue01441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01441_not_prime : ¬(recordGapCenter - 340854).Prime := by
  rw [fullRecordGapTerm01441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01441_fast_pow_mod_ne_one

def fullRecordGapValue01442 : Nat := fullRecordGapCenterValue - 340702

theorem fullRecordGapTerm01442_eq_value :
    recordGapCenter - 340702 = fullRecordGapValue01442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01442 (fullRecordGapValue01442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01442_not_prime : ¬(recordGapCenter - 340702).Prime := by
  rw [fullRecordGapTerm01442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01442_fast_pow_mod_ne_one

def fullRecordGapValue01443 : Nat := fullRecordGapCenterValue - 340638

theorem fullRecordGapTerm01443_eq_value :
    recordGapCenter - 340638 = fullRecordGapValue01443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01443 (fullRecordGapValue01443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01443_not_prime : ¬(recordGapCenter - 340638).Prime := by
  rw [fullRecordGapTerm01443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01443_fast_pow_mod_ne_one

def fullRecordGapValue01444 : Nat := fullRecordGapCenterValue - 340534

theorem fullRecordGapTerm01444_eq_value :
    recordGapCenter - 340534 = fullRecordGapValue01444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01444 (fullRecordGapValue01444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01444_not_prime : ¬(recordGapCenter - 340534).Prime := by
  rw [fullRecordGapTerm01444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01444_fast_pow_mod_ne_one

def fullRecordGapValue01445 : Nat := fullRecordGapCenterValue - 340422

theorem fullRecordGapTerm01445_eq_value :
    recordGapCenter - 340422 = fullRecordGapValue01445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01445 (fullRecordGapValue01445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01445_not_prime : ¬(recordGapCenter - 340422).Prime := by
  rw [fullRecordGapTerm01445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01445_fast_pow_mod_ne_one

def fullRecordGapValue01446 : Nat := fullRecordGapCenterValue - 340378

theorem fullRecordGapTerm01446_eq_value :
    recordGapCenter - 340378 = fullRecordGapValue01446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01446 (fullRecordGapValue01446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01446_not_prime : ¬(recordGapCenter - 340378).Prime := by
  rw [fullRecordGapTerm01446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01446_fast_pow_mod_ne_one

def fullRecordGapValue01447 : Nat := fullRecordGapCenterValue - 340372

theorem fullRecordGapTerm01447_eq_value :
    recordGapCenter - 340372 = fullRecordGapValue01447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01447 (fullRecordGapValue01447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01447_not_prime : ¬(recordGapCenter - 340372).Prime := by
  rw [fullRecordGapTerm01447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01447_fast_pow_mod_ne_one

def fullRecordGapValue01448 : Nat := fullRecordGapCenterValue - 340324

theorem fullRecordGapTerm01448_eq_value :
    recordGapCenter - 340324 = fullRecordGapValue01448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01448 (fullRecordGapValue01448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01448_not_prime : ¬(recordGapCenter - 340324).Prime := by
  rw [fullRecordGapTerm01448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01448_fast_pow_mod_ne_one

def fullRecordGapValue01449 : Nat := fullRecordGapCenterValue - 340282

theorem fullRecordGapTerm01449_eq_value :
    recordGapCenter - 340282 = fullRecordGapValue01449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01449 (fullRecordGapValue01449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01449_not_prime : ¬(recordGapCenter - 340282).Prime := by
  rw [fullRecordGapTerm01449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01449_fast_pow_mod_ne_one

def fullRecordGapValue01450 : Nat := fullRecordGapCenterValue - 340108

theorem fullRecordGapTerm01450_eq_value :
    recordGapCenter - 340108 = fullRecordGapValue01450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01450 (fullRecordGapValue01450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01450_not_prime : ¬(recordGapCenter - 340108).Prime := by
  rw [fullRecordGapTerm01450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01450_fast_pow_mod_ne_one

def fullRecordGapValue01451 : Nat := fullRecordGapCenterValue - 340084

theorem fullRecordGapTerm01451_eq_value :
    recordGapCenter - 340084 = fullRecordGapValue01451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01451 (fullRecordGapValue01451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01451_not_prime : ¬(recordGapCenter - 340084).Prime := by
  rw [fullRecordGapTerm01451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01451_fast_pow_mod_ne_one

def fullRecordGapValue01452 : Nat := fullRecordGapCenterValue - 340042

theorem fullRecordGapTerm01452_eq_value :
    recordGapCenter - 340042 = fullRecordGapValue01452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01452 (fullRecordGapValue01452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01452_not_prime : ¬(recordGapCenter - 340042).Prime := by
  rw [fullRecordGapTerm01452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01452_fast_pow_mod_ne_one

def fullRecordGapValue01453 : Nat := fullRecordGapCenterValue - 339982

theorem fullRecordGapTerm01453_eq_value :
    recordGapCenter - 339982 = fullRecordGapValue01453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01453 (fullRecordGapValue01453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01453_not_prime : ¬(recordGapCenter - 339982).Prime := by
  rw [fullRecordGapTerm01453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01453_fast_pow_mod_ne_one

def fullRecordGapValue01454 : Nat := fullRecordGapCenterValue - 339964

theorem fullRecordGapTerm01454_eq_value :
    recordGapCenter - 339964 = fullRecordGapValue01454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01454 (fullRecordGapValue01454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01454_not_prime : ¬(recordGapCenter - 339964).Prime := by
  rw [fullRecordGapTerm01454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01454_fast_pow_mod_ne_one

def fullRecordGapValue01455 : Nat := fullRecordGapCenterValue - 339954

theorem fullRecordGapTerm01455_eq_value :
    recordGapCenter - 339954 = fullRecordGapValue01455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01455 (fullRecordGapValue01455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01455_not_prime : ¬(recordGapCenter - 339954).Prime := by
  rw [fullRecordGapTerm01455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01455_fast_pow_mod_ne_one

def fullRecordGapValue01456 : Nat := fullRecordGapCenterValue - 339874

theorem fullRecordGapTerm01456_eq_value :
    recordGapCenter - 339874 = fullRecordGapValue01456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01456 (fullRecordGapValue01456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01456_not_prime : ¬(recordGapCenter - 339874).Prime := by
  rw [fullRecordGapTerm01456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01456_fast_pow_mod_ne_one

def fullRecordGapValue01457 : Nat := fullRecordGapCenterValue - 339868

theorem fullRecordGapTerm01457_eq_value :
    recordGapCenter - 339868 = fullRecordGapValue01457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01457 (fullRecordGapValue01457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01457_not_prime : ¬(recordGapCenter - 339868).Prime := by
  rw [fullRecordGapTerm01457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01457_fast_pow_mod_ne_one

def fullRecordGapValue01458 : Nat := fullRecordGapCenterValue - 339778

theorem fullRecordGapTerm01458_eq_value :
    recordGapCenter - 339778 = fullRecordGapValue01458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01458 (fullRecordGapValue01458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01458_not_prime : ¬(recordGapCenter - 339778).Prime := by
  rw [fullRecordGapTerm01458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01458_fast_pow_mod_ne_one

def fullRecordGapValue01459 : Nat := fullRecordGapCenterValue - 339652

theorem fullRecordGapTerm01459_eq_value :
    recordGapCenter - 339652 = fullRecordGapValue01459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01459 (fullRecordGapValue01459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01459_not_prime : ¬(recordGapCenter - 339652).Prime := by
  rw [fullRecordGapTerm01459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01459_fast_pow_mod_ne_one

def fullRecordGapValue01460 : Nat := fullRecordGapCenterValue - 339594

theorem fullRecordGapTerm01460_eq_value :
    recordGapCenter - 339594 = fullRecordGapValue01460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01460 (fullRecordGapValue01460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01460_not_prime : ¬(recordGapCenter - 339594).Prime := by
  rw [fullRecordGapTerm01460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01460_fast_pow_mod_ne_one

def fullRecordGapValue01461 : Nat := fullRecordGapCenterValue - 339582

theorem fullRecordGapTerm01461_eq_value :
    recordGapCenter - 339582 = fullRecordGapValue01461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01461 (fullRecordGapValue01461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01461_not_prime : ¬(recordGapCenter - 339582).Prime := by
  rw [fullRecordGapTerm01461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01461_fast_pow_mod_ne_one

def fullRecordGapValue01462 : Nat := fullRecordGapCenterValue - 339538

theorem fullRecordGapTerm01462_eq_value :
    recordGapCenter - 339538 = fullRecordGapValue01462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01462 (fullRecordGapValue01462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01462_not_prime : ¬(recordGapCenter - 339538).Prime := by
  rw [fullRecordGapTerm01462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01462_fast_pow_mod_ne_one

def fullRecordGapValue01463 : Nat := fullRecordGapCenterValue - 339418

theorem fullRecordGapTerm01463_eq_value :
    recordGapCenter - 339418 = fullRecordGapValue01463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01463 (fullRecordGapValue01463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01463_not_prime : ¬(recordGapCenter - 339418).Prime := by
  rw [fullRecordGapTerm01463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01463_fast_pow_mod_ne_one

def fullRecordGapValue01464 : Nat := fullRecordGapCenterValue - 339414

theorem fullRecordGapTerm01464_eq_value :
    recordGapCenter - 339414 = fullRecordGapValue01464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01464 (fullRecordGapValue01464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01464_not_prime : ¬(recordGapCenter - 339414).Prime := by
  rw [fullRecordGapTerm01464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01464_fast_pow_mod_ne_one

def fullRecordGapValue01465 : Nat := fullRecordGapCenterValue - 339258

theorem fullRecordGapTerm01465_eq_value :
    recordGapCenter - 339258 = fullRecordGapValue01465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01465 (fullRecordGapValue01465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01465_not_prime : ¬(recordGapCenter - 339258).Prime := by
  rw [fullRecordGapTerm01465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01465_fast_pow_mod_ne_one

def fullRecordGapValue01466 : Nat := fullRecordGapCenterValue - 339198

theorem fullRecordGapTerm01466_eq_value :
    recordGapCenter - 339198 = fullRecordGapValue01466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01466 (fullRecordGapValue01466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01466_not_prime : ¬(recordGapCenter - 339198).Prime := by
  rw [fullRecordGapTerm01466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01466_fast_pow_mod_ne_one

def fullRecordGapValue01467 : Nat := fullRecordGapCenterValue - 339114

theorem fullRecordGapTerm01467_eq_value :
    recordGapCenter - 339114 = fullRecordGapValue01467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01467 (fullRecordGapValue01467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01467_not_prime : ¬(recordGapCenter - 339114).Prime := by
  rw [fullRecordGapTerm01467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01467_fast_pow_mod_ne_one

def fullRecordGapValue01468 : Nat := fullRecordGapCenterValue - 338862

theorem fullRecordGapTerm01468_eq_value :
    recordGapCenter - 338862 = fullRecordGapValue01468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01468 (fullRecordGapValue01468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01468_not_prime : ¬(recordGapCenter - 338862).Prime := by
  rw [fullRecordGapTerm01468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01468_fast_pow_mod_ne_one

def fullRecordGapValue01469 : Nat := fullRecordGapCenterValue - 338818

theorem fullRecordGapTerm01469_eq_value :
    recordGapCenter - 338818 = fullRecordGapValue01469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01469 (fullRecordGapValue01469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01469_not_prime : ¬(recordGapCenter - 338818).Prime := by
  rw [fullRecordGapTerm01469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01469_fast_pow_mod_ne_one

def fullRecordGapValue01470 : Nat := fullRecordGapCenterValue - 338788

theorem fullRecordGapTerm01470_eq_value :
    recordGapCenter - 338788 = fullRecordGapValue01470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01470 (fullRecordGapValue01470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01470_not_prime : ¬(recordGapCenter - 338788).Prime := by
  rw [fullRecordGapTerm01470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01470_fast_pow_mod_ne_one

def fullRecordGapValue01471 : Nat := fullRecordGapCenterValue - 338722

theorem fullRecordGapTerm01471_eq_value :
    recordGapCenter - 338722 = fullRecordGapValue01471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01471 (fullRecordGapValue01471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01471_not_prime : ¬(recordGapCenter - 338722).Prime := by
  rw [fullRecordGapTerm01471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01471_fast_pow_mod_ne_one

def fullRecordGapValue01472 : Nat := fullRecordGapCenterValue - 338692

theorem fullRecordGapTerm01472_eq_value :
    recordGapCenter - 338692 = fullRecordGapValue01472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01472 (fullRecordGapValue01472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01472_not_prime : ¬(recordGapCenter - 338692).Prime := by
  rw [fullRecordGapTerm01472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01472_fast_pow_mod_ne_one

def fullRecordGapValue01473 : Nat := fullRecordGapCenterValue - 338658

theorem fullRecordGapTerm01473_eq_value :
    recordGapCenter - 338658 = fullRecordGapValue01473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01473 (fullRecordGapValue01473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01473_not_prime : ¬(recordGapCenter - 338658).Prime := by
  rw [fullRecordGapTerm01473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01473_fast_pow_mod_ne_one

def fullRecordGapValue01474 : Nat := fullRecordGapCenterValue - 338614

theorem fullRecordGapTerm01474_eq_value :
    recordGapCenter - 338614 = fullRecordGapValue01474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01474 (fullRecordGapValue01474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01474_not_prime : ¬(recordGapCenter - 338614).Prime := by
  rw [fullRecordGapTerm01474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01474_fast_pow_mod_ne_one

def fullRecordGapValue01475 : Nat := fullRecordGapCenterValue - 338502

theorem fullRecordGapTerm01475_eq_value :
    recordGapCenter - 338502 = fullRecordGapValue01475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01475 (fullRecordGapValue01475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01475_not_prime : ¬(recordGapCenter - 338502).Prime := by
  rw [fullRecordGapTerm01475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01475_fast_pow_mod_ne_one

def fullRecordGapValue01476 : Nat := fullRecordGapCenterValue - 338482

theorem fullRecordGapTerm01476_eq_value :
    recordGapCenter - 338482 = fullRecordGapValue01476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01476 (fullRecordGapValue01476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01476_not_prime : ¬(recordGapCenter - 338482).Prime := by
  rw [fullRecordGapTerm01476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01476_fast_pow_mod_ne_one

def fullRecordGapValue01477 : Nat := fullRecordGapCenterValue - 338398

theorem fullRecordGapTerm01477_eq_value :
    recordGapCenter - 338398 = fullRecordGapValue01477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01477 (fullRecordGapValue01477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01477_not_prime : ¬(recordGapCenter - 338398).Prime := by
  rw [fullRecordGapTerm01477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01477_fast_pow_mod_ne_one

def fullRecordGapValue01478 : Nat := fullRecordGapCenterValue - 338362

theorem fullRecordGapTerm01478_eq_value :
    recordGapCenter - 338362 = fullRecordGapValue01478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01478 (fullRecordGapValue01478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01478_not_prime : ¬(recordGapCenter - 338362).Prime := by
  rw [fullRecordGapTerm01478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01478_fast_pow_mod_ne_one

def fullRecordGapValue01479 : Nat := fullRecordGapCenterValue - 338158

theorem fullRecordGapTerm01479_eq_value :
    recordGapCenter - 338158 = fullRecordGapValue01479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01479 (fullRecordGapValue01479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01479_not_prime : ¬(recordGapCenter - 338158).Prime := by
  rw [fullRecordGapTerm01479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01479_fast_pow_mod_ne_one

def fullRecordGapValue01480 : Nat := fullRecordGapCenterValue - 338134

theorem fullRecordGapTerm01480_eq_value :
    recordGapCenter - 338134 = fullRecordGapValue01480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01480 (fullRecordGapValue01480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01480_not_prime : ¬(recordGapCenter - 338134).Prime := by
  rw [fullRecordGapTerm01480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01480_fast_pow_mod_ne_one

def fullRecordGapValue01481 : Nat := fullRecordGapCenterValue - 338098

theorem fullRecordGapTerm01481_eq_value :
    recordGapCenter - 338098 = fullRecordGapValue01481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01481 (fullRecordGapValue01481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01481_not_prime : ¬(recordGapCenter - 338098).Prime := by
  rw [fullRecordGapTerm01481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01481_fast_pow_mod_ne_one

def fullRecordGapValue01482 : Nat := fullRecordGapCenterValue - 338014

theorem fullRecordGapTerm01482_eq_value :
    recordGapCenter - 338014 = fullRecordGapValue01482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01482 (fullRecordGapValue01482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01482_not_prime : ¬(recordGapCenter - 338014).Prime := by
  rw [fullRecordGapTerm01482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01482_fast_pow_mod_ne_one

def fullRecordGapValue01483 : Nat := fullRecordGapCenterValue - 337998

theorem fullRecordGapTerm01483_eq_value :
    recordGapCenter - 337998 = fullRecordGapValue01483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01483 (fullRecordGapValue01483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01483_not_prime : ¬(recordGapCenter - 337998).Prime := by
  rw [fullRecordGapTerm01483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01483_fast_pow_mod_ne_one

def fullRecordGapValue01484 : Nat := fullRecordGapCenterValue - 337920

theorem fullRecordGapTerm01484_eq_value :
    recordGapCenter - 337920 = fullRecordGapValue01484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01484 (fullRecordGapValue01484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01484_not_prime : ¬(recordGapCenter - 337920).Prime := by
  rw [fullRecordGapTerm01484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01484_fast_pow_mod_ne_one

def fullRecordGapValue01485 : Nat := fullRecordGapCenterValue - 337798

theorem fullRecordGapTerm01485_eq_value :
    recordGapCenter - 337798 = fullRecordGapValue01485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01485 (fullRecordGapValue01485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01485_not_prime : ¬(recordGapCenter - 337798).Prime := by
  rw [fullRecordGapTerm01485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01485_fast_pow_mod_ne_one

def fullRecordGapValue01486 : Nat := fullRecordGapCenterValue - 337774

theorem fullRecordGapTerm01486_eq_value :
    recordGapCenter - 337774 = fullRecordGapValue01486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01486 (fullRecordGapValue01486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01486_not_prime : ¬(recordGapCenter - 337774).Prime := by
  rw [fullRecordGapTerm01486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01486_fast_pow_mod_ne_one

def fullRecordGapValue01487 : Nat := fullRecordGapCenterValue - 337684

theorem fullRecordGapTerm01487_eq_value :
    recordGapCenter - 337684 = fullRecordGapValue01487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01487 (fullRecordGapValue01487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01487_not_prime : ¬(recordGapCenter - 337684).Prime := by
  rw [fullRecordGapTerm01487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01487_fast_pow_mod_ne_one

def fullRecordGapValue01488 : Nat := fullRecordGapCenterValue - 337602

theorem fullRecordGapTerm01488_eq_value :
    recordGapCenter - 337602 = fullRecordGapValue01488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01488 (fullRecordGapValue01488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01488_not_prime : ¬(recordGapCenter - 337602).Prime := by
  rw [fullRecordGapTerm01488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01488_fast_pow_mod_ne_one

def fullRecordGapValue01489 : Nat := fullRecordGapCenterValue - 337500

theorem fullRecordGapTerm01489_eq_value :
    recordGapCenter - 337500 = fullRecordGapValue01489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01489 (fullRecordGapValue01489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01489_not_prime : ¬(recordGapCenter - 337500).Prime := by
  rw [fullRecordGapTerm01489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01489_fast_pow_mod_ne_one

def fullRecordGapValue01490 : Nat := fullRecordGapCenterValue - 337438

theorem fullRecordGapTerm01490_eq_value :
    recordGapCenter - 337438 = fullRecordGapValue01490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01490 (fullRecordGapValue01490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01490_not_prime : ¬(recordGapCenter - 337438).Prime := by
  rw [fullRecordGapTerm01490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01490_fast_pow_mod_ne_one

def fullRecordGapValue01491 : Nat := fullRecordGapCenterValue - 337354

theorem fullRecordGapTerm01491_eq_value :
    recordGapCenter - 337354 = fullRecordGapValue01491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01491 (fullRecordGapValue01491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01491_not_prime : ¬(recordGapCenter - 337354).Prime := by
  rw [fullRecordGapTerm01491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01491_fast_pow_mod_ne_one

def fullRecordGapValue01492 : Nat := fullRecordGapCenterValue - 337252

theorem fullRecordGapTerm01492_eq_value :
    recordGapCenter - 337252 = fullRecordGapValue01492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01492 (fullRecordGapValue01492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01492_not_prime : ¬(recordGapCenter - 337252).Prime := by
  rw [fullRecordGapTerm01492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01492_fast_pow_mod_ne_one

def fullRecordGapValue01493 : Nat := fullRecordGapCenterValue - 337234

theorem fullRecordGapTerm01493_eq_value :
    recordGapCenter - 337234 = fullRecordGapValue01493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01493 (fullRecordGapValue01493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01493_not_prime : ¬(recordGapCenter - 337234).Prime := by
  rw [fullRecordGapTerm01493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01493_fast_pow_mod_ne_one

def fullRecordGapValue01494 : Nat := fullRecordGapCenterValue - 337228

theorem fullRecordGapTerm01494_eq_value :
    recordGapCenter - 337228 = fullRecordGapValue01494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01494 (fullRecordGapValue01494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01494_not_prime : ¬(recordGapCenter - 337228).Prime := by
  rw [fullRecordGapTerm01494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01494_fast_pow_mod_ne_one

def fullRecordGapValue01495 : Nat := fullRecordGapCenterValue - 337074

theorem fullRecordGapTerm01495_eq_value :
    recordGapCenter - 337074 = fullRecordGapValue01495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01495 (fullRecordGapValue01495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01495_not_prime : ¬(recordGapCenter - 337074).Prime := by
  rw [fullRecordGapTerm01495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01495_fast_pow_mod_ne_one

def fullRecordGapValue01496 : Nat := fullRecordGapCenterValue - 337054

theorem fullRecordGapTerm01496_eq_value :
    recordGapCenter - 337054 = fullRecordGapValue01496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01496 (fullRecordGapValue01496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01496_not_prime : ¬(recordGapCenter - 337054).Prime := by
  rw [fullRecordGapTerm01496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01496_fast_pow_mod_ne_one

def fullRecordGapValue01497 : Nat := fullRecordGapCenterValue - 336898

theorem fullRecordGapTerm01497_eq_value :
    recordGapCenter - 336898 = fullRecordGapValue01497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01497 (fullRecordGapValue01497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01497_not_prime : ¬(recordGapCenter - 336898).Prime := by
  rw [fullRecordGapTerm01497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01497_fast_pow_mod_ne_one

def fullRecordGapValue01498 : Nat := fullRecordGapCenterValue - 336892

theorem fullRecordGapTerm01498_eq_value :
    recordGapCenter - 336892 = fullRecordGapValue01498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01498 (fullRecordGapValue01498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01498_not_prime : ¬(recordGapCenter - 336892).Prime := by
  rw [fullRecordGapTerm01498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01498_fast_pow_mod_ne_one

def fullRecordGapValue01499 : Nat := fullRecordGapCenterValue - 336844

theorem fullRecordGapTerm01499_eq_value :
    recordGapCenter - 336844 = fullRecordGapValue01499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01499 (fullRecordGapValue01499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01499_not_prime : ¬(recordGapCenter - 336844).Prime := by
  rw [fullRecordGapTerm01499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01499_fast_pow_mod_ne_one

def fullRecordGapValue01500 : Nat := fullRecordGapCenterValue - 336798

theorem fullRecordGapTerm01500_eq_value :
    recordGapCenter - 336798 = fullRecordGapValue01500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01500 (fullRecordGapValue01500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01500_not_prime : ¬(recordGapCenter - 336798).Prime := by
  rw [fullRecordGapTerm01500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01500_fast_pow_mod_ne_one

def fullRecordGapValue01501 : Nat := fullRecordGapCenterValue - 336594

theorem fullRecordGapTerm01501_eq_value :
    recordGapCenter - 336594 = fullRecordGapValue01501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01501 (fullRecordGapValue01501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01501_not_prime : ¬(recordGapCenter - 336594).Prime := by
  rw [fullRecordGapTerm01501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01501_fast_pow_mod_ne_one

def fullRecordGapValue01502 : Nat := fullRecordGapCenterValue - 336508

theorem fullRecordGapTerm01502_eq_value :
    recordGapCenter - 336508 = fullRecordGapValue01502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01502 (fullRecordGapValue01502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01502_not_prime : ¬(recordGapCenter - 336508).Prime := by
  rw [fullRecordGapTerm01502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01502_fast_pow_mod_ne_one

def fullRecordGapValue01503 : Nat := fullRecordGapCenterValue - 336394

theorem fullRecordGapTerm01503_eq_value :
    recordGapCenter - 336394 = fullRecordGapValue01503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01503 (fullRecordGapValue01503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01503_not_prime : ¬(recordGapCenter - 336394).Prime := by
  rw [fullRecordGapTerm01503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01503_fast_pow_mod_ne_one

def fullRecordGapValue01504 : Nat := fullRecordGapCenterValue - 336268

theorem fullRecordGapTerm01504_eq_value :
    recordGapCenter - 336268 = fullRecordGapValue01504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01504 (fullRecordGapValue01504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01504_not_prime : ¬(recordGapCenter - 336268).Prime := by
  rw [fullRecordGapTerm01504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01504_fast_pow_mod_ne_one

def fullRecordGapValue01505 : Nat := fullRecordGapCenterValue - 336244

theorem fullRecordGapTerm01505_eq_value :
    recordGapCenter - 336244 = fullRecordGapValue01505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01505 (fullRecordGapValue01505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01505_not_prime : ¬(recordGapCenter - 336244).Prime := by
  rw [fullRecordGapTerm01505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01505_fast_pow_mod_ne_one

def fullRecordGapValue01506 : Nat := fullRecordGapCenterValue - 336178

theorem fullRecordGapTerm01506_eq_value :
    recordGapCenter - 336178 = fullRecordGapValue01506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01506 (fullRecordGapValue01506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01506_not_prime : ¬(recordGapCenter - 336178).Prime := by
  rw [fullRecordGapTerm01506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01506_fast_pow_mod_ne_one

def fullRecordGapValue01507 : Nat := fullRecordGapCenterValue - 335932

theorem fullRecordGapTerm01507_eq_value :
    recordGapCenter - 335932 = fullRecordGapValue01507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01507 (fullRecordGapValue01507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01507_not_prime : ¬(recordGapCenter - 335932).Prime := by
  rw [fullRecordGapTerm01507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01507_fast_pow_mod_ne_one

def fullRecordGapValue01508 : Nat := fullRecordGapCenterValue - 335802

theorem fullRecordGapTerm01508_eq_value :
    recordGapCenter - 335802 = fullRecordGapValue01508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01508 (fullRecordGapValue01508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01508_not_prime : ¬(recordGapCenter - 335802).Prime := by
  rw [fullRecordGapTerm01508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01508_fast_pow_mod_ne_one

def fullRecordGapValue01509 : Nat := fullRecordGapCenterValue - 335782

theorem fullRecordGapTerm01509_eq_value :
    recordGapCenter - 335782 = fullRecordGapValue01509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01509 (fullRecordGapValue01509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01509_not_prime : ¬(recordGapCenter - 335782).Prime := by
  rw [fullRecordGapTerm01509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01509_fast_pow_mod_ne_one

def fullRecordGapValue01510 : Nat := fullRecordGapCenterValue - 335758

theorem fullRecordGapTerm01510_eq_value :
    recordGapCenter - 335758 = fullRecordGapValue01510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01510 (fullRecordGapValue01510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01510_not_prime : ¬(recordGapCenter - 335758).Prime := by
  rw [fullRecordGapTerm01510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01510_fast_pow_mod_ne_one

def fullRecordGapValue01511 : Nat := fullRecordGapCenterValue - 335554

theorem fullRecordGapTerm01511_eq_value :
    recordGapCenter - 335554 = fullRecordGapValue01511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01511 (fullRecordGapValue01511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01511_not_prime : ¬(recordGapCenter - 335554).Prime := by
  rw [fullRecordGapTerm01511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01511_fast_pow_mod_ne_one

def fullRecordGapValue01512 : Nat := fullRecordGapCenterValue - 335494

theorem fullRecordGapTerm01512_eq_value :
    recordGapCenter - 335494 = fullRecordGapValue01512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01512 (fullRecordGapValue01512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01512_not_prime : ¬(recordGapCenter - 335494).Prime := by
  rw [fullRecordGapTerm01512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01512_fast_pow_mod_ne_one

def fullRecordGapValue01513 : Nat := fullRecordGapCenterValue - 335458

theorem fullRecordGapTerm01513_eq_value :
    recordGapCenter - 335458 = fullRecordGapValue01513 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01513_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01513 (fullRecordGapValue01513 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01513_not_prime : ¬(recordGapCenter - 335458).Prime := by
  rw [fullRecordGapTerm01513_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01513, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01513_fast_pow_mod_ne_one

def fullRecordGapValue01514 : Nat := fullRecordGapCenterValue - 335382

theorem fullRecordGapTerm01514_eq_value :
    recordGapCenter - 335382 = fullRecordGapValue01514 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01514_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01514 (fullRecordGapValue01514 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01514_not_prime : ¬(recordGapCenter - 335382).Prime := by
  rw [fullRecordGapTerm01514_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01514, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01514_fast_pow_mod_ne_one

def fullRecordGapValue01515 : Nat := fullRecordGapCenterValue - 335254

theorem fullRecordGapTerm01515_eq_value :
    recordGapCenter - 335254 = fullRecordGapValue01515 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01515_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01515 (fullRecordGapValue01515 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01515_not_prime : ¬(recordGapCenter - 335254).Prime := by
  rw [fullRecordGapTerm01515_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01515, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01515_fast_pow_mod_ne_one

def fullRecordGapValue01516 : Nat := fullRecordGapCenterValue - 335194

theorem fullRecordGapTerm01516_eq_value :
    recordGapCenter - 335194 = fullRecordGapValue01516 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01516_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01516 (fullRecordGapValue01516 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01516_not_prime : ¬(recordGapCenter - 335194).Prime := by
  rw [fullRecordGapTerm01516_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01516, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01516_fast_pow_mod_ne_one

def fullRecordGapValue01517 : Nat := fullRecordGapCenterValue - 335092

theorem fullRecordGapTerm01517_eq_value :
    recordGapCenter - 335092 = fullRecordGapValue01517 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01517_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01517 (fullRecordGapValue01517 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01517_not_prime : ¬(recordGapCenter - 335092).Prime := by
  rw [fullRecordGapTerm01517_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01517, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01517_fast_pow_mod_ne_one

def fullRecordGapValue01518 : Nat := fullRecordGapCenterValue - 335058

theorem fullRecordGapTerm01518_eq_value :
    recordGapCenter - 335058 = fullRecordGapValue01518 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01518_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01518 (fullRecordGapValue01518 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01518_not_prime : ¬(recordGapCenter - 335058).Prime := by
  rw [fullRecordGapTerm01518_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01518, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01518_fast_pow_mod_ne_one

def fullRecordGapValue01519 : Nat := fullRecordGapCenterValue - 335022

theorem fullRecordGapTerm01519_eq_value :
    recordGapCenter - 335022 = fullRecordGapValue01519 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01519_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01519 (fullRecordGapValue01519 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01519_not_prime : ¬(recordGapCenter - 335022).Prime := by
  rw [fullRecordGapTerm01519_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01519, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01519_fast_pow_mod_ne_one

def fullRecordGapValue01520 : Nat := fullRecordGapCenterValue - 334974

theorem fullRecordGapTerm01520_eq_value :
    recordGapCenter - 334974 = fullRecordGapValue01520 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01520_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01520 (fullRecordGapValue01520 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01520_not_prime : ¬(recordGapCenter - 334974).Prime := by
  rw [fullRecordGapTerm01520_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01520, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01520_fast_pow_mod_ne_one

def fullRecordGapValue01521 : Nat := fullRecordGapCenterValue - 334942

theorem fullRecordGapTerm01521_eq_value :
    recordGapCenter - 334942 = fullRecordGapValue01521 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01521_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01521 (fullRecordGapValue01521 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01521_not_prime : ¬(recordGapCenter - 334942).Prime := by
  rw [fullRecordGapTerm01521_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01521, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01521_fast_pow_mod_ne_one

def fullRecordGapValue01522 : Nat := fullRecordGapCenterValue - 334914

theorem fullRecordGapTerm01522_eq_value :
    recordGapCenter - 334914 = fullRecordGapValue01522 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01522_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01522 (fullRecordGapValue01522 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01522_not_prime : ¬(recordGapCenter - 334914).Prime := by
  rw [fullRecordGapTerm01522_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01522, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01522_fast_pow_mod_ne_one

def fullRecordGapValue01523 : Nat := fullRecordGapCenterValue - 334758

theorem fullRecordGapTerm01523_eq_value :
    recordGapCenter - 334758 = fullRecordGapValue01523 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01523_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01523 (fullRecordGapValue01523 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01523_not_prime : ¬(recordGapCenter - 334758).Prime := by
  rw [fullRecordGapTerm01523_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01523, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01523_fast_pow_mod_ne_one

def fullRecordGapValue01524 : Nat := fullRecordGapCenterValue - 334612

theorem fullRecordGapTerm01524_eq_value :
    recordGapCenter - 334612 = fullRecordGapValue01524 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01524_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01524 (fullRecordGapValue01524 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01524_not_prime : ¬(recordGapCenter - 334612).Prime := by
  rw [fullRecordGapTerm01524_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01524, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01524_fast_pow_mod_ne_one

def fullRecordGapValue01525 : Nat := fullRecordGapCenterValue - 334534

theorem fullRecordGapTerm01525_eq_value :
    recordGapCenter - 334534 = fullRecordGapValue01525 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01525_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01525 (fullRecordGapValue01525 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01525_not_prime : ¬(recordGapCenter - 334534).Prime := by
  rw [fullRecordGapTerm01525_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01525, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01525_fast_pow_mod_ne_one

def fullRecordGapValue01526 : Nat := fullRecordGapCenterValue - 334522

theorem fullRecordGapTerm01526_eq_value :
    recordGapCenter - 334522 = fullRecordGapValue01526 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01526_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01526 (fullRecordGapValue01526 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01526_not_prime : ¬(recordGapCenter - 334522).Prime := by
  rw [fullRecordGapTerm01526_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01526, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01526_fast_pow_mod_ne_one

def fullRecordGapValue01527 : Nat := fullRecordGapCenterValue - 334498

theorem fullRecordGapTerm01527_eq_value :
    recordGapCenter - 334498 = fullRecordGapValue01527 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01527_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01527 (fullRecordGapValue01527 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01527_not_prime : ¬(recordGapCenter - 334498).Prime := by
  rw [fullRecordGapTerm01527_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01527, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01527_fast_pow_mod_ne_one

def fullRecordGapValue01528 : Nat := fullRecordGapCenterValue - 334302

theorem fullRecordGapTerm01528_eq_value :
    recordGapCenter - 334302 = fullRecordGapValue01528 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01528_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01528 (fullRecordGapValue01528 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01528_not_prime : ¬(recordGapCenter - 334302).Prime := by
  rw [fullRecordGapTerm01528_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01528, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01528_fast_pow_mod_ne_one

def fullRecordGapValue01529 : Nat := fullRecordGapCenterValue - 334234

theorem fullRecordGapTerm01529_eq_value :
    recordGapCenter - 334234 = fullRecordGapValue01529 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01529_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01529 (fullRecordGapValue01529 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01529_not_prime : ¬(recordGapCenter - 334234).Prime := by
  rw [fullRecordGapTerm01529_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01529, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01529_fast_pow_mod_ne_one

def fullRecordGapValue01530 : Nat := fullRecordGapCenterValue - 334182

theorem fullRecordGapTerm01530_eq_value :
    recordGapCenter - 334182 = fullRecordGapValue01530 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01530_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01530 (fullRecordGapValue01530 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01530_not_prime : ¬(recordGapCenter - 334182).Prime := by
  rw [fullRecordGapTerm01530_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01530, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01530_fast_pow_mod_ne_one

def fullRecordGapValue01531 : Nat := fullRecordGapCenterValue - 334102

theorem fullRecordGapTerm01531_eq_value :
    recordGapCenter - 334102 = fullRecordGapValue01531 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01531_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01531 (fullRecordGapValue01531 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01531_not_prime : ¬(recordGapCenter - 334102).Prime := by
  rw [fullRecordGapTerm01531_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01531, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01531_fast_pow_mod_ne_one

def fullRecordGapValue01532 : Nat := fullRecordGapCenterValue - 334078

theorem fullRecordGapTerm01532_eq_value :
    recordGapCenter - 334078 = fullRecordGapValue01532 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01532_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01532 (fullRecordGapValue01532 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01532_not_prime : ¬(recordGapCenter - 334078).Prime := by
  rw [fullRecordGapTerm01532_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01532, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01532_fast_pow_mod_ne_one

def fullRecordGapValue01533 : Nat := fullRecordGapCenterValue - 334018

theorem fullRecordGapTerm01533_eq_value :
    recordGapCenter - 334018 = fullRecordGapValue01533 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01533_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01533 (fullRecordGapValue01533 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01533_not_prime : ¬(recordGapCenter - 334018).Prime := by
  rw [fullRecordGapTerm01533_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01533, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01533_fast_pow_mod_ne_one

def fullRecordGapValue01534 : Nat := fullRecordGapCenterValue - 334002

theorem fullRecordGapTerm01534_eq_value :
    recordGapCenter - 334002 = fullRecordGapValue01534 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01534_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01534 (fullRecordGapValue01534 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01534_not_prime : ¬(recordGapCenter - 334002).Prime := by
  rw [fullRecordGapTerm01534_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01534, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01534_fast_pow_mod_ne_one

def fullRecordGapValue01535 : Nat := fullRecordGapCenterValue - 333798

theorem fullRecordGapTerm01535_eq_value :
    recordGapCenter - 333798 = fullRecordGapValue01535 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01535_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01535 (fullRecordGapValue01535 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01535_not_prime : ¬(recordGapCenter - 333798).Prime := by
  rw [fullRecordGapTerm01535_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01535, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01535_fast_pow_mod_ne_one

def fullRecordGapValue01536 : Nat := fullRecordGapCenterValue - 333742

theorem fullRecordGapTerm01536_eq_value :
    recordGapCenter - 333742 = fullRecordGapValue01536 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01536_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01536 (fullRecordGapValue01536 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01536_not_prime : ¬(recordGapCenter - 333742).Prime := by
  rw [fullRecordGapTerm01536_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01536, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01536_fast_pow_mod_ne_one

end PrimeFactorUnimodality
