import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue05377 : Nat := fullRecordGapCenterValue + 263786

theorem fullRecordGapTerm05377_eq_value :
    recordGapCenter + 263786 = fullRecordGapValue05377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05377 (fullRecordGapValue05377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05377_not_prime : ¬(recordGapCenter + 263786).Prime := by
  rw [fullRecordGapTerm05377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05377_fast_pow_mod_ne_one

def fullRecordGapValue05378 : Nat := fullRecordGapCenterValue + 263828

theorem fullRecordGapTerm05378_eq_value :
    recordGapCenter + 263828 = fullRecordGapValue05378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05378 (fullRecordGapValue05378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05378_not_prime : ¬(recordGapCenter + 263828).Prime := by
  rw [fullRecordGapTerm05378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05378_fast_pow_mod_ne_one

def fullRecordGapValue05379 : Nat := fullRecordGapCenterValue + 263972

theorem fullRecordGapTerm05379_eq_value :
    recordGapCenter + 263972 = fullRecordGapValue05379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05379 (fullRecordGapValue05379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05379_not_prime : ¬(recordGapCenter + 263972).Prime := by
  rw [fullRecordGapTerm05379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05379_fast_pow_mod_ne_one

def fullRecordGapValue05380 : Nat := fullRecordGapCenterValue + 264002

theorem fullRecordGapTerm05380_eq_value :
    recordGapCenter + 264002 = fullRecordGapValue05380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05380 (fullRecordGapValue05380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05380_not_prime : ¬(recordGapCenter + 264002).Prime := by
  rw [fullRecordGapTerm05380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05380_fast_pow_mod_ne_one

def fullRecordGapValue05381 : Nat := fullRecordGapCenterValue + 264218

theorem fullRecordGapTerm05381_eq_value :
    recordGapCenter + 264218 = fullRecordGapValue05381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05381 (fullRecordGapValue05381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05381_not_prime : ¬(recordGapCenter + 264218).Prime := by
  rw [fullRecordGapTerm05381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05381_fast_pow_mod_ne_one

def fullRecordGapValue05382 : Nat := fullRecordGapCenterValue + 264338

theorem fullRecordGapTerm05382_eq_value :
    recordGapCenter + 264338 = fullRecordGapValue05382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05382 (fullRecordGapValue05382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05382_not_prime : ¬(recordGapCenter + 264338).Prime := by
  rw [fullRecordGapTerm05382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05382_fast_pow_mod_ne_one

def fullRecordGapValue05383 : Nat := fullRecordGapCenterValue + 264482

theorem fullRecordGapTerm05383_eq_value :
    recordGapCenter + 264482 = fullRecordGapValue05383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05383 (fullRecordGapValue05383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05383_not_prime : ¬(recordGapCenter + 264482).Prime := by
  rw [fullRecordGapTerm05383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05383_fast_pow_mod_ne_one

def fullRecordGapValue05384 : Nat := fullRecordGapCenterValue + 264666

theorem fullRecordGapTerm05384_eq_value :
    recordGapCenter + 264666 = fullRecordGapValue05384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05384 (fullRecordGapValue05384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05384_not_prime : ¬(recordGapCenter + 264666).Prime := by
  rw [fullRecordGapTerm05384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05384_fast_pow_mod_ne_one

def fullRecordGapValue05385 : Nat := fullRecordGapCenterValue + 264692

theorem fullRecordGapTerm05385_eq_value :
    recordGapCenter + 264692 = fullRecordGapValue05385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05385 (fullRecordGapValue05385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05385_not_prime : ¬(recordGapCenter + 264692).Prime := by
  rw [fullRecordGapTerm05385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05385_fast_pow_mod_ne_one

def fullRecordGapValue05386 : Nat := fullRecordGapCenterValue + 264716

theorem fullRecordGapTerm05386_eq_value :
    recordGapCenter + 264716 = fullRecordGapValue05386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05386 (fullRecordGapValue05386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05386_not_prime : ¬(recordGapCenter + 264716).Prime := by
  rw [fullRecordGapTerm05386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05386_fast_pow_mod_ne_one

def fullRecordGapValue05387 : Nat := fullRecordGapCenterValue + 264738

theorem fullRecordGapTerm05387_eq_value :
    recordGapCenter + 264738 = fullRecordGapValue05387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05387 (fullRecordGapValue05387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05387_not_prime : ¬(recordGapCenter + 264738).Prime := by
  rw [fullRecordGapTerm05387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05387_fast_pow_mod_ne_one

def fullRecordGapValue05388 : Nat := fullRecordGapCenterValue + 264786

theorem fullRecordGapTerm05388_eq_value :
    recordGapCenter + 264786 = fullRecordGapValue05388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05388 (fullRecordGapValue05388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05388_not_prime : ¬(recordGapCenter + 264786).Prime := by
  rw [fullRecordGapTerm05388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05388_fast_pow_mod_ne_one

def fullRecordGapValue05389 : Nat := fullRecordGapCenterValue + 264806

theorem fullRecordGapTerm05389_eq_value :
    recordGapCenter + 264806 = fullRecordGapValue05389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05389 (fullRecordGapValue05389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05389_not_prime : ¬(recordGapCenter + 264806).Prime := by
  rw [fullRecordGapTerm05389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05389_fast_pow_mod_ne_one

def fullRecordGapValue05390 : Nat := fullRecordGapCenterValue + 264818

theorem fullRecordGapTerm05390_eq_value :
    recordGapCenter + 264818 = fullRecordGapValue05390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05390 (fullRecordGapValue05390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05390_not_prime : ¬(recordGapCenter + 264818).Prime := by
  rw [fullRecordGapTerm05390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05390_fast_pow_mod_ne_one

def fullRecordGapValue05391 : Nat := fullRecordGapCenterValue + 265022

theorem fullRecordGapTerm05391_eq_value :
    recordGapCenter + 265022 = fullRecordGapValue05391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05391 (fullRecordGapValue05391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05391_not_prime : ¬(recordGapCenter + 265022).Prime := by
  rw [fullRecordGapTerm05391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05391_fast_pow_mod_ne_one

def fullRecordGapValue05392 : Nat := fullRecordGapCenterValue + 265058

theorem fullRecordGapTerm05392_eq_value :
    recordGapCenter + 265058 = fullRecordGapValue05392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05392 (fullRecordGapValue05392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05392_not_prime : ¬(recordGapCenter + 265058).Prime := by
  rw [fullRecordGapTerm05392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05392_fast_pow_mod_ne_one

def fullRecordGapValue05393 : Nat := fullRecordGapCenterValue + 265178

theorem fullRecordGapTerm05393_eq_value :
    recordGapCenter + 265178 = fullRecordGapValue05393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05393 (fullRecordGapValue05393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05393_not_prime : ¬(recordGapCenter + 265178).Prime := by
  rw [fullRecordGapTerm05393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05393_fast_pow_mod_ne_one

def fullRecordGapValue05394 : Nat := fullRecordGapCenterValue + 265262

theorem fullRecordGapTerm05394_eq_value :
    recordGapCenter + 265262 = fullRecordGapValue05394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05394 (fullRecordGapValue05394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05394_not_prime : ¬(recordGapCenter + 265262).Prime := by
  rw [fullRecordGapTerm05394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05394_fast_pow_mod_ne_one

def fullRecordGapValue05395 : Nat := fullRecordGapCenterValue + 265326

theorem fullRecordGapTerm05395_eq_value :
    recordGapCenter + 265326 = fullRecordGapValue05395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05395 (fullRecordGapValue05395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05395_not_prime : ¬(recordGapCenter + 265326).Prime := by
  rw [fullRecordGapTerm05395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05395_fast_pow_mod_ne_one

def fullRecordGapValue05396 : Nat := fullRecordGapCenterValue + 265436

theorem fullRecordGapTerm05396_eq_value :
    recordGapCenter + 265436 = fullRecordGapValue05396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05396 (fullRecordGapValue05396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05396_not_prime : ¬(recordGapCenter + 265436).Prime := by
  rw [fullRecordGapTerm05396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05396_fast_pow_mod_ne_one

def fullRecordGapValue05397 : Nat := fullRecordGapCenterValue + 265508

theorem fullRecordGapTerm05397_eq_value :
    recordGapCenter + 265508 = fullRecordGapValue05397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05397 (fullRecordGapValue05397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05397_not_prime : ¬(recordGapCenter + 265508).Prime := by
  rw [fullRecordGapTerm05397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05397_fast_pow_mod_ne_one

def fullRecordGapValue05398 : Nat := fullRecordGapCenterValue + 265526

theorem fullRecordGapTerm05398_eq_value :
    recordGapCenter + 265526 = fullRecordGapValue05398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05398 (fullRecordGapValue05398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05398_not_prime : ¬(recordGapCenter + 265526).Prime := by
  rw [fullRecordGapTerm05398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05398_fast_pow_mod_ne_one

def fullRecordGapValue05399 : Nat := fullRecordGapCenterValue + 265686

theorem fullRecordGapTerm05399_eq_value :
    recordGapCenter + 265686 = fullRecordGapValue05399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05399 (fullRecordGapValue05399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05399_not_prime : ¬(recordGapCenter + 265686).Prime := by
  rw [fullRecordGapTerm05399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05399_fast_pow_mod_ne_one

def fullRecordGapValue05400 : Nat := fullRecordGapCenterValue + 266078

theorem fullRecordGapTerm05400_eq_value :
    recordGapCenter + 266078 = fullRecordGapValue05400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05400 (fullRecordGapValue05400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05400_not_prime : ¬(recordGapCenter + 266078).Prime := by
  rw [fullRecordGapTerm05400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05400_fast_pow_mod_ne_one

def fullRecordGapValue05401 : Nat := fullRecordGapCenterValue + 266106

theorem fullRecordGapTerm05401_eq_value :
    recordGapCenter + 266106 = fullRecordGapValue05401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05401 (fullRecordGapValue05401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05401_not_prime : ¬(recordGapCenter + 266106).Prime := by
  rw [fullRecordGapTerm05401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05401_fast_pow_mod_ne_one

def fullRecordGapValue05402 : Nat := fullRecordGapCenterValue + 266112

theorem fullRecordGapTerm05402_eq_value :
    recordGapCenter + 266112 = fullRecordGapValue05402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05402 (fullRecordGapValue05402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05402_not_prime : ¬(recordGapCenter + 266112).Prime := by
  rw [fullRecordGapTerm05402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05402_fast_pow_mod_ne_one

def fullRecordGapValue05403 : Nat := fullRecordGapCenterValue + 266138

theorem fullRecordGapTerm05403_eq_value :
    recordGapCenter + 266138 = fullRecordGapValue05403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05403 (fullRecordGapValue05403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05403_not_prime : ¬(recordGapCenter + 266138).Prime := by
  rw [fullRecordGapTerm05403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05403_fast_pow_mod_ne_one

def fullRecordGapValue05404 : Nat := fullRecordGapCenterValue + 266226

theorem fullRecordGapTerm05404_eq_value :
    recordGapCenter + 266226 = fullRecordGapValue05404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05404 (fullRecordGapValue05404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05404_not_prime : ¬(recordGapCenter + 266226).Prime := by
  rw [fullRecordGapTerm05404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05404_fast_pow_mod_ne_one

def fullRecordGapValue05405 : Nat := fullRecordGapCenterValue + 266298

theorem fullRecordGapTerm05405_eq_value :
    recordGapCenter + 266298 = fullRecordGapValue05405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05405 (fullRecordGapValue05405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05405_not_prime : ¬(recordGapCenter + 266298).Prime := by
  rw [fullRecordGapTerm05405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05405_fast_pow_mod_ne_one

def fullRecordGapValue05406 : Nat := fullRecordGapCenterValue + 266348

theorem fullRecordGapTerm05406_eq_value :
    recordGapCenter + 266348 = fullRecordGapValue05406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05406 (fullRecordGapValue05406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05406_not_prime : ¬(recordGapCenter + 266348).Prime := by
  rw [fullRecordGapTerm05406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05406_fast_pow_mod_ne_one

def fullRecordGapValue05407 : Nat := fullRecordGapCenterValue + 266642

theorem fullRecordGapTerm05407_eq_value :
    recordGapCenter + 266642 = fullRecordGapValue05407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05407 (fullRecordGapValue05407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05407_not_prime : ¬(recordGapCenter + 266642).Prime := by
  rw [fullRecordGapTerm05407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05407_fast_pow_mod_ne_one

def fullRecordGapValue05408 : Nat := fullRecordGapCenterValue + 266718

theorem fullRecordGapTerm05408_eq_value :
    recordGapCenter + 266718 = fullRecordGapValue05408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05408 (fullRecordGapValue05408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05408_not_prime : ¬(recordGapCenter + 266718).Prime := by
  rw [fullRecordGapTerm05408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05408_fast_pow_mod_ne_one

def fullRecordGapValue05409 : Nat := fullRecordGapCenterValue + 266852

theorem fullRecordGapTerm05409_eq_value :
    recordGapCenter + 266852 = fullRecordGapValue05409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05409 (fullRecordGapValue05409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05409_not_prime : ¬(recordGapCenter + 266852).Prime := by
  rw [fullRecordGapTerm05409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05409_fast_pow_mod_ne_one

def fullRecordGapValue05410 : Nat := fullRecordGapCenterValue + 266898

theorem fullRecordGapTerm05410_eq_value :
    recordGapCenter + 266898 = fullRecordGapValue05410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05410 (fullRecordGapValue05410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05410_not_prime : ¬(recordGapCenter + 266898).Prime := by
  rw [fullRecordGapTerm05410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05410_fast_pow_mod_ne_one

def fullRecordGapValue05411 : Nat := fullRecordGapCenterValue + 266946

theorem fullRecordGapTerm05411_eq_value :
    recordGapCenter + 266946 = fullRecordGapValue05411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05411 (fullRecordGapValue05411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05411_not_prime : ¬(recordGapCenter + 266946).Prime := by
  rw [fullRecordGapTerm05411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05411_fast_pow_mod_ne_one

def fullRecordGapValue05412 : Nat := fullRecordGapCenterValue + 266982

theorem fullRecordGapTerm05412_eq_value :
    recordGapCenter + 266982 = fullRecordGapValue05412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05412 (fullRecordGapValue05412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05412_not_prime : ¬(recordGapCenter + 266982).Prime := by
  rw [fullRecordGapTerm05412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05412_fast_pow_mod_ne_one

def fullRecordGapValue05413 : Nat := fullRecordGapCenterValue + 266996

theorem fullRecordGapTerm05413_eq_value :
    recordGapCenter + 266996 = fullRecordGapValue05413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05413 (fullRecordGapValue05413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05413_not_prime : ¬(recordGapCenter + 266996).Prime := by
  rw [fullRecordGapTerm05413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05413_fast_pow_mod_ne_one

def fullRecordGapValue05414 : Nat := fullRecordGapCenterValue + 267198

theorem fullRecordGapTerm05414_eq_value :
    recordGapCenter + 267198 = fullRecordGapValue05414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05414 (fullRecordGapValue05414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05414_not_prime : ¬(recordGapCenter + 267198).Prime := by
  rw [fullRecordGapTerm05414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05414_fast_pow_mod_ne_one

def fullRecordGapValue05415 : Nat := fullRecordGapCenterValue + 267222

theorem fullRecordGapTerm05415_eq_value :
    recordGapCenter + 267222 = fullRecordGapValue05415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05415 (fullRecordGapValue05415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05415_not_prime : ¬(recordGapCenter + 267222).Prime := by
  rw [fullRecordGapTerm05415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05415_fast_pow_mod_ne_one

def fullRecordGapValue05416 : Nat := fullRecordGapCenterValue + 267236

theorem fullRecordGapTerm05416_eq_value :
    recordGapCenter + 267236 = fullRecordGapValue05416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05416 (fullRecordGapValue05416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05416_not_prime : ¬(recordGapCenter + 267236).Prime := by
  rw [fullRecordGapTerm05416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05416_fast_pow_mod_ne_one

def fullRecordGapValue05417 : Nat := fullRecordGapCenterValue + 267258

theorem fullRecordGapTerm05417_eq_value :
    recordGapCenter + 267258 = fullRecordGapValue05417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05417 (fullRecordGapValue05417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05417_not_prime : ¬(recordGapCenter + 267258).Prime := by
  rw [fullRecordGapTerm05417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05417_fast_pow_mod_ne_one

def fullRecordGapValue05418 : Nat := fullRecordGapCenterValue + 267300

theorem fullRecordGapTerm05418_eq_value :
    recordGapCenter + 267300 = fullRecordGapValue05418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05418 (fullRecordGapValue05418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05418_not_prime : ¬(recordGapCenter + 267300).Prime := by
  rw [fullRecordGapTerm05418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05418_fast_pow_mod_ne_one

def fullRecordGapValue05419 : Nat := fullRecordGapCenterValue + 267446

theorem fullRecordGapTerm05419_eq_value :
    recordGapCenter + 267446 = fullRecordGapValue05419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05419 (fullRecordGapValue05419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05419_not_prime : ¬(recordGapCenter + 267446).Prime := by
  rw [fullRecordGapTerm05419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05419_fast_pow_mod_ne_one

def fullRecordGapValue05420 : Nat := fullRecordGapCenterValue + 267522

theorem fullRecordGapTerm05420_eq_value :
    recordGapCenter + 267522 = fullRecordGapValue05420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05420 (fullRecordGapValue05420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05420_not_prime : ¬(recordGapCenter + 267522).Prime := by
  rw [fullRecordGapTerm05420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05420_fast_pow_mod_ne_one

def fullRecordGapValue05421 : Nat := fullRecordGapCenterValue + 267702

theorem fullRecordGapTerm05421_eq_value :
    recordGapCenter + 267702 = fullRecordGapValue05421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05421 (fullRecordGapValue05421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05421_not_prime : ¬(recordGapCenter + 267702).Prime := by
  rw [fullRecordGapTerm05421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05421_fast_pow_mod_ne_one

def fullRecordGapValue05422 : Nat := fullRecordGapCenterValue + 267738

theorem fullRecordGapTerm05422_eq_value :
    recordGapCenter + 267738 = fullRecordGapValue05422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05422 (fullRecordGapValue05422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05422_not_prime : ¬(recordGapCenter + 267738).Prime := by
  rw [fullRecordGapTerm05422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05422_fast_pow_mod_ne_one

def fullRecordGapValue05423 : Nat := fullRecordGapCenterValue + 267788

theorem fullRecordGapTerm05423_eq_value :
    recordGapCenter + 267788 = fullRecordGapValue05423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05423 (fullRecordGapValue05423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05423_not_prime : ¬(recordGapCenter + 267788).Prime := by
  rw [fullRecordGapTerm05423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05423_fast_pow_mod_ne_one

def fullRecordGapValue05424 : Nat := fullRecordGapCenterValue + 267942

theorem fullRecordGapTerm05424_eq_value :
    recordGapCenter + 267942 = fullRecordGapValue05424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05424 (fullRecordGapValue05424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05424_not_prime : ¬(recordGapCenter + 267942).Prime := by
  rw [fullRecordGapTerm05424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05424_fast_pow_mod_ne_one

def fullRecordGapValue05425 : Nat := fullRecordGapCenterValue + 267986

theorem fullRecordGapTerm05425_eq_value :
    recordGapCenter + 267986 = fullRecordGapValue05425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05425 (fullRecordGapValue05425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05425_not_prime : ¬(recordGapCenter + 267986).Prime := by
  rw [fullRecordGapTerm05425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05425_fast_pow_mod_ne_one

def fullRecordGapValue05426 : Nat := fullRecordGapCenterValue + 268098

theorem fullRecordGapTerm05426_eq_value :
    recordGapCenter + 268098 = fullRecordGapValue05426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05426 (fullRecordGapValue05426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05426_not_prime : ¬(recordGapCenter + 268098).Prime := by
  rw [fullRecordGapTerm05426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05426_fast_pow_mod_ne_one

def fullRecordGapValue05427 : Nat := fullRecordGapCenterValue + 268118

theorem fullRecordGapTerm05427_eq_value :
    recordGapCenter + 268118 = fullRecordGapValue05427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05427 (fullRecordGapValue05427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05427_not_prime : ¬(recordGapCenter + 268118).Prime := by
  rw [fullRecordGapTerm05427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05427_fast_pow_mod_ne_one

def fullRecordGapValue05428 : Nat := fullRecordGapCenterValue + 268172

theorem fullRecordGapTerm05428_eq_value :
    recordGapCenter + 268172 = fullRecordGapValue05428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05428 (fullRecordGapValue05428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05428_not_prime : ¬(recordGapCenter + 268172).Prime := by
  rw [fullRecordGapTerm05428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05428_fast_pow_mod_ne_one

def fullRecordGapValue05429 : Nat := fullRecordGapCenterValue + 268196

theorem fullRecordGapTerm05429_eq_value :
    recordGapCenter + 268196 = fullRecordGapValue05429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05429 (fullRecordGapValue05429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05429_not_prime : ¬(recordGapCenter + 268196).Prime := by
  rw [fullRecordGapTerm05429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05429_fast_pow_mod_ne_one

def fullRecordGapValue05430 : Nat := fullRecordGapCenterValue + 268206

theorem fullRecordGapTerm05430_eq_value :
    recordGapCenter + 268206 = fullRecordGapValue05430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05430 (fullRecordGapValue05430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05430_not_prime : ¬(recordGapCenter + 268206).Prime := by
  rw [fullRecordGapTerm05430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05430_fast_pow_mod_ne_one

def fullRecordGapValue05431 : Nat := fullRecordGapCenterValue + 268538

theorem fullRecordGapTerm05431_eq_value :
    recordGapCenter + 268538 = fullRecordGapValue05431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05431 (fullRecordGapValue05431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05431_not_prime : ¬(recordGapCenter + 268538).Prime := by
  rw [fullRecordGapTerm05431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05431_fast_pow_mod_ne_one

def fullRecordGapValue05432 : Nat := fullRecordGapCenterValue + 268556

theorem fullRecordGapTerm05432_eq_value :
    recordGapCenter + 268556 = fullRecordGapValue05432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05432 (fullRecordGapValue05432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05432_not_prime : ¬(recordGapCenter + 268556).Prime := by
  rw [fullRecordGapTerm05432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05432_fast_pow_mod_ne_one

def fullRecordGapValue05433 : Nat := fullRecordGapCenterValue + 268662

theorem fullRecordGapTerm05433_eq_value :
    recordGapCenter + 268662 = fullRecordGapValue05433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05433 (fullRecordGapValue05433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05433_not_prime : ¬(recordGapCenter + 268662).Prime := by
  rw [fullRecordGapTerm05433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05433_fast_pow_mod_ne_one

def fullRecordGapValue05434 : Nat := fullRecordGapCenterValue + 268718

theorem fullRecordGapTerm05434_eq_value :
    recordGapCenter + 268718 = fullRecordGapValue05434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05434 (fullRecordGapValue05434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05434_not_prime : ¬(recordGapCenter + 268718).Prime := by
  rw [fullRecordGapTerm05434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05434_fast_pow_mod_ne_one

def fullRecordGapValue05435 : Nat := fullRecordGapCenterValue + 268802

theorem fullRecordGapTerm05435_eq_value :
    recordGapCenter + 268802 = fullRecordGapValue05435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05435 (fullRecordGapValue05435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05435_not_prime : ¬(recordGapCenter + 268802).Prime := by
  rw [fullRecordGapTerm05435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05435_fast_pow_mod_ne_one

def fullRecordGapValue05436 : Nat := fullRecordGapCenterValue + 268886

theorem fullRecordGapTerm05436_eq_value :
    recordGapCenter + 268886 = fullRecordGapValue05436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05436 (fullRecordGapValue05436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05436_not_prime : ¬(recordGapCenter + 268886).Prime := by
  rw [fullRecordGapTerm05436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05436_fast_pow_mod_ne_one

def fullRecordGapValue05437 : Nat := fullRecordGapCenterValue + 269006

theorem fullRecordGapTerm05437_eq_value :
    recordGapCenter + 269006 = fullRecordGapValue05437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05437 (fullRecordGapValue05437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05437_not_prime : ¬(recordGapCenter + 269006).Prime := by
  rw [fullRecordGapTerm05437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05437_fast_pow_mod_ne_one

def fullRecordGapValue05438 : Nat := fullRecordGapCenterValue + 269202

theorem fullRecordGapTerm05438_eq_value :
    recordGapCenter + 269202 = fullRecordGapValue05438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05438 (fullRecordGapValue05438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05438_not_prime : ¬(recordGapCenter + 269202).Prime := by
  rw [fullRecordGapTerm05438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05438_fast_pow_mod_ne_one

def fullRecordGapValue05439 : Nat := fullRecordGapCenterValue + 269322

theorem fullRecordGapTerm05439_eq_value :
    recordGapCenter + 269322 = fullRecordGapValue05439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05439 (fullRecordGapValue05439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05439_not_prime : ¬(recordGapCenter + 269322).Prime := by
  rw [fullRecordGapTerm05439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05439_fast_pow_mod_ne_one

def fullRecordGapValue05440 : Nat := fullRecordGapCenterValue + 269396

theorem fullRecordGapTerm05440_eq_value :
    recordGapCenter + 269396 = fullRecordGapValue05440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05440 (fullRecordGapValue05440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05440_not_prime : ¬(recordGapCenter + 269396).Prime := by
  rw [fullRecordGapTerm05440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05440_fast_pow_mod_ne_one

def fullRecordGapValue05441 : Nat := fullRecordGapCenterValue + 269502

theorem fullRecordGapTerm05441_eq_value :
    recordGapCenter + 269502 = fullRecordGapValue05441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05441 (fullRecordGapValue05441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05441_not_prime : ¬(recordGapCenter + 269502).Prime := by
  rw [fullRecordGapTerm05441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05441_fast_pow_mod_ne_one

def fullRecordGapValue05442 : Nat := fullRecordGapCenterValue + 269708

theorem fullRecordGapTerm05442_eq_value :
    recordGapCenter + 269708 = fullRecordGapValue05442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05442 (fullRecordGapValue05442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05442_not_prime : ¬(recordGapCenter + 269708).Prime := by
  rw [fullRecordGapTerm05442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05442_fast_pow_mod_ne_one

def fullRecordGapValue05443 : Nat := fullRecordGapCenterValue + 269732

theorem fullRecordGapTerm05443_eq_value :
    recordGapCenter + 269732 = fullRecordGapValue05443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05443 (fullRecordGapValue05443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05443_not_prime : ¬(recordGapCenter + 269732).Prime := by
  rw [fullRecordGapTerm05443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05443_fast_pow_mod_ne_one

def fullRecordGapValue05444 : Nat := fullRecordGapCenterValue + 269778

theorem fullRecordGapTerm05444_eq_value :
    recordGapCenter + 269778 = fullRecordGapValue05444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05444 (fullRecordGapValue05444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05444_not_prime : ¬(recordGapCenter + 269778).Prime := by
  rw [fullRecordGapTerm05444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05444_fast_pow_mod_ne_one

def fullRecordGapValue05445 : Nat := fullRecordGapCenterValue + 269846

theorem fullRecordGapTerm05445_eq_value :
    recordGapCenter + 269846 = fullRecordGapValue05445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05445 (fullRecordGapValue05445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05445_not_prime : ¬(recordGapCenter + 269846).Prime := by
  rw [fullRecordGapTerm05445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05445_fast_pow_mod_ne_one

def fullRecordGapValue05446 : Nat := fullRecordGapCenterValue + 269922

theorem fullRecordGapTerm05446_eq_value :
    recordGapCenter + 269922 = fullRecordGapValue05446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05446 (fullRecordGapValue05446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05446_not_prime : ¬(recordGapCenter + 269922).Prime := by
  rw [fullRecordGapTerm05446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05446_fast_pow_mod_ne_one

def fullRecordGapValue05447 : Nat := fullRecordGapCenterValue + 269978

theorem fullRecordGapTerm05447_eq_value :
    recordGapCenter + 269978 = fullRecordGapValue05447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05447 (fullRecordGapValue05447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05447_not_prime : ¬(recordGapCenter + 269978).Prime := by
  rw [fullRecordGapTerm05447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05447_fast_pow_mod_ne_one

def fullRecordGapValue05448 : Nat := fullRecordGapCenterValue + 270042

theorem fullRecordGapTerm05448_eq_value :
    recordGapCenter + 270042 = fullRecordGapValue05448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05448 (fullRecordGapValue05448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05448_not_prime : ¬(recordGapCenter + 270042).Prime := by
  rw [fullRecordGapTerm05448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05448_fast_pow_mod_ne_one

def fullRecordGapValue05449 : Nat := fullRecordGapCenterValue + 270078

theorem fullRecordGapTerm05449_eq_value :
    recordGapCenter + 270078 = fullRecordGapValue05449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05449 (fullRecordGapValue05449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05449_not_prime : ¬(recordGapCenter + 270078).Prime := by
  rw [fullRecordGapTerm05449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05449_fast_pow_mod_ne_one

def fullRecordGapValue05450 : Nat := fullRecordGapCenterValue + 270086

theorem fullRecordGapTerm05450_eq_value :
    recordGapCenter + 270086 = fullRecordGapValue05450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05450 (fullRecordGapValue05450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05450_not_prime : ¬(recordGapCenter + 270086).Prime := by
  rw [fullRecordGapTerm05450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05450_fast_pow_mod_ne_one

def fullRecordGapValue05451 : Nat := fullRecordGapCenterValue + 270092

theorem fullRecordGapTerm05451_eq_value :
    recordGapCenter + 270092 = fullRecordGapValue05451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05451 (fullRecordGapValue05451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05451_not_prime : ¬(recordGapCenter + 270092).Prime := by
  rw [fullRecordGapTerm05451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05451_fast_pow_mod_ne_one

def fullRecordGapValue05452 : Nat := fullRecordGapCenterValue + 270302

theorem fullRecordGapTerm05452_eq_value :
    recordGapCenter + 270302 = fullRecordGapValue05452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05452 (fullRecordGapValue05452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05452_not_prime : ¬(recordGapCenter + 270302).Prime := by
  rw [fullRecordGapTerm05452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05452_fast_pow_mod_ne_one

def fullRecordGapValue05453 : Nat := fullRecordGapCenterValue + 270308

theorem fullRecordGapTerm05453_eq_value :
    recordGapCenter + 270308 = fullRecordGapValue05453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05453 (fullRecordGapValue05453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05453_not_prime : ¬(recordGapCenter + 270308).Prime := by
  rw [fullRecordGapTerm05453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05453_fast_pow_mod_ne_one

def fullRecordGapValue05454 : Nat := fullRecordGapCenterValue + 270356

theorem fullRecordGapTerm05454_eq_value :
    recordGapCenter + 270356 = fullRecordGapValue05454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05454 (fullRecordGapValue05454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05454_not_prime : ¬(recordGapCenter + 270356).Prime := by
  rw [fullRecordGapTerm05454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05454_fast_pow_mod_ne_one

def fullRecordGapValue05455 : Nat := fullRecordGapCenterValue + 270462

theorem fullRecordGapTerm05455_eq_value :
    recordGapCenter + 270462 = fullRecordGapValue05455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05455 (fullRecordGapValue05455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05455_not_prime : ¬(recordGapCenter + 270462).Prime := by
  rw [fullRecordGapTerm05455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05455_fast_pow_mod_ne_one

def fullRecordGapValue05456 : Nat := fullRecordGapCenterValue + 270498

theorem fullRecordGapTerm05456_eq_value :
    recordGapCenter + 270498 = fullRecordGapValue05456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05456 (fullRecordGapValue05456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05456_not_prime : ¬(recordGapCenter + 270498).Prime := by
  rw [fullRecordGapTerm05456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05456_fast_pow_mod_ne_one

def fullRecordGapValue05457 : Nat := fullRecordGapCenterValue + 270638

theorem fullRecordGapTerm05457_eq_value :
    recordGapCenter + 270638 = fullRecordGapValue05457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05457 (fullRecordGapValue05457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05457_not_prime : ¬(recordGapCenter + 270638).Prime := by
  rw [fullRecordGapTerm05457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05457_fast_pow_mod_ne_one

def fullRecordGapValue05458 : Nat := fullRecordGapCenterValue + 270698

theorem fullRecordGapTerm05458_eq_value :
    recordGapCenter + 270698 = fullRecordGapValue05458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05458 (fullRecordGapValue05458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05458_not_prime : ¬(recordGapCenter + 270698).Prime := by
  rw [fullRecordGapTerm05458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05458_fast_pow_mod_ne_one

def fullRecordGapValue05459 : Nat := fullRecordGapCenterValue + 270726

theorem fullRecordGapTerm05459_eq_value :
    recordGapCenter + 270726 = fullRecordGapValue05459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05459 (fullRecordGapValue05459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05459_not_prime : ¬(recordGapCenter + 270726).Prime := by
  rw [fullRecordGapTerm05459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05459_fast_pow_mod_ne_one

def fullRecordGapValue05460 : Nat := fullRecordGapCenterValue + 270786

theorem fullRecordGapTerm05460_eq_value :
    recordGapCenter + 270786 = fullRecordGapValue05460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05460 (fullRecordGapValue05460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05460_not_prime : ¬(recordGapCenter + 270786).Prime := by
  rw [fullRecordGapTerm05460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05460_fast_pow_mod_ne_one

def fullRecordGapValue05461 : Nat := fullRecordGapCenterValue + 270966

theorem fullRecordGapTerm05461_eq_value :
    recordGapCenter + 270966 = fullRecordGapValue05461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05461 (fullRecordGapValue05461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05461_not_prime : ¬(recordGapCenter + 270966).Prime := by
  rw [fullRecordGapTerm05461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05461_fast_pow_mod_ne_one

def fullRecordGapValue05462 : Nat := fullRecordGapCenterValue + 271022

theorem fullRecordGapTerm05462_eq_value :
    recordGapCenter + 271022 = fullRecordGapValue05462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05462 (fullRecordGapValue05462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05462_not_prime : ¬(recordGapCenter + 271022).Prime := by
  rw [fullRecordGapTerm05462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05462_fast_pow_mod_ne_one

def fullRecordGapValue05463 : Nat := fullRecordGapCenterValue + 271028

theorem fullRecordGapTerm05463_eq_value :
    recordGapCenter + 271028 = fullRecordGapValue05463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05463 (fullRecordGapValue05463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05463_not_prime : ¬(recordGapCenter + 271028).Prime := by
  rw [fullRecordGapTerm05463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05463_fast_pow_mod_ne_one

def fullRecordGapValue05464 : Nat := fullRecordGapCenterValue + 271040

theorem fullRecordGapTerm05464_eq_value :
    recordGapCenter + 271040 = fullRecordGapValue05464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05464 (fullRecordGapValue05464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05464_not_prime : ¬(recordGapCenter + 271040).Prime := by
  rw [fullRecordGapTerm05464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05464_fast_pow_mod_ne_one

def fullRecordGapValue05465 : Nat := fullRecordGapCenterValue + 271086

theorem fullRecordGapTerm05465_eq_value :
    recordGapCenter + 271086 = fullRecordGapValue05465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05465 (fullRecordGapValue05465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05465_not_prime : ¬(recordGapCenter + 271086).Prime := by
  rw [fullRecordGapTerm05465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05465_fast_pow_mod_ne_one

def fullRecordGapValue05466 : Nat := fullRecordGapCenterValue + 271118

theorem fullRecordGapTerm05466_eq_value :
    recordGapCenter + 271118 = fullRecordGapValue05466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05466 (fullRecordGapValue05466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05466_not_prime : ¬(recordGapCenter + 271118).Prime := by
  rw [fullRecordGapTerm05466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05466_fast_pow_mod_ne_one

def fullRecordGapValue05467 : Nat := fullRecordGapCenterValue + 271182

theorem fullRecordGapTerm05467_eq_value :
    recordGapCenter + 271182 = fullRecordGapValue05467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05467 (fullRecordGapValue05467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05467_not_prime : ¬(recordGapCenter + 271182).Prime := by
  rw [fullRecordGapTerm05467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05467_fast_pow_mod_ne_one

def fullRecordGapValue05468 : Nat := fullRecordGapCenterValue + 271202

theorem fullRecordGapTerm05468_eq_value :
    recordGapCenter + 271202 = fullRecordGapValue05468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05468 (fullRecordGapValue05468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05468_not_prime : ¬(recordGapCenter + 271202).Prime := by
  rw [fullRecordGapTerm05468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05468_fast_pow_mod_ne_one

def fullRecordGapValue05469 : Nat := fullRecordGapCenterValue + 271226

theorem fullRecordGapTerm05469_eq_value :
    recordGapCenter + 271226 = fullRecordGapValue05469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05469 (fullRecordGapValue05469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05469_not_prime : ¬(recordGapCenter + 271226).Prime := by
  rw [fullRecordGapTerm05469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05469_fast_pow_mod_ne_one

def fullRecordGapValue05470 : Nat := fullRecordGapCenterValue + 271482

theorem fullRecordGapTerm05470_eq_value :
    recordGapCenter + 271482 = fullRecordGapValue05470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05470 (fullRecordGapValue05470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05470_not_prime : ¬(recordGapCenter + 271482).Prime := by
  rw [fullRecordGapTerm05470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05470_fast_pow_mod_ne_one

def fullRecordGapValue05471 : Nat := fullRecordGapCenterValue + 271598

theorem fullRecordGapTerm05471_eq_value :
    recordGapCenter + 271598 = fullRecordGapValue05471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05471 (fullRecordGapValue05471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05471_not_prime : ¬(recordGapCenter + 271598).Prime := by
  rw [fullRecordGapTerm05471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05471_fast_pow_mod_ne_one

def fullRecordGapValue05472 : Nat := fullRecordGapCenterValue + 271656

theorem fullRecordGapTerm05472_eq_value :
    recordGapCenter + 271656 = fullRecordGapValue05472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05472 (fullRecordGapValue05472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05472_not_prime : ¬(recordGapCenter + 271656).Prime := by
  rw [fullRecordGapTerm05472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05472_fast_pow_mod_ne_one

def fullRecordGapValue05473 : Nat := fullRecordGapCenterValue + 271658

theorem fullRecordGapTerm05473_eq_value :
    recordGapCenter + 271658 = fullRecordGapValue05473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05473 (fullRecordGapValue05473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05473_not_prime : ¬(recordGapCenter + 271658).Prime := by
  rw [fullRecordGapTerm05473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05473_fast_pow_mod_ne_one

def fullRecordGapValue05474 : Nat := fullRecordGapCenterValue + 271826

theorem fullRecordGapTerm05474_eq_value :
    recordGapCenter + 271826 = fullRecordGapValue05474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05474 (fullRecordGapValue05474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05474_not_prime : ¬(recordGapCenter + 271826).Prime := by
  rw [fullRecordGapTerm05474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05474_fast_pow_mod_ne_one

def fullRecordGapValue05475 : Nat := fullRecordGapCenterValue + 272022

theorem fullRecordGapTerm05475_eq_value :
    recordGapCenter + 272022 = fullRecordGapValue05475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05475 (fullRecordGapValue05475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05475_not_prime : ¬(recordGapCenter + 272022).Prime := by
  rw [fullRecordGapTerm05475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05475_fast_pow_mod_ne_one

def fullRecordGapValue05476 : Nat := fullRecordGapCenterValue + 272046

theorem fullRecordGapTerm05476_eq_value :
    recordGapCenter + 272046 = fullRecordGapValue05476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05476 (fullRecordGapValue05476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05476_not_prime : ¬(recordGapCenter + 272046).Prime := by
  rw [fullRecordGapTerm05476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05476_fast_pow_mod_ne_one

def fullRecordGapValue05477 : Nat := fullRecordGapCenterValue + 272058

theorem fullRecordGapTerm05477_eq_value :
    recordGapCenter + 272058 = fullRecordGapValue05477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05477 (fullRecordGapValue05477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05477_not_prime : ¬(recordGapCenter + 272058).Prime := by
  rw [fullRecordGapTerm05477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05477_fast_pow_mod_ne_one

def fullRecordGapValue05478 : Nat := fullRecordGapCenterValue + 272160

theorem fullRecordGapTerm05478_eq_value :
    recordGapCenter + 272160 = fullRecordGapValue05478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05478 (fullRecordGapValue05478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05478_not_prime : ¬(recordGapCenter + 272160).Prime := by
  rw [fullRecordGapTerm05478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05478_fast_pow_mod_ne_one

def fullRecordGapValue05479 : Nat := fullRecordGapCenterValue + 272198

theorem fullRecordGapTerm05479_eq_value :
    recordGapCenter + 272198 = fullRecordGapValue05479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05479 (fullRecordGapValue05479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05479_not_prime : ¬(recordGapCenter + 272198).Prime := by
  rw [fullRecordGapTerm05479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05479_fast_pow_mod_ne_one

def fullRecordGapValue05480 : Nat := fullRecordGapCenterValue + 272478

theorem fullRecordGapTerm05480_eq_value :
    recordGapCenter + 272478 = fullRecordGapValue05480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05480 (fullRecordGapValue05480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05480_not_prime : ¬(recordGapCenter + 272478).Prime := by
  rw [fullRecordGapTerm05480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05480_fast_pow_mod_ne_one

def fullRecordGapValue05481 : Nat := fullRecordGapCenterValue + 272522

theorem fullRecordGapTerm05481_eq_value :
    recordGapCenter + 272522 = fullRecordGapValue05481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05481 (fullRecordGapValue05481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05481_not_prime : ¬(recordGapCenter + 272522).Prime := by
  rw [fullRecordGapTerm05481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05481_fast_pow_mod_ne_one

def fullRecordGapValue05482 : Nat := fullRecordGapCenterValue + 272562

theorem fullRecordGapTerm05482_eq_value :
    recordGapCenter + 272562 = fullRecordGapValue05482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05482 (fullRecordGapValue05482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05482_not_prime : ¬(recordGapCenter + 272562).Prime := by
  rw [fullRecordGapTerm05482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05482_fast_pow_mod_ne_one

def fullRecordGapValue05483 : Nat := fullRecordGapCenterValue + 272858

theorem fullRecordGapTerm05483_eq_value :
    recordGapCenter + 272858 = fullRecordGapValue05483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05483 (fullRecordGapValue05483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05483_not_prime : ¬(recordGapCenter + 272858).Prime := by
  rw [fullRecordGapTerm05483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05483_fast_pow_mod_ne_one

def fullRecordGapValue05484 : Nat := fullRecordGapCenterValue + 272946

theorem fullRecordGapTerm05484_eq_value :
    recordGapCenter + 272946 = fullRecordGapValue05484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05484 (fullRecordGapValue05484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05484_not_prime : ¬(recordGapCenter + 272946).Prime := by
  rw [fullRecordGapTerm05484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05484_fast_pow_mod_ne_one

def fullRecordGapValue05485 : Nat := fullRecordGapCenterValue + 272982

theorem fullRecordGapTerm05485_eq_value :
    recordGapCenter + 272982 = fullRecordGapValue05485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05485 (fullRecordGapValue05485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05485_not_prime : ¬(recordGapCenter + 272982).Prime := by
  rw [fullRecordGapTerm05485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05485_fast_pow_mod_ne_one

def fullRecordGapValue05486 : Nat := fullRecordGapCenterValue + 273002

theorem fullRecordGapTerm05486_eq_value :
    recordGapCenter + 273002 = fullRecordGapValue05486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05486 (fullRecordGapValue05486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05486_not_prime : ¬(recordGapCenter + 273002).Prime := by
  rw [fullRecordGapTerm05486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05486_fast_pow_mod_ne_one

def fullRecordGapValue05487 : Nat := fullRecordGapCenterValue + 273116

theorem fullRecordGapTerm05487_eq_value :
    recordGapCenter + 273116 = fullRecordGapValue05487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05487 (fullRecordGapValue05487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05487_not_prime : ¬(recordGapCenter + 273116).Prime := by
  rw [fullRecordGapTerm05487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05487_fast_pow_mod_ne_one

def fullRecordGapValue05488 : Nat := fullRecordGapCenterValue + 273198

theorem fullRecordGapTerm05488_eq_value :
    recordGapCenter + 273198 = fullRecordGapValue05488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05488 (fullRecordGapValue05488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05488_not_prime : ¬(recordGapCenter + 273198).Prime := by
  rw [fullRecordGapTerm05488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05488_fast_pow_mod_ne_one

def fullRecordGapValue05489 : Nat := fullRecordGapCenterValue + 273386

theorem fullRecordGapTerm05489_eq_value :
    recordGapCenter + 273386 = fullRecordGapValue05489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05489 (fullRecordGapValue05489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05489_not_prime : ¬(recordGapCenter + 273386).Prime := by
  rw [fullRecordGapTerm05489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05489_fast_pow_mod_ne_one

def fullRecordGapValue05490 : Nat := fullRecordGapCenterValue + 273506

theorem fullRecordGapTerm05490_eq_value :
    recordGapCenter + 273506 = fullRecordGapValue05490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05490 (fullRecordGapValue05490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05490_not_prime : ¬(recordGapCenter + 273506).Prime := by
  rw [fullRecordGapTerm05490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05490_fast_pow_mod_ne_one

def fullRecordGapValue05491 : Nat := fullRecordGapCenterValue + 273626

theorem fullRecordGapTerm05491_eq_value :
    recordGapCenter + 273626 = fullRecordGapValue05491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05491 (fullRecordGapValue05491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05491_not_prime : ¬(recordGapCenter + 273626).Prime := by
  rw [fullRecordGapTerm05491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05491_fast_pow_mod_ne_one

def fullRecordGapValue05492 : Nat := fullRecordGapCenterValue + 273758

theorem fullRecordGapTerm05492_eq_value :
    recordGapCenter + 273758 = fullRecordGapValue05492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05492 (fullRecordGapValue05492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05492_not_prime : ¬(recordGapCenter + 273758).Prime := by
  rw [fullRecordGapTerm05492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05492_fast_pow_mod_ne_one

def fullRecordGapValue05493 : Nat := fullRecordGapCenterValue + 273998

theorem fullRecordGapTerm05493_eq_value :
    recordGapCenter + 273998 = fullRecordGapValue05493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05493 (fullRecordGapValue05493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05493_not_prime : ¬(recordGapCenter + 273998).Prime := by
  rw [fullRecordGapTerm05493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05493_fast_pow_mod_ne_one

def fullRecordGapValue05494 : Nat := fullRecordGapCenterValue + 274002

theorem fullRecordGapTerm05494_eq_value :
    recordGapCenter + 274002 = fullRecordGapValue05494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05494 (fullRecordGapValue05494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05494_not_prime : ¬(recordGapCenter + 274002).Prime := by
  rw [fullRecordGapTerm05494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05494_fast_pow_mod_ne_one

def fullRecordGapValue05495 : Nat := fullRecordGapCenterValue + 274062

theorem fullRecordGapTerm05495_eq_value :
    recordGapCenter + 274062 = fullRecordGapValue05495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05495 (fullRecordGapValue05495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05495_not_prime : ¬(recordGapCenter + 274062).Prime := by
  rw [fullRecordGapTerm05495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05495_fast_pow_mod_ne_one

def fullRecordGapValue05496 : Nat := fullRecordGapCenterValue + 274382

theorem fullRecordGapTerm05496_eq_value :
    recordGapCenter + 274382 = fullRecordGapValue05496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05496 (fullRecordGapValue05496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05496_not_prime : ¬(recordGapCenter + 274382).Prime := by
  rw [fullRecordGapTerm05496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05496_fast_pow_mod_ne_one

def fullRecordGapValue05497 : Nat := fullRecordGapCenterValue + 274478

theorem fullRecordGapTerm05497_eq_value :
    recordGapCenter + 274478 = fullRecordGapValue05497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05497 (fullRecordGapValue05497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05497_not_prime : ¬(recordGapCenter + 274478).Prime := by
  rw [fullRecordGapTerm05497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05497_fast_pow_mod_ne_one

def fullRecordGapValue05498 : Nat := fullRecordGapCenterValue + 274502

theorem fullRecordGapTerm05498_eq_value :
    recordGapCenter + 274502 = fullRecordGapValue05498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05498 (fullRecordGapValue05498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05498_not_prime : ¬(recordGapCenter + 274502).Prime := by
  rw [fullRecordGapTerm05498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05498_fast_pow_mod_ne_one

def fullRecordGapValue05499 : Nat := fullRecordGapCenterValue + 274676

theorem fullRecordGapTerm05499_eq_value :
    recordGapCenter + 274676 = fullRecordGapValue05499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05499 (fullRecordGapValue05499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05499_not_prime : ¬(recordGapCenter + 274676).Prime := by
  rw [fullRecordGapTerm05499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05499_fast_pow_mod_ne_one

def fullRecordGapValue05500 : Nat := fullRecordGapCenterValue + 274682

theorem fullRecordGapTerm05500_eq_value :
    recordGapCenter + 274682 = fullRecordGapValue05500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05500 (fullRecordGapValue05500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05500_not_prime : ¬(recordGapCenter + 274682).Prime := by
  rw [fullRecordGapTerm05500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05500_fast_pow_mod_ne_one

def fullRecordGapValue05501 : Nat := fullRecordGapCenterValue + 274718

theorem fullRecordGapTerm05501_eq_value :
    recordGapCenter + 274718 = fullRecordGapValue05501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05501 (fullRecordGapValue05501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05501_not_prime : ¬(recordGapCenter + 274718).Prime := by
  rw [fullRecordGapTerm05501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05501_fast_pow_mod_ne_one

def fullRecordGapValue05502 : Nat := fullRecordGapCenterValue + 274766

theorem fullRecordGapTerm05502_eq_value :
    recordGapCenter + 274766 = fullRecordGapValue05502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05502 (fullRecordGapValue05502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05502_not_prime : ¬(recordGapCenter + 274766).Prime := by
  rw [fullRecordGapTerm05502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05502_fast_pow_mod_ne_one

def fullRecordGapValue05503 : Nat := fullRecordGapCenterValue + 274796

theorem fullRecordGapTerm05503_eq_value :
    recordGapCenter + 274796 = fullRecordGapValue05503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05503 (fullRecordGapValue05503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05503_not_prime : ¬(recordGapCenter + 274796).Prime := by
  rw [fullRecordGapTerm05503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05503_fast_pow_mod_ne_one

def fullRecordGapValue05504 : Nat := fullRecordGapCenterValue + 274916

theorem fullRecordGapTerm05504_eq_value :
    recordGapCenter + 274916 = fullRecordGapValue05504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05504 (fullRecordGapValue05504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05504_not_prime : ¬(recordGapCenter + 274916).Prime := by
  rw [fullRecordGapTerm05504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05504_fast_pow_mod_ne_one

def fullRecordGapValue05505 : Nat := fullRecordGapCenterValue + 274982

theorem fullRecordGapTerm05505_eq_value :
    recordGapCenter + 274982 = fullRecordGapValue05505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05505 (fullRecordGapValue05505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05505_not_prime : ¬(recordGapCenter + 274982).Prime := by
  rw [fullRecordGapTerm05505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05505_fast_pow_mod_ne_one

def fullRecordGapValue05506 : Nat := fullRecordGapCenterValue + 275108

theorem fullRecordGapTerm05506_eq_value :
    recordGapCenter + 275108 = fullRecordGapValue05506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05506 (fullRecordGapValue05506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05506_not_prime : ¬(recordGapCenter + 275108).Prime := by
  rw [fullRecordGapTerm05506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05506_fast_pow_mod_ne_one

def fullRecordGapValue05507 : Nat := fullRecordGapCenterValue + 275186

theorem fullRecordGapTerm05507_eq_value :
    recordGapCenter + 275186 = fullRecordGapValue05507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05507 (fullRecordGapValue05507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05507_not_prime : ¬(recordGapCenter + 275186).Prime := by
  rw [fullRecordGapTerm05507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05507_fast_pow_mod_ne_one

def fullRecordGapValue05508 : Nat := fullRecordGapCenterValue + 275318

theorem fullRecordGapTerm05508_eq_value :
    recordGapCenter + 275318 = fullRecordGapValue05508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05508 (fullRecordGapValue05508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05508_not_prime : ¬(recordGapCenter + 275318).Prime := by
  rw [fullRecordGapTerm05508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05508_fast_pow_mod_ne_one

def fullRecordGapValue05509 : Nat := fullRecordGapCenterValue + 275426

theorem fullRecordGapTerm05509_eq_value :
    recordGapCenter + 275426 = fullRecordGapValue05509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05509 (fullRecordGapValue05509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05509_not_prime : ¬(recordGapCenter + 275426).Prime := by
  rw [fullRecordGapTerm05509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05509_fast_pow_mod_ne_one

def fullRecordGapValue05510 : Nat := fullRecordGapCenterValue + 275516

theorem fullRecordGapTerm05510_eq_value :
    recordGapCenter + 275516 = fullRecordGapValue05510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05510 (fullRecordGapValue05510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05510_not_prime : ¬(recordGapCenter + 275516).Prime := by
  rw [fullRecordGapTerm05510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05510_fast_pow_mod_ne_one

def fullRecordGapValue05511 : Nat := fullRecordGapCenterValue + 275562

theorem fullRecordGapTerm05511_eq_value :
    recordGapCenter + 275562 = fullRecordGapValue05511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05511 (fullRecordGapValue05511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05511_not_prime : ¬(recordGapCenter + 275562).Prime := by
  rw [fullRecordGapTerm05511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05511_fast_pow_mod_ne_one

def fullRecordGapValue05512 : Nat := fullRecordGapCenterValue + 275588

theorem fullRecordGapTerm05512_eq_value :
    recordGapCenter + 275588 = fullRecordGapValue05512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05512 (fullRecordGapValue05512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05512_not_prime : ¬(recordGapCenter + 275588).Prime := by
  rw [fullRecordGapTerm05512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05512_fast_pow_mod_ne_one

def fullRecordGapValue05513 : Nat := fullRecordGapCenterValue + 275636

theorem fullRecordGapTerm05513_eq_value :
    recordGapCenter + 275636 = fullRecordGapValue05513 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05513_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05513 (fullRecordGapValue05513 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05513_not_prime : ¬(recordGapCenter + 275636).Prime := by
  rw [fullRecordGapTerm05513_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05513, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05513_fast_pow_mod_ne_one

def fullRecordGapValue05514 : Nat := fullRecordGapCenterValue + 275658

theorem fullRecordGapTerm05514_eq_value :
    recordGapCenter + 275658 = fullRecordGapValue05514 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05514_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05514 (fullRecordGapValue05514 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05514_not_prime : ¬(recordGapCenter + 275658).Prime := by
  rw [fullRecordGapTerm05514_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05514, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05514_fast_pow_mod_ne_one

def fullRecordGapValue05515 : Nat := fullRecordGapCenterValue + 275718

theorem fullRecordGapTerm05515_eq_value :
    recordGapCenter + 275718 = fullRecordGapValue05515 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05515_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05515 (fullRecordGapValue05515 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05515_not_prime : ¬(recordGapCenter + 275718).Prime := by
  rw [fullRecordGapTerm05515_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05515, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05515_fast_pow_mod_ne_one

def fullRecordGapValue05516 : Nat := fullRecordGapCenterValue + 275738

theorem fullRecordGapTerm05516_eq_value :
    recordGapCenter + 275738 = fullRecordGapValue05516 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05516_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05516 (fullRecordGapValue05516 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05516_not_prime : ¬(recordGapCenter + 275738).Prime := by
  rw [fullRecordGapTerm05516_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05516, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05516_fast_pow_mod_ne_one

def fullRecordGapValue05517 : Nat := fullRecordGapCenterValue + 275822

theorem fullRecordGapTerm05517_eq_value :
    recordGapCenter + 275822 = fullRecordGapValue05517 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05517_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05517 (fullRecordGapValue05517 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05517_not_prime : ¬(recordGapCenter + 275822).Prime := by
  rw [fullRecordGapTerm05517_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05517, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05517_fast_pow_mod_ne_one

def fullRecordGapValue05518 : Nat := fullRecordGapCenterValue + 275852

theorem fullRecordGapTerm05518_eq_value :
    recordGapCenter + 275852 = fullRecordGapValue05518 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05518_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05518 (fullRecordGapValue05518 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05518_not_prime : ¬(recordGapCenter + 275852).Prime := by
  rw [fullRecordGapTerm05518_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05518, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05518_fast_pow_mod_ne_one

def fullRecordGapValue05519 : Nat := fullRecordGapCenterValue + 275882

theorem fullRecordGapTerm05519_eq_value :
    recordGapCenter + 275882 = fullRecordGapValue05519 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05519_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05519 (fullRecordGapValue05519 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05519_not_prime : ¬(recordGapCenter + 275882).Prime := by
  rw [fullRecordGapTerm05519_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05519, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05519_fast_pow_mod_ne_one

def fullRecordGapValue05520 : Nat := fullRecordGapCenterValue + 275966

theorem fullRecordGapTerm05520_eq_value :
    recordGapCenter + 275966 = fullRecordGapValue05520 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05520_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05520 (fullRecordGapValue05520 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05520_not_prime : ¬(recordGapCenter + 275966).Prime := by
  rw [fullRecordGapTerm05520_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05520, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05520_fast_pow_mod_ne_one

def fullRecordGapValue05521 : Nat := fullRecordGapCenterValue + 276126

theorem fullRecordGapTerm05521_eq_value :
    recordGapCenter + 276126 = fullRecordGapValue05521 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05521_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05521 (fullRecordGapValue05521 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05521_not_prime : ¬(recordGapCenter + 276126).Prime := by
  rw [fullRecordGapTerm05521_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05521, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05521_fast_pow_mod_ne_one

def fullRecordGapValue05522 : Nat := fullRecordGapCenterValue + 276158

theorem fullRecordGapTerm05522_eq_value :
    recordGapCenter + 276158 = fullRecordGapValue05522 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05522_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05522 (fullRecordGapValue05522 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05522_not_prime : ¬(recordGapCenter + 276158).Prime := by
  rw [fullRecordGapTerm05522_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05522, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05522_fast_pow_mod_ne_one

def fullRecordGapValue05523 : Nat := fullRecordGapCenterValue + 276362

theorem fullRecordGapTerm05523_eq_value :
    recordGapCenter + 276362 = fullRecordGapValue05523 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05523_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05523 (fullRecordGapValue05523 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05523_not_prime : ¬(recordGapCenter + 276362).Prime := by
  rw [fullRecordGapTerm05523_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05523, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05523_fast_pow_mod_ne_one

def fullRecordGapValue05524 : Nat := fullRecordGapCenterValue + 276578

theorem fullRecordGapTerm05524_eq_value :
    recordGapCenter + 276578 = fullRecordGapValue05524 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05524_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05524 (fullRecordGapValue05524 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05524_not_prime : ¬(recordGapCenter + 276578).Prime := by
  rw [fullRecordGapTerm05524_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05524, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05524_fast_pow_mod_ne_one

def fullRecordGapValue05525 : Nat := fullRecordGapCenterValue + 276698

theorem fullRecordGapTerm05525_eq_value :
    recordGapCenter + 276698 = fullRecordGapValue05525 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05525_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05525 (fullRecordGapValue05525 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05525_not_prime : ¬(recordGapCenter + 276698).Prime := by
  rw [fullRecordGapTerm05525_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05525, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05525_fast_pow_mod_ne_one

def fullRecordGapValue05526 : Nat := fullRecordGapCenterValue + 276846

theorem fullRecordGapTerm05526_eq_value :
    recordGapCenter + 276846 = fullRecordGapValue05526 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05526_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05526 (fullRecordGapValue05526 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05526_not_prime : ¬(recordGapCenter + 276846).Prime := by
  rw [fullRecordGapTerm05526_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05526, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05526_fast_pow_mod_ne_one

def fullRecordGapValue05527 : Nat := fullRecordGapCenterValue + 276882

theorem fullRecordGapTerm05527_eq_value :
    recordGapCenter + 276882 = fullRecordGapValue05527 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05527_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05527 (fullRecordGapValue05527 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05527_not_prime : ¬(recordGapCenter + 276882).Prime := by
  rw [fullRecordGapTerm05527_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05527, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05527_fast_pow_mod_ne_one

def fullRecordGapValue05528 : Nat := fullRecordGapCenterValue + 276902

theorem fullRecordGapTerm05528_eq_value :
    recordGapCenter + 276902 = fullRecordGapValue05528 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05528_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05528 (fullRecordGapValue05528 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05528_not_prime : ¬(recordGapCenter + 276902).Prime := by
  rw [fullRecordGapTerm05528_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05528, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05528_fast_pow_mod_ne_one

def fullRecordGapValue05529 : Nat := fullRecordGapCenterValue + 277118

theorem fullRecordGapTerm05529_eq_value :
    recordGapCenter + 277118 = fullRecordGapValue05529 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05529_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05529 (fullRecordGapValue05529 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05529_not_prime : ¬(recordGapCenter + 277118).Prime := by
  rw [fullRecordGapTerm05529_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05529, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05529_fast_pow_mod_ne_one

def fullRecordGapValue05530 : Nat := fullRecordGapCenterValue + 277268

theorem fullRecordGapTerm05530_eq_value :
    recordGapCenter + 277268 = fullRecordGapValue05530 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05530_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05530 (fullRecordGapValue05530 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05530_not_prime : ¬(recordGapCenter + 277268).Prime := by
  rw [fullRecordGapTerm05530_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05530, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05530_fast_pow_mod_ne_one

def fullRecordGapValue05531 : Nat := fullRecordGapCenterValue + 277422

theorem fullRecordGapTerm05531_eq_value :
    recordGapCenter + 277422 = fullRecordGapValue05531 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05531_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05531 (fullRecordGapValue05531 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05531_not_prime : ¬(recordGapCenter + 277422).Prime := by
  rw [fullRecordGapTerm05531_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05531, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05531_fast_pow_mod_ne_one

def fullRecordGapValue05532 : Nat := fullRecordGapCenterValue + 277586

theorem fullRecordGapTerm05532_eq_value :
    recordGapCenter + 277586 = fullRecordGapValue05532 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05532_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05532 (fullRecordGapValue05532 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05532_not_prime : ¬(recordGapCenter + 277586).Prime := by
  rw [fullRecordGapTerm05532_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05532, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05532_fast_pow_mod_ne_one

def fullRecordGapValue05533 : Nat := fullRecordGapCenterValue + 277778

theorem fullRecordGapTerm05533_eq_value :
    recordGapCenter + 277778 = fullRecordGapValue05533 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05533_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05533 (fullRecordGapValue05533 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05533_not_prime : ¬(recordGapCenter + 277778).Prime := by
  rw [fullRecordGapTerm05533_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05533, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05533_fast_pow_mod_ne_one

def fullRecordGapValue05534 : Nat := fullRecordGapCenterValue + 277806

theorem fullRecordGapTerm05534_eq_value :
    recordGapCenter + 277806 = fullRecordGapValue05534 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05534_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05534 (fullRecordGapValue05534 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05534_not_prime : ¬(recordGapCenter + 277806).Prime := by
  rw [fullRecordGapTerm05534_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05534, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05534_fast_pow_mod_ne_one

def fullRecordGapValue05535 : Nat := fullRecordGapCenterValue + 277830

theorem fullRecordGapTerm05535_eq_value :
    recordGapCenter + 277830 = fullRecordGapValue05535 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05535_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05535 (fullRecordGapValue05535 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05535_not_prime : ¬(recordGapCenter + 277830).Prime := by
  rw [fullRecordGapTerm05535_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05535, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05535_fast_pow_mod_ne_one

def fullRecordGapValue05536 : Nat := fullRecordGapCenterValue + 277868

theorem fullRecordGapTerm05536_eq_value :
    recordGapCenter + 277868 = fullRecordGapValue05536 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05536_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05536 (fullRecordGapValue05536 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05536_not_prime : ¬(recordGapCenter + 277868).Prime := by
  rw [fullRecordGapTerm05536_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05536, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05536_fast_pow_mod_ne_one

def fullRecordGapValue05537 : Nat := fullRecordGapCenterValue + 278246

theorem fullRecordGapTerm05537_eq_value :
    recordGapCenter + 278246 = fullRecordGapValue05537 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05537_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05537 (fullRecordGapValue05537 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05537_not_prime : ¬(recordGapCenter + 278246).Prime := by
  rw [fullRecordGapTerm05537_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05537, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05537_fast_pow_mod_ne_one

def fullRecordGapValue05538 : Nat := fullRecordGapCenterValue + 278612

theorem fullRecordGapTerm05538_eq_value :
    recordGapCenter + 278612 = fullRecordGapValue05538 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05538_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05538 (fullRecordGapValue05538 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05538_not_prime : ¬(recordGapCenter + 278612).Prime := by
  rw [fullRecordGapTerm05538_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05538, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05538_fast_pow_mod_ne_one

def fullRecordGapValue05539 : Nat := fullRecordGapCenterValue + 278618

theorem fullRecordGapTerm05539_eq_value :
    recordGapCenter + 278618 = fullRecordGapValue05539 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05539_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05539 (fullRecordGapValue05539 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05539_not_prime : ¬(recordGapCenter + 278618).Prime := by
  rw [fullRecordGapTerm05539_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05539, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05539_fast_pow_mod_ne_one

def fullRecordGapValue05540 : Nat := fullRecordGapCenterValue + 278666

theorem fullRecordGapTerm05540_eq_value :
    recordGapCenter + 278666 = fullRecordGapValue05540 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05540_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05540 (fullRecordGapValue05540 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05540_not_prime : ¬(recordGapCenter + 278666).Prime := by
  rw [fullRecordGapTerm05540_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05540, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05540_fast_pow_mod_ne_one

def fullRecordGapValue05541 : Nat := fullRecordGapCenterValue + 278678

theorem fullRecordGapTerm05541_eq_value :
    recordGapCenter + 278678 = fullRecordGapValue05541 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05541_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05541 (fullRecordGapValue05541 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05541_not_prime : ¬(recordGapCenter + 278678).Prime := by
  rw [fullRecordGapTerm05541_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05541, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05541_fast_pow_mod_ne_one

def fullRecordGapValue05542 : Nat := fullRecordGapCenterValue + 278682

theorem fullRecordGapTerm05542_eq_value :
    recordGapCenter + 278682 = fullRecordGapValue05542 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05542_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05542 (fullRecordGapValue05542 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05542_not_prime : ¬(recordGapCenter + 278682).Prime := by
  rw [fullRecordGapTerm05542_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05542, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05542_fast_pow_mod_ne_one

def fullRecordGapValue05543 : Nat := fullRecordGapCenterValue + 278708

theorem fullRecordGapTerm05543_eq_value :
    recordGapCenter + 278708 = fullRecordGapValue05543 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05543_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05543 (fullRecordGapValue05543 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05543_not_prime : ¬(recordGapCenter + 278708).Prime := by
  rw [fullRecordGapTerm05543_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05543, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05543_fast_pow_mod_ne_one

def fullRecordGapValue05544 : Nat := fullRecordGapCenterValue + 278742

theorem fullRecordGapTerm05544_eq_value :
    recordGapCenter + 278742 = fullRecordGapValue05544 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05544_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05544 (fullRecordGapValue05544 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05544_not_prime : ¬(recordGapCenter + 278742).Prime := by
  rw [fullRecordGapTerm05544_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05544, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05544_fast_pow_mod_ne_one

def fullRecordGapValue05545 : Nat := fullRecordGapCenterValue + 278826

theorem fullRecordGapTerm05545_eq_value :
    recordGapCenter + 278826 = fullRecordGapValue05545 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05545_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05545 (fullRecordGapValue05545 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05545_not_prime : ¬(recordGapCenter + 278826).Prime := by
  rw [fullRecordGapTerm05545_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05545, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05545_fast_pow_mod_ne_one

def fullRecordGapValue05546 : Nat := fullRecordGapCenterValue + 278948

theorem fullRecordGapTerm05546_eq_value :
    recordGapCenter + 278948 = fullRecordGapValue05546 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05546_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05546 (fullRecordGapValue05546 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05546_not_prime : ¬(recordGapCenter + 278948).Prime := by
  rw [fullRecordGapTerm05546_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05546, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05546_fast_pow_mod_ne_one

def fullRecordGapValue05547 : Nat := fullRecordGapCenterValue + 279218

theorem fullRecordGapTerm05547_eq_value :
    recordGapCenter + 279218 = fullRecordGapValue05547 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05547_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05547 (fullRecordGapValue05547 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05547_not_prime : ¬(recordGapCenter + 279218).Prime := by
  rw [fullRecordGapTerm05547_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05547, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05547_fast_pow_mod_ne_one

def fullRecordGapValue05548 : Nat := fullRecordGapCenterValue + 279332

theorem fullRecordGapTerm05548_eq_value :
    recordGapCenter + 279332 = fullRecordGapValue05548 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05548_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05548 (fullRecordGapValue05548 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05548_not_prime : ¬(recordGapCenter + 279332).Prime := by
  rw [fullRecordGapTerm05548_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05548, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05548_fast_pow_mod_ne_one

def fullRecordGapValue05549 : Nat := fullRecordGapCenterValue + 279438

theorem fullRecordGapTerm05549_eq_value :
    recordGapCenter + 279438 = fullRecordGapValue05549 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05549_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05549 (fullRecordGapValue05549 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05549_not_prime : ¬(recordGapCenter + 279438).Prime := by
  rw [fullRecordGapTerm05549_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05549, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05549_fast_pow_mod_ne_one

def fullRecordGapValue05550 : Nat := fullRecordGapCenterValue + 279458

theorem fullRecordGapTerm05550_eq_value :
    recordGapCenter + 279458 = fullRecordGapValue05550 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05550_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05550 (fullRecordGapValue05550 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05550_not_prime : ¬(recordGapCenter + 279458).Prime := by
  rw [fullRecordGapTerm05550_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05550, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05550_fast_pow_mod_ne_one

def fullRecordGapValue05551 : Nat := fullRecordGapCenterValue + 279510

theorem fullRecordGapTerm05551_eq_value :
    recordGapCenter + 279510 = fullRecordGapValue05551 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05551_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05551 (fullRecordGapValue05551 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05551_not_prime : ¬(recordGapCenter + 279510).Prime := by
  rw [fullRecordGapTerm05551_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05551, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05551_fast_pow_mod_ne_one

def fullRecordGapValue05552 : Nat := fullRecordGapCenterValue + 279546

theorem fullRecordGapTerm05552_eq_value :
    recordGapCenter + 279546 = fullRecordGapValue05552 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05552_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05552 (fullRecordGapValue05552 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05552_not_prime : ¬(recordGapCenter + 279546).Prime := by
  rw [fullRecordGapTerm05552_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05552, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05552_fast_pow_mod_ne_one

def fullRecordGapValue05553 : Nat := fullRecordGapCenterValue + 279596

theorem fullRecordGapTerm05553_eq_value :
    recordGapCenter + 279596 = fullRecordGapValue05553 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05553_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05553 (fullRecordGapValue05553 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05553_not_prime : ¬(recordGapCenter + 279596).Prime := by
  rw [fullRecordGapTerm05553_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05553, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05553_fast_pow_mod_ne_one

def fullRecordGapValue05554 : Nat := fullRecordGapCenterValue + 279606

theorem fullRecordGapTerm05554_eq_value :
    recordGapCenter + 279606 = fullRecordGapValue05554 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05554_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05554 (fullRecordGapValue05554 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05554_not_prime : ¬(recordGapCenter + 279606).Prime := by
  rw [fullRecordGapTerm05554_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05554, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05554_fast_pow_mod_ne_one

def fullRecordGapValue05555 : Nat := fullRecordGapCenterValue + 279662

theorem fullRecordGapTerm05555_eq_value :
    recordGapCenter + 279662 = fullRecordGapValue05555 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05555_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05555 (fullRecordGapValue05555 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05555_not_prime : ¬(recordGapCenter + 279662).Prime := by
  rw [fullRecordGapTerm05555_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05555, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05555_fast_pow_mod_ne_one

def fullRecordGapValue05556 : Nat := fullRecordGapCenterValue + 279798

theorem fullRecordGapTerm05556_eq_value :
    recordGapCenter + 279798 = fullRecordGapValue05556 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05556_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05556 (fullRecordGapValue05556 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05556_not_prime : ¬(recordGapCenter + 279798).Prime := by
  rw [fullRecordGapTerm05556_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05556, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05556_fast_pow_mod_ne_one

def fullRecordGapValue05557 : Nat := fullRecordGapCenterValue + 279878

theorem fullRecordGapTerm05557_eq_value :
    recordGapCenter + 279878 = fullRecordGapValue05557 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05557_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05557 (fullRecordGapValue05557 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05557_not_prime : ¬(recordGapCenter + 279878).Prime := by
  rw [fullRecordGapTerm05557_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05557, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05557_fast_pow_mod_ne_one

def fullRecordGapValue05558 : Nat := fullRecordGapCenterValue + 279998

theorem fullRecordGapTerm05558_eq_value :
    recordGapCenter + 279998 = fullRecordGapValue05558 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05558_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05558 (fullRecordGapValue05558 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05558_not_prime : ¬(recordGapCenter + 279998).Prime := by
  rw [fullRecordGapTerm05558_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05558, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05558_fast_pow_mod_ne_one

def fullRecordGapValue05559 : Nat := fullRecordGapCenterValue + 280106

theorem fullRecordGapTerm05559_eq_value :
    recordGapCenter + 280106 = fullRecordGapValue05559 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05559_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05559 (fullRecordGapValue05559 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05559_not_prime : ¬(recordGapCenter + 280106).Prime := by
  rw [fullRecordGapTerm05559_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05559, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05559_fast_pow_mod_ne_one

def fullRecordGapValue05560 : Nat := fullRecordGapCenterValue + 280142

theorem fullRecordGapTerm05560_eq_value :
    recordGapCenter + 280142 = fullRecordGapValue05560 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05560_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05560 (fullRecordGapValue05560 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05560_not_prime : ¬(recordGapCenter + 280142).Prime := by
  rw [fullRecordGapTerm05560_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05560, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05560_fast_pow_mod_ne_one

def fullRecordGapValue05561 : Nat := fullRecordGapCenterValue + 280218

theorem fullRecordGapTerm05561_eq_value :
    recordGapCenter + 280218 = fullRecordGapValue05561 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05561_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05561 (fullRecordGapValue05561 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05561_not_prime : ¬(recordGapCenter + 280218).Prime := by
  rw [fullRecordGapTerm05561_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05561, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05561_fast_pow_mod_ne_one

def fullRecordGapValue05562 : Nat := fullRecordGapCenterValue + 280382

theorem fullRecordGapTerm05562_eq_value :
    recordGapCenter + 280382 = fullRecordGapValue05562 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05562_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05562 (fullRecordGapValue05562 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05562_not_prime : ¬(recordGapCenter + 280382).Prime := by
  rw [fullRecordGapTerm05562_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05562, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05562_fast_pow_mod_ne_one

def fullRecordGapValue05563 : Nat := fullRecordGapCenterValue + 280506

theorem fullRecordGapTerm05563_eq_value :
    recordGapCenter + 280506 = fullRecordGapValue05563 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05563_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05563 (fullRecordGapValue05563 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05563_not_prime : ¬(recordGapCenter + 280506).Prime := by
  rw [fullRecordGapTerm05563_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05563, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05563_fast_pow_mod_ne_one

def fullRecordGapValue05564 : Nat := fullRecordGapCenterValue + 280556

theorem fullRecordGapTerm05564_eq_value :
    recordGapCenter + 280556 = fullRecordGapValue05564 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05564_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05564 (fullRecordGapValue05564 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05564_not_prime : ¬(recordGapCenter + 280556).Prime := by
  rw [fullRecordGapTerm05564_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05564, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05564_fast_pow_mod_ne_one

def fullRecordGapValue05565 : Nat := fullRecordGapCenterValue + 280838

theorem fullRecordGapTerm05565_eq_value :
    recordGapCenter + 280838 = fullRecordGapValue05565 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05565_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05565 (fullRecordGapValue05565 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05565_not_prime : ¬(recordGapCenter + 280838).Prime := by
  rw [fullRecordGapTerm05565_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05565, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05565_fast_pow_mod_ne_one

def fullRecordGapValue05566 : Nat := fullRecordGapCenterValue + 280842

theorem fullRecordGapTerm05566_eq_value :
    recordGapCenter + 280842 = fullRecordGapValue05566 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05566_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05566 (fullRecordGapValue05566 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05566_not_prime : ¬(recordGapCenter + 280842).Prime := by
  rw [fullRecordGapTerm05566_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05566, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05566_fast_pow_mod_ne_one

def fullRecordGapValue05567 : Nat := fullRecordGapCenterValue + 280886

theorem fullRecordGapTerm05567_eq_value :
    recordGapCenter + 280886 = fullRecordGapValue05567 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05567_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05567 (fullRecordGapValue05567 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05567_not_prime : ¬(recordGapCenter + 280886).Prime := by
  rw [fullRecordGapTerm05567_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05567, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05567_fast_pow_mod_ne_one

def fullRecordGapValue05568 : Nat := fullRecordGapCenterValue + 280898

theorem fullRecordGapTerm05568_eq_value :
    recordGapCenter + 280898 = fullRecordGapValue05568 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05568_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05568 (fullRecordGapValue05568 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05568_not_prime : ¬(recordGapCenter + 280898).Prime := by
  rw [fullRecordGapTerm05568_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05568, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05568_fast_pow_mod_ne_one

def fullRecordGapValue05569 : Nat := fullRecordGapCenterValue + 281102

theorem fullRecordGapTerm05569_eq_value :
    recordGapCenter + 281102 = fullRecordGapValue05569 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05569_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05569 (fullRecordGapValue05569 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05569_not_prime : ¬(recordGapCenter + 281102).Prime := by
  rw [fullRecordGapTerm05569_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05569, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05569_fast_pow_mod_ne_one

def fullRecordGapValue05570 : Nat := fullRecordGapCenterValue + 281166

theorem fullRecordGapTerm05570_eq_value :
    recordGapCenter + 281166 = fullRecordGapValue05570 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05570_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05570 (fullRecordGapValue05570 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05570_not_prime : ¬(recordGapCenter + 281166).Prime := by
  rw [fullRecordGapTerm05570_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05570, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05570_fast_pow_mod_ne_one

def fullRecordGapValue05571 : Nat := fullRecordGapCenterValue + 281202

theorem fullRecordGapTerm05571_eq_value :
    recordGapCenter + 281202 = fullRecordGapValue05571 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05571_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05571 (fullRecordGapValue05571 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05571_not_prime : ¬(recordGapCenter + 281202).Prime := by
  rw [fullRecordGapTerm05571_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05571, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05571_fast_pow_mod_ne_one

def fullRecordGapValue05572 : Nat := fullRecordGapCenterValue + 281262

theorem fullRecordGapTerm05572_eq_value :
    recordGapCenter + 281262 = fullRecordGapValue05572 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05572_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05572 (fullRecordGapValue05572 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05572_not_prime : ¬(recordGapCenter + 281262).Prime := by
  rw [fullRecordGapTerm05572_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05572, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05572_fast_pow_mod_ne_one

def fullRecordGapValue05573 : Nat := fullRecordGapCenterValue + 281318

theorem fullRecordGapTerm05573_eq_value :
    recordGapCenter + 281318 = fullRecordGapValue05573 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05573_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05573 (fullRecordGapValue05573 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05573_not_prime : ¬(recordGapCenter + 281318).Prime := by
  rw [fullRecordGapTerm05573_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05573, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05573_fast_pow_mod_ne_one

def fullRecordGapValue05574 : Nat := fullRecordGapCenterValue + 281366

theorem fullRecordGapTerm05574_eq_value :
    recordGapCenter + 281366 = fullRecordGapValue05574 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05574_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05574 (fullRecordGapValue05574 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05574_not_prime : ¬(recordGapCenter + 281366).Prime := by
  rw [fullRecordGapTerm05574_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05574, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05574_fast_pow_mod_ne_one

def fullRecordGapValue05575 : Nat := fullRecordGapCenterValue + 281492

theorem fullRecordGapTerm05575_eq_value :
    recordGapCenter + 281492 = fullRecordGapValue05575 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05575_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05575 (fullRecordGapValue05575 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05575_not_prime : ¬(recordGapCenter + 281492).Prime := by
  rw [fullRecordGapTerm05575_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05575, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05575_fast_pow_mod_ne_one

def fullRecordGapValue05576 : Nat := fullRecordGapCenterValue + 281600

theorem fullRecordGapTerm05576_eq_value :
    recordGapCenter + 281600 = fullRecordGapValue05576 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05576_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05576 (fullRecordGapValue05576 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05576_not_prime : ¬(recordGapCenter + 281600).Prime := by
  rw [fullRecordGapTerm05576_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05576, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05576_fast_pow_mod_ne_one

def fullRecordGapValue05577 : Nat := fullRecordGapCenterValue + 281678

theorem fullRecordGapTerm05577_eq_value :
    recordGapCenter + 281678 = fullRecordGapValue05577 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05577_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05577 (fullRecordGapValue05577 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05577_not_prime : ¬(recordGapCenter + 281678).Prime := by
  rw [fullRecordGapTerm05577_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05577, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05577_fast_pow_mod_ne_one

def fullRecordGapValue05578 : Nat := fullRecordGapCenterValue + 281982

theorem fullRecordGapTerm05578_eq_value :
    recordGapCenter + 281982 = fullRecordGapValue05578 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05578_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05578 (fullRecordGapValue05578 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05578_not_prime : ¬(recordGapCenter + 281982).Prime := by
  rw [fullRecordGapTerm05578_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05578, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05578_fast_pow_mod_ne_one

def fullRecordGapValue05579 : Nat := fullRecordGapCenterValue + 282122

theorem fullRecordGapTerm05579_eq_value :
    recordGapCenter + 282122 = fullRecordGapValue05579 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05579_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05579 (fullRecordGapValue05579 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05579_not_prime : ¬(recordGapCenter + 282122).Prime := by
  rw [fullRecordGapTerm05579_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05579, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05579_fast_pow_mod_ne_one

def fullRecordGapValue05580 : Nat := fullRecordGapCenterValue + 282242

theorem fullRecordGapTerm05580_eq_value :
    recordGapCenter + 282242 = fullRecordGapValue05580 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05580_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05580 (fullRecordGapValue05580 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05580_not_prime : ¬(recordGapCenter + 282242).Prime := by
  rw [fullRecordGapTerm05580_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05580, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05580_fast_pow_mod_ne_one

def fullRecordGapValue05581 : Nat := fullRecordGapCenterValue + 282306

theorem fullRecordGapTerm05581_eq_value :
    recordGapCenter + 282306 = fullRecordGapValue05581 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05581_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05581 (fullRecordGapValue05581 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05581_not_prime : ¬(recordGapCenter + 282306).Prime := by
  rw [fullRecordGapTerm05581_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05581, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05581_fast_pow_mod_ne_one

def fullRecordGapValue05582 : Nat := fullRecordGapCenterValue + 282398

theorem fullRecordGapTerm05582_eq_value :
    recordGapCenter + 282398 = fullRecordGapValue05582 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05582_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05582 (fullRecordGapValue05582 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05582_not_prime : ¬(recordGapCenter + 282398).Prime := by
  rw [fullRecordGapTerm05582_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05582, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05582_fast_pow_mod_ne_one

def fullRecordGapValue05583 : Nat := fullRecordGapCenterValue + 282482

theorem fullRecordGapTerm05583_eq_value :
    recordGapCenter + 282482 = fullRecordGapValue05583 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05583_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05583 (fullRecordGapValue05583 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05583_not_prime : ¬(recordGapCenter + 282482).Prime := by
  rw [fullRecordGapTerm05583_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05583, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05583_fast_pow_mod_ne_one

def fullRecordGapValue05584 : Nat := fullRecordGapCenterValue + 282566

theorem fullRecordGapTerm05584_eq_value :
    recordGapCenter + 282566 = fullRecordGapValue05584 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05584_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05584 (fullRecordGapValue05584 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05584_not_prime : ¬(recordGapCenter + 282566).Prime := by
  rw [fullRecordGapTerm05584_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05584, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05584_fast_pow_mod_ne_one

def fullRecordGapValue05585 : Nat := fullRecordGapCenterValue + 282836

theorem fullRecordGapTerm05585_eq_value :
    recordGapCenter + 282836 = fullRecordGapValue05585 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05585_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05585 (fullRecordGapValue05585 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05585_not_prime : ¬(recordGapCenter + 282836).Prime := by
  rw [fullRecordGapTerm05585_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05585, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05585_fast_pow_mod_ne_one

def fullRecordGapValue05586 : Nat := fullRecordGapCenterValue + 282858

theorem fullRecordGapTerm05586_eq_value :
    recordGapCenter + 282858 = fullRecordGapValue05586 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05586_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05586 (fullRecordGapValue05586 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05586_not_prime : ¬(recordGapCenter + 282858).Prime := by
  rw [fullRecordGapTerm05586_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05586, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05586_fast_pow_mod_ne_one

def fullRecordGapValue05587 : Nat := fullRecordGapCenterValue + 282966

theorem fullRecordGapTerm05587_eq_value :
    recordGapCenter + 282966 = fullRecordGapValue05587 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05587_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05587 (fullRecordGapValue05587 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05587_not_prime : ¬(recordGapCenter + 282966).Prime := by
  rw [fullRecordGapTerm05587_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05587, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05587_fast_pow_mod_ne_one

def fullRecordGapValue05588 : Nat := fullRecordGapCenterValue + 283076

theorem fullRecordGapTerm05588_eq_value :
    recordGapCenter + 283076 = fullRecordGapValue05588 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05588_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05588 (fullRecordGapValue05588 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05588_not_prime : ¬(recordGapCenter + 283076).Prime := by
  rw [fullRecordGapTerm05588_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05588, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05588_fast_pow_mod_ne_one

def fullRecordGapValue05589 : Nat := fullRecordGapCenterValue + 283238

theorem fullRecordGapTerm05589_eq_value :
    recordGapCenter + 283238 = fullRecordGapValue05589 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05589_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05589 (fullRecordGapValue05589 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05589_not_prime : ¬(recordGapCenter + 283238).Prime := by
  rw [fullRecordGapTerm05589_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05589, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05589_fast_pow_mod_ne_one

def fullRecordGapValue05590 : Nat := fullRecordGapCenterValue + 283242

theorem fullRecordGapTerm05590_eq_value :
    recordGapCenter + 283242 = fullRecordGapValue05590 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05590_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05590 (fullRecordGapValue05590 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05590_not_prime : ¬(recordGapCenter + 283242).Prime := by
  rw [fullRecordGapTerm05590_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05590, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05590_fast_pow_mod_ne_one

def fullRecordGapValue05591 : Nat := fullRecordGapCenterValue + 283298

theorem fullRecordGapTerm05591_eq_value :
    recordGapCenter + 283298 = fullRecordGapValue05591 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05591_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05591 (fullRecordGapValue05591 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05591_not_prime : ¬(recordGapCenter + 283298).Prime := by
  rw [fullRecordGapTerm05591_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05591, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05591_fast_pow_mod_ne_one

def fullRecordGapValue05592 : Nat := fullRecordGapCenterValue + 283358

theorem fullRecordGapTerm05592_eq_value :
    recordGapCenter + 283358 = fullRecordGapValue05592 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05592_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05592 (fullRecordGapValue05592 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05592_not_prime : ¬(recordGapCenter + 283358).Prime := by
  rw [fullRecordGapTerm05592_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05592, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05592_fast_pow_mod_ne_one

def fullRecordGapValue05593 : Nat := fullRecordGapCenterValue + 283418

theorem fullRecordGapTerm05593_eq_value :
    recordGapCenter + 283418 = fullRecordGapValue05593 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05593_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05593 (fullRecordGapValue05593 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05593_not_prime : ¬(recordGapCenter + 283418).Prime := by
  rw [fullRecordGapTerm05593_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05593, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05593_fast_pow_mod_ne_one

def fullRecordGapValue05594 : Nat := fullRecordGapCenterValue + 283500

theorem fullRecordGapTerm05594_eq_value :
    recordGapCenter + 283500 = fullRecordGapValue05594 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05594_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05594 (fullRecordGapValue05594 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05594_not_prime : ¬(recordGapCenter + 283500).Prime := by
  rw [fullRecordGapTerm05594_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05594, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05594_fast_pow_mod_ne_one

def fullRecordGapValue05595 : Nat := fullRecordGapCenterValue + 283586

theorem fullRecordGapTerm05595_eq_value :
    recordGapCenter + 283586 = fullRecordGapValue05595 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05595_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05595 (fullRecordGapValue05595 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05595_not_prime : ¬(recordGapCenter + 283586).Prime := by
  rw [fullRecordGapTerm05595_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05595, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05595_fast_pow_mod_ne_one

def fullRecordGapValue05596 : Nat := fullRecordGapCenterValue + 283622

theorem fullRecordGapTerm05596_eq_value :
    recordGapCenter + 283622 = fullRecordGapValue05596 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05596_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05596 (fullRecordGapValue05596 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05596_not_prime : ¬(recordGapCenter + 283622).Prime := by
  rw [fullRecordGapTerm05596_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05596, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05596_fast_pow_mod_ne_one

def fullRecordGapValue05597 : Nat := fullRecordGapCenterValue + 283658

theorem fullRecordGapTerm05597_eq_value :
    recordGapCenter + 283658 = fullRecordGapValue05597 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05597_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05597 (fullRecordGapValue05597 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05597_not_prime : ¬(recordGapCenter + 283658).Prime := by
  rw [fullRecordGapTerm05597_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05597, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05597_fast_pow_mod_ne_one

def fullRecordGapValue05598 : Nat := fullRecordGapCenterValue + 283676

theorem fullRecordGapTerm05598_eq_value :
    recordGapCenter + 283676 = fullRecordGapValue05598 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05598_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05598 (fullRecordGapValue05598 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05598_not_prime : ¬(recordGapCenter + 283676).Prime := by
  rw [fullRecordGapTerm05598_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05598, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05598_fast_pow_mod_ne_one

def fullRecordGapValue05599 : Nat := fullRecordGapCenterValue + 283706

theorem fullRecordGapTerm05599_eq_value :
    recordGapCenter + 283706 = fullRecordGapValue05599 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05599_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05599 (fullRecordGapValue05599 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05599_not_prime : ¬(recordGapCenter + 283706).Prime := by
  rw [fullRecordGapTerm05599_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05599, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05599_fast_pow_mod_ne_one

def fullRecordGapValue05600 : Nat := fullRecordGapCenterValue + 283742

theorem fullRecordGapTerm05600_eq_value :
    recordGapCenter + 283742 = fullRecordGapValue05600 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05600_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05600 (fullRecordGapValue05600 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05600_not_prime : ¬(recordGapCenter + 283742).Prime := by
  rw [fullRecordGapTerm05600_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05600, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05600_fast_pow_mod_ne_one

def fullRecordGapValue05601 : Nat := fullRecordGapCenterValue + 283748

theorem fullRecordGapTerm05601_eq_value :
    recordGapCenter + 283748 = fullRecordGapValue05601 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05601_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05601 (fullRecordGapValue05601 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05601_not_prime : ¬(recordGapCenter + 283748).Prime := by
  rw [fullRecordGapTerm05601_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05601, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05601_fast_pow_mod_ne_one

def fullRecordGapValue05602 : Nat := fullRecordGapCenterValue + 283782

theorem fullRecordGapTerm05602_eq_value :
    recordGapCenter + 283782 = fullRecordGapValue05602 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05602_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05602 (fullRecordGapValue05602 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05602_not_prime : ¬(recordGapCenter + 283782).Prime := by
  rw [fullRecordGapTerm05602_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05602, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05602_fast_pow_mod_ne_one

def fullRecordGapValue05603 : Nat := fullRecordGapCenterValue + 283902

theorem fullRecordGapTerm05603_eq_value :
    recordGapCenter + 283902 = fullRecordGapValue05603 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05603_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05603 (fullRecordGapValue05603 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05603_not_prime : ¬(recordGapCenter + 283902).Prime := by
  rw [fullRecordGapTerm05603_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05603, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05603_fast_pow_mod_ne_one

def fullRecordGapValue05604 : Nat := fullRecordGapCenterValue + 283916

theorem fullRecordGapTerm05604_eq_value :
    recordGapCenter + 283916 = fullRecordGapValue05604 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05604_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05604 (fullRecordGapValue05604 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05604_not_prime : ¬(recordGapCenter + 283916).Prime := by
  rw [fullRecordGapTerm05604_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05604, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05604_fast_pow_mod_ne_one

def fullRecordGapValue05605 : Nat := fullRecordGapCenterValue + 283922

theorem fullRecordGapTerm05605_eq_value :
    recordGapCenter + 283922 = fullRecordGapValue05605 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05605_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05605 (fullRecordGapValue05605 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05605_not_prime : ¬(recordGapCenter + 283922).Prime := by
  rw [fullRecordGapTerm05605_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05605, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05605_fast_pow_mod_ne_one

def fullRecordGapValue05606 : Nat := fullRecordGapCenterValue + 283988

theorem fullRecordGapTerm05606_eq_value :
    recordGapCenter + 283988 = fullRecordGapValue05606 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05606_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05606 (fullRecordGapValue05606 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05606_not_prime : ¬(recordGapCenter + 283988).Prime := by
  rw [fullRecordGapTerm05606_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05606, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05606_fast_pow_mod_ne_one

def fullRecordGapValue05607 : Nat := fullRecordGapCenterValue + 284156

theorem fullRecordGapTerm05607_eq_value :
    recordGapCenter + 284156 = fullRecordGapValue05607 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05607_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05607 (fullRecordGapValue05607 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05607_not_prime : ¬(recordGapCenter + 284156).Prime := by
  rw [fullRecordGapTerm05607_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05607, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05607_fast_pow_mod_ne_one

def fullRecordGapValue05608 : Nat := fullRecordGapCenterValue + 284198

theorem fullRecordGapTerm05608_eq_value :
    recordGapCenter + 284198 = fullRecordGapValue05608 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05608_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05608 (fullRecordGapValue05608 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05608_not_prime : ¬(recordGapCenter + 284198).Prime := by
  rw [fullRecordGapTerm05608_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05608, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05608_fast_pow_mod_ne_one

def fullRecordGapValue05609 : Nat := fullRecordGapCenterValue + 284222

theorem fullRecordGapTerm05609_eq_value :
    recordGapCenter + 284222 = fullRecordGapValue05609 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05609_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05609 (fullRecordGapValue05609 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05609_not_prime : ¬(recordGapCenter + 284222).Prime := by
  rw [fullRecordGapTerm05609_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05609, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05609_fast_pow_mod_ne_one

def fullRecordGapValue05610 : Nat := fullRecordGapCenterValue + 284322

theorem fullRecordGapTerm05610_eq_value :
    recordGapCenter + 284322 = fullRecordGapValue05610 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05610_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05610 (fullRecordGapValue05610 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05610_not_prime : ¬(recordGapCenter + 284322).Prime := by
  rw [fullRecordGapTerm05610_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05610, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05610_fast_pow_mod_ne_one

def fullRecordGapValue05611 : Nat := fullRecordGapCenterValue + 284516

theorem fullRecordGapTerm05611_eq_value :
    recordGapCenter + 284516 = fullRecordGapValue05611 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05611_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05611 (fullRecordGapValue05611 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05611_not_prime : ¬(recordGapCenter + 284516).Prime := by
  rw [fullRecordGapTerm05611_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05611, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05611_fast_pow_mod_ne_one

def fullRecordGapValue05612 : Nat := fullRecordGapCenterValue + 284646

theorem fullRecordGapTerm05612_eq_value :
    recordGapCenter + 284646 = fullRecordGapValue05612 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05612_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05612 (fullRecordGapValue05612 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05612_not_prime : ¬(recordGapCenter + 284646).Prime := by
  rw [fullRecordGapTerm05612_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05612, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05612_fast_pow_mod_ne_one

def fullRecordGapValue05613 : Nat := fullRecordGapCenterValue + 284762

theorem fullRecordGapTerm05613_eq_value :
    recordGapCenter + 284762 = fullRecordGapValue05613 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05613_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05613 (fullRecordGapValue05613 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05613_not_prime : ¬(recordGapCenter + 284762).Prime := by
  rw [fullRecordGapTerm05613_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05613, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05613_fast_pow_mod_ne_one

def fullRecordGapValue05614 : Nat := fullRecordGapCenterValue + 284996

theorem fullRecordGapTerm05614_eq_value :
    recordGapCenter + 284996 = fullRecordGapValue05614 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05614_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05614 (fullRecordGapValue05614 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05614_not_prime : ¬(recordGapCenter + 284996).Prime := by
  rw [fullRecordGapTerm05614_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05614, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05614_fast_pow_mod_ne_one

def fullRecordGapValue05615 : Nat := fullRecordGapCenterValue + 285078

theorem fullRecordGapTerm05615_eq_value :
    recordGapCenter + 285078 = fullRecordGapValue05615 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05615_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05615 (fullRecordGapValue05615 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05615_not_prime : ¬(recordGapCenter + 285078).Prime := by
  rw [fullRecordGapTerm05615_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05615, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05615_fast_pow_mod_ne_one

def fullRecordGapValue05616 : Nat := fullRecordGapCenterValue + 285086

theorem fullRecordGapTerm05616_eq_value :
    recordGapCenter + 285086 = fullRecordGapValue05616 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05616_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05616 (fullRecordGapValue05616 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05616_not_prime : ¬(recordGapCenter + 285086).Prime := by
  rw [fullRecordGapTerm05616_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05616, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05616_fast_pow_mod_ne_one

def fullRecordGapValue05617 : Nat := fullRecordGapCenterValue + 285120

theorem fullRecordGapTerm05617_eq_value :
    recordGapCenter + 285120 = fullRecordGapValue05617 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05617_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05617 (fullRecordGapValue05617 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05617_not_prime : ¬(recordGapCenter + 285120).Prime := by
  rw [fullRecordGapTerm05617_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05617, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05617_fast_pow_mod_ne_one

def fullRecordGapValue05618 : Nat := fullRecordGapCenterValue + 285126

theorem fullRecordGapTerm05618_eq_value :
    recordGapCenter + 285126 = fullRecordGapValue05618 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05618_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05618 (fullRecordGapValue05618 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05618_not_prime : ¬(recordGapCenter + 285126).Prime := by
  rw [fullRecordGapTerm05618_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05618, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05618_fast_pow_mod_ne_one

def fullRecordGapValue05619 : Nat := fullRecordGapCenterValue + 285146

theorem fullRecordGapTerm05619_eq_value :
    recordGapCenter + 285146 = fullRecordGapValue05619 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05619_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05619 (fullRecordGapValue05619 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05619_not_prime : ¬(recordGapCenter + 285146).Prime := by
  rw [fullRecordGapTerm05619_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05619, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05619_fast_pow_mod_ne_one

def fullRecordGapValue05620 : Nat := fullRecordGapCenterValue + 285162

theorem fullRecordGapTerm05620_eq_value :
    recordGapCenter + 285162 = fullRecordGapValue05620 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05620_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05620 (fullRecordGapValue05620 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05620_not_prime : ¬(recordGapCenter + 285162).Prime := by
  rw [fullRecordGapTerm05620_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05620, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05620_fast_pow_mod_ne_one

def fullRecordGapValue05621 : Nat := fullRecordGapCenterValue + 285198

theorem fullRecordGapTerm05621_eq_value :
    recordGapCenter + 285198 = fullRecordGapValue05621 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05621_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05621 (fullRecordGapValue05621 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05621_not_prime : ¬(recordGapCenter + 285198).Prime := by
  rw [fullRecordGapTerm05621_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05621, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05621_fast_pow_mod_ne_one

def fullRecordGapValue05622 : Nat := fullRecordGapCenterValue + 285356

theorem fullRecordGapTerm05622_eq_value :
    recordGapCenter + 285356 = fullRecordGapValue05622 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05622_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05622 (fullRecordGapValue05622 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05622_not_prime : ¬(recordGapCenter + 285356).Prime := by
  rw [fullRecordGapTerm05622_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05622, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05622_fast_pow_mod_ne_one

def fullRecordGapValue05623 : Nat := fullRecordGapCenterValue + 285378

theorem fullRecordGapTerm05623_eq_value :
    recordGapCenter + 285378 = fullRecordGapValue05623 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05623_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05623 (fullRecordGapValue05623 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05623_not_prime : ¬(recordGapCenter + 285378).Prime := by
  rw [fullRecordGapTerm05623_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05623, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05623_fast_pow_mod_ne_one

def fullRecordGapValue05624 : Nat := fullRecordGapCenterValue + 285422

theorem fullRecordGapTerm05624_eq_value :
    recordGapCenter + 285422 = fullRecordGapValue05624 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05624_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05624 (fullRecordGapValue05624 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05624_not_prime : ¬(recordGapCenter + 285422).Prime := by
  rw [fullRecordGapTerm05624_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05624, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05624_fast_pow_mod_ne_one

def fullRecordGapValue05625 : Nat := fullRecordGapCenterValue + 285518

theorem fullRecordGapTerm05625_eq_value :
    recordGapCenter + 285518 = fullRecordGapValue05625 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05625_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05625 (fullRecordGapValue05625 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05625_not_prime : ¬(recordGapCenter + 285518).Prime := by
  rw [fullRecordGapTerm05625_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05625, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05625_fast_pow_mod_ne_one

def fullRecordGapValue05626 : Nat := fullRecordGapCenterValue + 285542

theorem fullRecordGapTerm05626_eq_value :
    recordGapCenter + 285542 = fullRecordGapValue05626 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05626_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05626 (fullRecordGapValue05626 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05626_not_prime : ¬(recordGapCenter + 285542).Prime := by
  rw [fullRecordGapTerm05626_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05626, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05626_fast_pow_mod_ne_one

def fullRecordGapValue05627 : Nat := fullRecordGapCenterValue + 285596

theorem fullRecordGapTerm05627_eq_value :
    recordGapCenter + 285596 = fullRecordGapValue05627 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05627_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05627 (fullRecordGapValue05627 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05627_not_prime : ¬(recordGapCenter + 285596).Prime := by
  rw [fullRecordGapTerm05627_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05627, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05627_fast_pow_mod_ne_one

def fullRecordGapValue05628 : Nat := fullRecordGapCenterValue + 285716

theorem fullRecordGapTerm05628_eq_value :
    recordGapCenter + 285716 = fullRecordGapValue05628 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05628_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05628 (fullRecordGapValue05628 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05628_not_prime : ¬(recordGapCenter + 285716).Prime := by
  rw [fullRecordGapTerm05628_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05628, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05628_fast_pow_mod_ne_one

def fullRecordGapValue05629 : Nat := fullRecordGapCenterValue + 285768

theorem fullRecordGapTerm05629_eq_value :
    recordGapCenter + 285768 = fullRecordGapValue05629 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05629_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05629 (fullRecordGapValue05629 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05629_not_prime : ¬(recordGapCenter + 285768).Prime := by
  rw [fullRecordGapTerm05629_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05629, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05629_fast_pow_mod_ne_one

def fullRecordGapValue05630 : Nat := fullRecordGapCenterValue + 285932

theorem fullRecordGapTerm05630_eq_value :
    recordGapCenter + 285932 = fullRecordGapValue05630 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05630_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05630 (fullRecordGapValue05630 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05630_not_prime : ¬(recordGapCenter + 285932).Prime := by
  rw [fullRecordGapTerm05630_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05630, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05630_fast_pow_mod_ne_one

def fullRecordGapValue05631 : Nat := fullRecordGapCenterValue + 285962

theorem fullRecordGapTerm05631_eq_value :
    recordGapCenter + 285962 = fullRecordGapValue05631 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05631_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05631 (fullRecordGapValue05631 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05631_not_prime : ¬(recordGapCenter + 285962).Prime := by
  rw [fullRecordGapTerm05631_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05631, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05631_fast_pow_mod_ne_one

def fullRecordGapValue05632 : Nat := fullRecordGapCenterValue + 286196

theorem fullRecordGapTerm05632_eq_value :
    recordGapCenter + 286196 = fullRecordGapValue05632 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05632_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05632 (fullRecordGapValue05632 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05632_not_prime : ¬(recordGapCenter + 286196).Prime := by
  rw [fullRecordGapTerm05632_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05632, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05632_fast_pow_mod_ne_one

end PrimeFactorUnimodality
