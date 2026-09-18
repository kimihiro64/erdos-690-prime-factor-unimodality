import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue02305 : Nat := fullRecordGapCenterValue - 264742

theorem fullRecordGapTerm02305_eq_value :
    recordGapCenter - 264742 = fullRecordGapValue02305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02305 (fullRecordGapValue02305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02305_not_prime : ¬(recordGapCenter - 264742).Prime := by
  rw [fullRecordGapTerm02305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02305_fast_pow_mod_ne_one

def fullRecordGapValue02306 : Nat := fullRecordGapCenterValue - 264714

theorem fullRecordGapTerm02306_eq_value :
    recordGapCenter - 264714 = fullRecordGapValue02306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02306 (fullRecordGapValue02306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02306_not_prime : ¬(recordGapCenter - 264714).Prime := by
  rw [fullRecordGapTerm02306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02306_fast_pow_mod_ne_one

def fullRecordGapValue02307 : Nat := fullRecordGapCenterValue - 264600

theorem fullRecordGapTerm02307_eq_value :
    recordGapCenter - 264600 = fullRecordGapValue02307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02307 (fullRecordGapValue02307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02307_not_prime : ¬(recordGapCenter - 264600).Prime := by
  rw [fullRecordGapTerm02307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02307_fast_pow_mod_ne_one

def fullRecordGapValue02308 : Nat := fullRecordGapCenterValue - 264514

theorem fullRecordGapTerm02308_eq_value :
    recordGapCenter - 264514 = fullRecordGapValue02308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02308 (fullRecordGapValue02308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02308_not_prime : ¬(recordGapCenter - 264514).Prime := by
  rw [fullRecordGapTerm02308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02308_fast_pow_mod_ne_one

def fullRecordGapValue02309 : Nat := fullRecordGapCenterValue - 264274

theorem fullRecordGapTerm02309_eq_value :
    recordGapCenter - 264274 = fullRecordGapValue02309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02309 (fullRecordGapValue02309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02309_not_prime : ¬(recordGapCenter - 264274).Prime := by
  rw [fullRecordGapTerm02309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02309_fast_pow_mod_ne_one

def fullRecordGapValue02310 : Nat := fullRecordGapCenterValue - 264162

theorem fullRecordGapTerm02310_eq_value :
    recordGapCenter - 264162 = fullRecordGapValue02310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02310 (fullRecordGapValue02310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02310_not_prime : ¬(recordGapCenter - 264162).Prime := by
  rw [fullRecordGapTerm02310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02310_fast_pow_mod_ne_one

def fullRecordGapValue02311 : Nat := fullRecordGapCenterValue - 264148

theorem fullRecordGapTerm02311_eq_value :
    recordGapCenter - 264148 = fullRecordGapValue02311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02311 (fullRecordGapValue02311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02311_not_prime : ¬(recordGapCenter - 264148).Prime := by
  rw [fullRecordGapTerm02311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02311_fast_pow_mod_ne_one

def fullRecordGapValue02312 : Nat := fullRecordGapCenterValue - 264142

theorem fullRecordGapTerm02312_eq_value :
    recordGapCenter - 264142 = fullRecordGapValue02312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02312 (fullRecordGapValue02312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02312_not_prime : ¬(recordGapCenter - 264142).Prime := by
  rw [fullRecordGapTerm02312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02312_fast_pow_mod_ne_one

def fullRecordGapValue02313 : Nat := fullRecordGapCenterValue - 264102

theorem fullRecordGapTerm02313_eq_value :
    recordGapCenter - 264102 = fullRecordGapValue02313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02313 (fullRecordGapValue02313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02313_not_prime : ¬(recordGapCenter - 264102).Prime := by
  rw [fullRecordGapTerm02313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02313_fast_pow_mod_ne_one

def fullRecordGapValue02314 : Nat := fullRecordGapCenterValue - 263932

theorem fullRecordGapTerm02314_eq_value :
    recordGapCenter - 263932 = fullRecordGapValue02314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02314 (fullRecordGapValue02314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02314_not_prime : ¬(recordGapCenter - 263932).Prime := by
  rw [fullRecordGapTerm02314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02314_fast_pow_mod_ne_one

def fullRecordGapValue02315 : Nat := fullRecordGapCenterValue - 263878

theorem fullRecordGapTerm02315_eq_value :
    recordGapCenter - 263878 = fullRecordGapValue02315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02315 (fullRecordGapValue02315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02315_not_prime : ¬(recordGapCenter - 263878).Prime := by
  rw [fullRecordGapTerm02315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02315_fast_pow_mod_ne_one

def fullRecordGapValue02316 : Nat := fullRecordGapCenterValue - 263854

theorem fullRecordGapTerm02316_eq_value :
    recordGapCenter - 263854 = fullRecordGapValue02316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02316 (fullRecordGapValue02316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02316_not_prime : ¬(recordGapCenter - 263854).Prime := by
  rw [fullRecordGapTerm02316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02316_fast_pow_mod_ne_one

def fullRecordGapValue02317 : Nat := fullRecordGapCenterValue - 263814

theorem fullRecordGapTerm02317_eq_value :
    recordGapCenter - 263814 = fullRecordGapValue02317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02317 (fullRecordGapValue02317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02317_not_prime : ¬(recordGapCenter - 263814).Prime := by
  rw [fullRecordGapTerm02317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02317_fast_pow_mod_ne_one

def fullRecordGapValue02318 : Nat := fullRecordGapCenterValue - 263778

theorem fullRecordGapTerm02318_eq_value :
    recordGapCenter - 263778 = fullRecordGapValue02318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02318 (fullRecordGapValue02318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02318_not_prime : ¬(recordGapCenter - 263778).Prime := by
  rw [fullRecordGapTerm02318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02318_fast_pow_mod_ne_one

def fullRecordGapValue02319 : Nat := fullRecordGapCenterValue - 263598

theorem fullRecordGapTerm02319_eq_value :
    recordGapCenter - 263598 = fullRecordGapValue02319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02319 (fullRecordGapValue02319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02319_not_prime : ¬(recordGapCenter - 263598).Prime := by
  rw [fullRecordGapTerm02319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02319_fast_pow_mod_ne_one

def fullRecordGapValue02320 : Nat := fullRecordGapCenterValue - 263554

theorem fullRecordGapTerm02320_eq_value :
    recordGapCenter - 263554 = fullRecordGapValue02320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02320 (fullRecordGapValue02320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02320_not_prime : ¬(recordGapCenter - 263554).Prime := by
  rw [fullRecordGapTerm02320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02320_fast_pow_mod_ne_one

def fullRecordGapValue02321 : Nat := fullRecordGapCenterValue - 263518

theorem fullRecordGapTerm02321_eq_value :
    recordGapCenter - 263518 = fullRecordGapValue02321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02321 (fullRecordGapValue02321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02321_not_prime : ¬(recordGapCenter - 263518).Prime := by
  rw [fullRecordGapTerm02321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02321_fast_pow_mod_ne_one

def fullRecordGapValue02322 : Nat := fullRecordGapCenterValue - 263422

theorem fullRecordGapTerm02322_eq_value :
    recordGapCenter - 263422 = fullRecordGapValue02322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02322 (fullRecordGapValue02322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02322_not_prime : ¬(recordGapCenter - 263422).Prime := by
  rw [fullRecordGapTerm02322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02322_fast_pow_mod_ne_one

def fullRecordGapValue02323 : Nat := fullRecordGapCenterValue - 263202

theorem fullRecordGapTerm02323_eq_value :
    recordGapCenter - 263202 = fullRecordGapValue02323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02323 (fullRecordGapValue02323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02323_not_prime : ¬(recordGapCenter - 263202).Prime := by
  rw [fullRecordGapTerm02323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02323_fast_pow_mod_ne_one

def fullRecordGapValue02324 : Nat := fullRecordGapCenterValue - 263182

theorem fullRecordGapTerm02324_eq_value :
    recordGapCenter - 263182 = fullRecordGapValue02324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02324 (fullRecordGapValue02324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02324_not_prime : ¬(recordGapCenter - 263182).Prime := by
  rw [fullRecordGapTerm02324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02324_fast_pow_mod_ne_one

def fullRecordGapValue02325 : Nat := fullRecordGapCenterValue - 263118

theorem fullRecordGapTerm02325_eq_value :
    recordGapCenter - 263118 = fullRecordGapValue02325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02325 (fullRecordGapValue02325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02325_not_prime : ¬(recordGapCenter - 263118).Prime := by
  rw [fullRecordGapTerm02325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02325_fast_pow_mod_ne_one

def fullRecordGapValue02326 : Nat := fullRecordGapCenterValue - 263044

theorem fullRecordGapTerm02326_eq_value :
    recordGapCenter - 263044 = fullRecordGapValue02326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02326 (fullRecordGapValue02326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02326_not_prime : ¬(recordGapCenter - 263044).Prime := by
  rw [fullRecordGapTerm02326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02326_fast_pow_mod_ne_one

def fullRecordGapValue02327 : Nat := fullRecordGapCenterValue - 262978

theorem fullRecordGapTerm02327_eq_value :
    recordGapCenter - 262978 = fullRecordGapValue02327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02327 (fullRecordGapValue02327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02327_not_prime : ¬(recordGapCenter - 262978).Prime := by
  rw [fullRecordGapTerm02327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02327_fast_pow_mod_ne_one

def fullRecordGapValue02328 : Nat := fullRecordGapCenterValue - 262954

theorem fullRecordGapTerm02328_eq_value :
    recordGapCenter - 262954 = fullRecordGapValue02328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02328 (fullRecordGapValue02328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02328_not_prime : ¬(recordGapCenter - 262954).Prime := by
  rw [fullRecordGapTerm02328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02328_fast_pow_mod_ne_one

def fullRecordGapValue02329 : Nat := fullRecordGapCenterValue - 262894

theorem fullRecordGapTerm02329_eq_value :
    recordGapCenter - 262894 = fullRecordGapValue02329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02329 (fullRecordGapValue02329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02329_not_prime : ¬(recordGapCenter - 262894).Prime := by
  rw [fullRecordGapTerm02329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02329_fast_pow_mod_ne_one

def fullRecordGapValue02330 : Nat := fullRecordGapCenterValue - 262852

theorem fullRecordGapTerm02330_eq_value :
    recordGapCenter - 262852 = fullRecordGapValue02330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02330 (fullRecordGapValue02330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02330_not_prime : ¬(recordGapCenter - 262852).Prime := by
  rw [fullRecordGapTerm02330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02330_fast_pow_mod_ne_one

def fullRecordGapValue02331 : Nat := fullRecordGapCenterValue - 262762

theorem fullRecordGapTerm02331_eq_value :
    recordGapCenter - 262762 = fullRecordGapValue02331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02331 (fullRecordGapValue02331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02331_not_prime : ¬(recordGapCenter - 262762).Prime := by
  rw [fullRecordGapTerm02331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02331_fast_pow_mod_ne_one

def fullRecordGapValue02332 : Nat := fullRecordGapCenterValue - 262722

theorem fullRecordGapTerm02332_eq_value :
    recordGapCenter - 262722 = fullRecordGapValue02332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02332 (fullRecordGapValue02332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02332_not_prime : ¬(recordGapCenter - 262722).Prime := by
  rw [fullRecordGapTerm02332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02332_fast_pow_mod_ne_one

def fullRecordGapValue02333 : Nat := fullRecordGapCenterValue - 262714

theorem fullRecordGapTerm02333_eq_value :
    recordGapCenter - 262714 = fullRecordGapValue02333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02333 (fullRecordGapValue02333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02333_not_prime : ¬(recordGapCenter - 262714).Prime := by
  rw [fullRecordGapTerm02333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02333_fast_pow_mod_ne_one

def fullRecordGapValue02334 : Nat := fullRecordGapCenterValue - 262698

theorem fullRecordGapTerm02334_eq_value :
    recordGapCenter - 262698 = fullRecordGapValue02334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02334 (fullRecordGapValue02334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02334_not_prime : ¬(recordGapCenter - 262698).Prime := by
  rw [fullRecordGapTerm02334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02334_fast_pow_mod_ne_one

def fullRecordGapValue02335 : Nat := fullRecordGapCenterValue - 262642

theorem fullRecordGapTerm02335_eq_value :
    recordGapCenter - 262642 = fullRecordGapValue02335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02335 (fullRecordGapValue02335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02335_not_prime : ¬(recordGapCenter - 262642).Prime := by
  rw [fullRecordGapTerm02335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02335_fast_pow_mod_ne_one

def fullRecordGapValue02336 : Nat := fullRecordGapCenterValue - 262594

theorem fullRecordGapTerm02336_eq_value :
    recordGapCenter - 262594 = fullRecordGapValue02336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02336 (fullRecordGapValue02336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02336_not_prime : ¬(recordGapCenter - 262594).Prime := by
  rw [fullRecordGapTerm02336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02336_fast_pow_mod_ne_one

def fullRecordGapValue02337 : Nat := fullRecordGapCenterValue - 262554

theorem fullRecordGapTerm02337_eq_value :
    recordGapCenter - 262554 = fullRecordGapValue02337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02337 (fullRecordGapValue02337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02337_not_prime : ¬(recordGapCenter - 262554).Prime := by
  rw [fullRecordGapTerm02337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02337_fast_pow_mod_ne_one

def fullRecordGapValue02338 : Nat := fullRecordGapCenterValue - 262498

theorem fullRecordGapTerm02338_eq_value :
    recordGapCenter - 262498 = fullRecordGapValue02338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02338 (fullRecordGapValue02338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02338_not_prime : ¬(recordGapCenter - 262498).Prime := by
  rw [fullRecordGapTerm02338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02338_fast_pow_mod_ne_one

def fullRecordGapValue02339 : Nat := fullRecordGapCenterValue - 262440

theorem fullRecordGapTerm02339_eq_value :
    recordGapCenter - 262440 = fullRecordGapValue02339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02339 (fullRecordGapValue02339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02339_not_prime : ¬(recordGapCenter - 262440).Prime := by
  rw [fullRecordGapTerm02339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02339_fast_pow_mod_ne_one

def fullRecordGapValue02340 : Nat := fullRecordGapCenterValue - 262348

theorem fullRecordGapTerm02340_eq_value :
    recordGapCenter - 262348 = fullRecordGapValue02340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02340 (fullRecordGapValue02340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02340_not_prime : ¬(recordGapCenter - 262348).Prime := by
  rw [fullRecordGapTerm02340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02340_fast_pow_mod_ne_one

def fullRecordGapValue02341 : Nat := fullRecordGapCenterValue - 262324

theorem fullRecordGapTerm02341_eq_value :
    recordGapCenter - 262324 = fullRecordGapValue02341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02341 (fullRecordGapValue02341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02341_not_prime : ¬(recordGapCenter - 262324).Prime := by
  rw [fullRecordGapTerm02341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02341_fast_pow_mod_ne_one

def fullRecordGapValue02342 : Nat := fullRecordGapCenterValue - 262258

theorem fullRecordGapTerm02342_eq_value :
    recordGapCenter - 262258 = fullRecordGapValue02342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02342 (fullRecordGapValue02342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02342_not_prime : ¬(recordGapCenter - 262258).Prime := by
  rw [fullRecordGapTerm02342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02342_fast_pow_mod_ne_one

def fullRecordGapValue02343 : Nat := fullRecordGapCenterValue - 262204

theorem fullRecordGapTerm02343_eq_value :
    recordGapCenter - 262204 = fullRecordGapValue02343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02343 (fullRecordGapValue02343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02343_not_prime : ¬(recordGapCenter - 262204).Prime := by
  rw [fullRecordGapTerm02343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02343_fast_pow_mod_ne_one

def fullRecordGapValue02344 : Nat := fullRecordGapCenterValue - 262084

theorem fullRecordGapTerm02344_eq_value :
    recordGapCenter - 262084 = fullRecordGapValue02344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02344 (fullRecordGapValue02344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02344_not_prime : ¬(recordGapCenter - 262084).Prime := by
  rw [fullRecordGapTerm02344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02344_fast_pow_mod_ne_one

def fullRecordGapValue02345 : Nat := fullRecordGapCenterValue - 262014

theorem fullRecordGapTerm02345_eq_value :
    recordGapCenter - 262014 = fullRecordGapValue02345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02345 (fullRecordGapValue02345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02345_not_prime : ¬(recordGapCenter - 262014).Prime := by
  rw [fullRecordGapTerm02345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02345_fast_pow_mod_ne_one

def fullRecordGapValue02346 : Nat := fullRecordGapCenterValue - 261954

theorem fullRecordGapTerm02346_eq_value :
    recordGapCenter - 261954 = fullRecordGapValue02346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02346 (fullRecordGapValue02346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02346_not_prime : ¬(recordGapCenter - 261954).Prime := by
  rw [fullRecordGapTerm02346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02346_fast_pow_mod_ne_one

def fullRecordGapValue02347 : Nat := fullRecordGapCenterValue - 261798

theorem fullRecordGapTerm02347_eq_value :
    recordGapCenter - 261798 = fullRecordGapValue02347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02347 (fullRecordGapValue02347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02347_not_prime : ¬(recordGapCenter - 261798).Prime := by
  rw [fullRecordGapTerm02347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02347_fast_pow_mod_ne_one

def fullRecordGapValue02348 : Nat := fullRecordGapCenterValue - 261762

theorem fullRecordGapTerm02348_eq_value :
    recordGapCenter - 261762 = fullRecordGapValue02348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02348 (fullRecordGapValue02348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02348_not_prime : ¬(recordGapCenter - 261762).Prime := by
  rw [fullRecordGapTerm02348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02348_fast_pow_mod_ne_one

def fullRecordGapValue02349 : Nat := fullRecordGapCenterValue - 261748

theorem fullRecordGapTerm02349_eq_value :
    recordGapCenter - 261748 = fullRecordGapValue02349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02349 (fullRecordGapValue02349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02349_not_prime : ¬(recordGapCenter - 261748).Prime := by
  rw [fullRecordGapTerm02349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02349_fast_pow_mod_ne_one

def fullRecordGapValue02350 : Nat := fullRecordGapCenterValue - 261634

theorem fullRecordGapTerm02350_eq_value :
    recordGapCenter - 261634 = fullRecordGapValue02350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02350 (fullRecordGapValue02350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02350_not_prime : ¬(recordGapCenter - 261634).Prime := by
  rw [fullRecordGapTerm02350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02350_fast_pow_mod_ne_one

def fullRecordGapValue02351 : Nat := fullRecordGapCenterValue - 261622

theorem fullRecordGapTerm02351_eq_value :
    recordGapCenter - 261622 = fullRecordGapValue02351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02351 (fullRecordGapValue02351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02351_not_prime : ¬(recordGapCenter - 261622).Prime := by
  rw [fullRecordGapTerm02351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02351_fast_pow_mod_ne_one

def fullRecordGapValue02352 : Nat := fullRecordGapCenterValue - 261582

theorem fullRecordGapTerm02352_eq_value :
    recordGapCenter - 261582 = fullRecordGapValue02352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02352 (fullRecordGapValue02352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02352_not_prime : ¬(recordGapCenter - 261582).Prime := by
  rw [fullRecordGapTerm02352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02352_fast_pow_mod_ne_one

def fullRecordGapValue02353 : Nat := fullRecordGapCenterValue - 261574

theorem fullRecordGapTerm02353_eq_value :
    recordGapCenter - 261574 = fullRecordGapValue02353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02353 (fullRecordGapValue02353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02353_not_prime : ¬(recordGapCenter - 261574).Prime := by
  rw [fullRecordGapTerm02353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02353_fast_pow_mod_ne_one

def fullRecordGapValue02354 : Nat := fullRecordGapCenterValue - 261462

theorem fullRecordGapTerm02354_eq_value :
    recordGapCenter - 261462 = fullRecordGapValue02354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02354 (fullRecordGapValue02354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02354_not_prime : ¬(recordGapCenter - 261462).Prime := by
  rw [fullRecordGapTerm02354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02354_fast_pow_mod_ne_one

def fullRecordGapValue02355 : Nat := fullRecordGapCenterValue - 261412

theorem fullRecordGapTerm02355_eq_value :
    recordGapCenter - 261412 = fullRecordGapValue02355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02355 (fullRecordGapValue02355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02355_not_prime : ¬(recordGapCenter - 261412).Prime := by
  rw [fullRecordGapTerm02355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02355_fast_pow_mod_ne_one

def fullRecordGapValue02356 : Nat := fullRecordGapCenterValue - 261292

theorem fullRecordGapTerm02356_eq_value :
    recordGapCenter - 261292 = fullRecordGapValue02356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02356 (fullRecordGapValue02356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02356_not_prime : ¬(recordGapCenter - 261292).Prime := by
  rw [fullRecordGapTerm02356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02356_fast_pow_mod_ne_one

def fullRecordGapValue02357 : Nat := fullRecordGapCenterValue - 261238

theorem fullRecordGapTerm02357_eq_value :
    recordGapCenter - 261238 = fullRecordGapValue02357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02357 (fullRecordGapValue02357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02357_not_prime : ¬(recordGapCenter - 261238).Prime := by
  rw [fullRecordGapTerm02357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02357_fast_pow_mod_ne_one

def fullRecordGapValue02358 : Nat := fullRecordGapCenterValue - 261028

theorem fullRecordGapTerm02358_eq_value :
    recordGapCenter - 261028 = fullRecordGapValue02358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02358 (fullRecordGapValue02358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02358_not_prime : ¬(recordGapCenter - 261028).Prime := by
  rw [fullRecordGapTerm02358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02358_fast_pow_mod_ne_one

def fullRecordGapValue02359 : Nat := fullRecordGapCenterValue - 260922

theorem fullRecordGapTerm02359_eq_value :
    recordGapCenter - 260922 = fullRecordGapValue02359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02359 (fullRecordGapValue02359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02359_not_prime : ¬(recordGapCenter - 260922).Prime := by
  rw [fullRecordGapTerm02359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02359_fast_pow_mod_ne_one

def fullRecordGapValue02360 : Nat := fullRecordGapCenterValue - 260878

theorem fullRecordGapTerm02360_eq_value :
    recordGapCenter - 260878 = fullRecordGapValue02360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02360 (fullRecordGapValue02360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02360_not_prime : ¬(recordGapCenter - 260878).Prime := by
  rw [fullRecordGapTerm02360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02360_fast_pow_mod_ne_one

def fullRecordGapValue02361 : Nat := fullRecordGapCenterValue - 260818

theorem fullRecordGapTerm02361_eq_value :
    recordGapCenter - 260818 = fullRecordGapValue02361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02361 (fullRecordGapValue02361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02361_not_prime : ¬(recordGapCenter - 260818).Prime := by
  rw [fullRecordGapTerm02361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02361_fast_pow_mod_ne_one

def fullRecordGapValue02362 : Nat := fullRecordGapCenterValue - 260812

theorem fullRecordGapTerm02362_eq_value :
    recordGapCenter - 260812 = fullRecordGapValue02362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02362 (fullRecordGapValue02362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02362_not_prime : ¬(recordGapCenter - 260812).Prime := by
  rw [fullRecordGapTerm02362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02362_fast_pow_mod_ne_one

def fullRecordGapValue02363 : Nat := fullRecordGapCenterValue - 260742

theorem fullRecordGapTerm02363_eq_value :
    recordGapCenter - 260742 = fullRecordGapValue02363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02363 (fullRecordGapValue02363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02363_not_prime : ¬(recordGapCenter - 260742).Prime := by
  rw [fullRecordGapTerm02363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02363_fast_pow_mod_ne_one

def fullRecordGapValue02364 : Nat := fullRecordGapCenterValue - 260614

theorem fullRecordGapTerm02364_eq_value :
    recordGapCenter - 260614 = fullRecordGapValue02364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02364 (fullRecordGapValue02364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02364_not_prime : ¬(recordGapCenter - 260614).Prime := by
  rw [fullRecordGapTerm02364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02364_fast_pow_mod_ne_one

def fullRecordGapValue02365 : Nat := fullRecordGapCenterValue - 260518

theorem fullRecordGapTerm02365_eq_value :
    recordGapCenter - 260518 = fullRecordGapValue02365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02365 (fullRecordGapValue02365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02365_not_prime : ¬(recordGapCenter - 260518).Prime := by
  rw [fullRecordGapTerm02365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02365_fast_pow_mod_ne_one

def fullRecordGapValue02366 : Nat := fullRecordGapCenterValue - 260404

theorem fullRecordGapTerm02366_eq_value :
    recordGapCenter - 260404 = fullRecordGapValue02366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02366 (fullRecordGapValue02366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02366_not_prime : ¬(recordGapCenter - 260404).Prime := by
  rw [fullRecordGapTerm02366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02366_fast_pow_mod_ne_one

def fullRecordGapValue02367 : Nat := fullRecordGapCenterValue - 260398

theorem fullRecordGapTerm02367_eq_value :
    recordGapCenter - 260398 = fullRecordGapValue02367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02367 (fullRecordGapValue02367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02367_not_prime : ¬(recordGapCenter - 260398).Prime := by
  rw [fullRecordGapTerm02367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02367_fast_pow_mod_ne_one

def fullRecordGapValue02368 : Nat := fullRecordGapCenterValue - 260382

theorem fullRecordGapTerm02368_eq_value :
    recordGapCenter - 260382 = fullRecordGapValue02368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02368 (fullRecordGapValue02368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02368_not_prime : ¬(recordGapCenter - 260382).Prime := by
  rw [fullRecordGapTerm02368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02368_fast_pow_mod_ne_one

def fullRecordGapValue02369 : Nat := fullRecordGapCenterValue - 259878

theorem fullRecordGapTerm02369_eq_value :
    recordGapCenter - 259878 = fullRecordGapValue02369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02369 (fullRecordGapValue02369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02369_not_prime : ¬(recordGapCenter - 259878).Prime := by
  rw [fullRecordGapTerm02369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02369_fast_pow_mod_ne_one

def fullRecordGapValue02370 : Nat := fullRecordGapCenterValue - 259804

theorem fullRecordGapTerm02370_eq_value :
    recordGapCenter - 259804 = fullRecordGapValue02370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02370 (fullRecordGapValue02370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02370_not_prime : ¬(recordGapCenter - 259804).Prime := by
  rw [fullRecordGapTerm02370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02370_fast_pow_mod_ne_one

def fullRecordGapValue02371 : Nat := fullRecordGapCenterValue - 259564

theorem fullRecordGapTerm02371_eq_value :
    recordGapCenter - 259564 = fullRecordGapValue02371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02371 (fullRecordGapValue02371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02371_not_prime : ¬(recordGapCenter - 259564).Prime := by
  rw [fullRecordGapTerm02371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02371_fast_pow_mod_ne_one

def fullRecordGapValue02372 : Nat := fullRecordGapCenterValue - 259342

theorem fullRecordGapTerm02372_eq_value :
    recordGapCenter - 259342 = fullRecordGapValue02372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02372 (fullRecordGapValue02372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02372_not_prime : ¬(recordGapCenter - 259342).Prime := by
  rw [fullRecordGapTerm02372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02372_fast_pow_mod_ne_one

def fullRecordGapValue02373 : Nat := fullRecordGapCenterValue - 259338

theorem fullRecordGapTerm02373_eq_value :
    recordGapCenter - 259338 = fullRecordGapValue02373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02373 (fullRecordGapValue02373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02373_not_prime : ¬(recordGapCenter - 259338).Prime := by
  rw [fullRecordGapTerm02373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02373_fast_pow_mod_ne_one

def fullRecordGapValue02374 : Nat := fullRecordGapCenterValue - 259308

theorem fullRecordGapTerm02374_eq_value :
    recordGapCenter - 259308 = fullRecordGapValue02374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02374 (fullRecordGapValue02374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02374_not_prime : ¬(recordGapCenter - 259308).Prime := by
  rw [fullRecordGapTerm02374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02374_fast_pow_mod_ne_one

def fullRecordGapValue02375 : Nat := fullRecordGapCenterValue - 259282

theorem fullRecordGapTerm02375_eq_value :
    recordGapCenter - 259282 = fullRecordGapValue02375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02375 (fullRecordGapValue02375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02375_not_prime : ¬(recordGapCenter - 259282).Prime := by
  rw [fullRecordGapTerm02375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02375_fast_pow_mod_ne_one

def fullRecordGapValue02376 : Nat := fullRecordGapCenterValue - 259132

theorem fullRecordGapTerm02376_eq_value :
    recordGapCenter - 259132 = fullRecordGapValue02376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02376 (fullRecordGapValue02376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02376_not_prime : ¬(recordGapCenter - 259132).Prime := by
  rw [fullRecordGapTerm02376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02376_fast_pow_mod_ne_one

def fullRecordGapValue02377 : Nat := fullRecordGapCenterValue - 259062

theorem fullRecordGapTerm02377_eq_value :
    recordGapCenter - 259062 = fullRecordGapValue02377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02377 (fullRecordGapValue02377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02377_not_prime : ¬(recordGapCenter - 259062).Prime := by
  rw [fullRecordGapTerm02377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02377_fast_pow_mod_ne_one

def fullRecordGapValue02378 : Nat := fullRecordGapCenterValue - 259018

theorem fullRecordGapTerm02378_eq_value :
    recordGapCenter - 259018 = fullRecordGapValue02378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02378 (fullRecordGapValue02378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02378_not_prime : ¬(recordGapCenter - 259018).Prime := by
  rw [fullRecordGapTerm02378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02378_fast_pow_mod_ne_one

def fullRecordGapValue02379 : Nat := fullRecordGapCenterValue - 258954

theorem fullRecordGapTerm02379_eq_value :
    recordGapCenter - 258954 = fullRecordGapValue02379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02379 (fullRecordGapValue02379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02379_not_prime : ¬(recordGapCenter - 258954).Prime := by
  rw [fullRecordGapTerm02379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02379_fast_pow_mod_ne_one

def fullRecordGapValue02380 : Nat := fullRecordGapCenterValue - 258898

theorem fullRecordGapTerm02380_eq_value :
    recordGapCenter - 258898 = fullRecordGapValue02380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02380 (fullRecordGapValue02380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02380_not_prime : ¬(recordGapCenter - 258898).Prime := by
  rw [fullRecordGapTerm02380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02380_fast_pow_mod_ne_one

def fullRecordGapValue02381 : Nat := fullRecordGapCenterValue - 258720

theorem fullRecordGapTerm02381_eq_value :
    recordGapCenter - 258720 = fullRecordGapValue02381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02381 (fullRecordGapValue02381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02381_not_prime : ¬(recordGapCenter - 258720).Prime := by
  rw [fullRecordGapTerm02381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02381_fast_pow_mod_ne_one

def fullRecordGapValue02382 : Nat := fullRecordGapCenterValue - 258694

theorem fullRecordGapTerm02382_eq_value :
    recordGapCenter - 258694 = fullRecordGapValue02382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02382 (fullRecordGapValue02382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02382_not_prime : ¬(recordGapCenter - 258694).Prime := by
  rw [fullRecordGapTerm02382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02382_fast_pow_mod_ne_one

def fullRecordGapValue02383 : Nat := fullRecordGapCenterValue - 258484

theorem fullRecordGapTerm02383_eq_value :
    recordGapCenter - 258484 = fullRecordGapValue02383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02383 (fullRecordGapValue02383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02383_not_prime : ¬(recordGapCenter - 258484).Prime := by
  rw [fullRecordGapTerm02383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02383_fast_pow_mod_ne_one

def fullRecordGapValue02384 : Nat := fullRecordGapCenterValue - 258418

theorem fullRecordGapTerm02384_eq_value :
    recordGapCenter - 258418 = fullRecordGapValue02384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02384 (fullRecordGapValue02384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02384_not_prime : ¬(recordGapCenter - 258418).Prime := by
  rw [fullRecordGapTerm02384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02384_fast_pow_mod_ne_one

def fullRecordGapValue02385 : Nat := fullRecordGapCenterValue - 258178

theorem fullRecordGapTerm02385_eq_value :
    recordGapCenter - 258178 = fullRecordGapValue02385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02385 (fullRecordGapValue02385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02385_not_prime : ¬(recordGapCenter - 258178).Prime := by
  rw [fullRecordGapTerm02385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02385_fast_pow_mod_ne_one

def fullRecordGapValue02386 : Nat := fullRecordGapCenterValue - 258022

theorem fullRecordGapTerm02386_eq_value :
    recordGapCenter - 258022 = fullRecordGapValue02386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02386 (fullRecordGapValue02386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02386_not_prime : ¬(recordGapCenter - 258022).Prime := by
  rw [fullRecordGapTerm02386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02386_fast_pow_mod_ne_one

def fullRecordGapValue02387 : Nat := fullRecordGapCenterValue - 257962

theorem fullRecordGapTerm02387_eq_value :
    recordGapCenter - 257962 = fullRecordGapValue02387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02387 (fullRecordGapValue02387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02387_not_prime : ¬(recordGapCenter - 257962).Prime := by
  rw [fullRecordGapTerm02387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02387_fast_pow_mod_ne_one

def fullRecordGapValue02388 : Nat := fullRecordGapCenterValue - 257878

theorem fullRecordGapTerm02388_eq_value :
    recordGapCenter - 257878 = fullRecordGapValue02388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02388 (fullRecordGapValue02388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02388_not_prime : ¬(recordGapCenter - 257878).Prime := by
  rw [fullRecordGapTerm02388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02388_fast_pow_mod_ne_one

def fullRecordGapValue02389 : Nat := fullRecordGapCenterValue - 257674

theorem fullRecordGapTerm02389_eq_value :
    recordGapCenter - 257674 = fullRecordGapValue02389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02389 (fullRecordGapValue02389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02389_not_prime : ¬(recordGapCenter - 257674).Prime := by
  rw [fullRecordGapTerm02389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02389_fast_pow_mod_ne_one

def fullRecordGapValue02390 : Nat := fullRecordGapCenterValue - 257662

theorem fullRecordGapTerm02390_eq_value :
    recordGapCenter - 257662 = fullRecordGapValue02390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02390 (fullRecordGapValue02390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02390_not_prime : ¬(recordGapCenter - 257662).Prime := by
  rw [fullRecordGapTerm02390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02390_fast_pow_mod_ne_one

def fullRecordGapValue02391 : Nat := fullRecordGapCenterValue - 257638

theorem fullRecordGapTerm02391_eq_value :
    recordGapCenter - 257638 = fullRecordGapValue02391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02391 (fullRecordGapValue02391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02391_not_prime : ¬(recordGapCenter - 257638).Prime := by
  rw [fullRecordGapTerm02391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02391_fast_pow_mod_ne_one

def fullRecordGapValue02392 : Nat := fullRecordGapCenterValue - 257434

theorem fullRecordGapTerm02392_eq_value :
    recordGapCenter - 257434 = fullRecordGapValue02392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02392 (fullRecordGapValue02392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02392_not_prime : ¬(recordGapCenter - 257434).Prime := by
  rw [fullRecordGapTerm02392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02392_fast_pow_mod_ne_one

def fullRecordGapValue02393 : Nat := fullRecordGapCenterValue - 257332

theorem fullRecordGapTerm02393_eq_value :
    recordGapCenter - 257332 = fullRecordGapValue02393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02393 (fullRecordGapValue02393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02393_not_prime : ¬(recordGapCenter - 257332).Prime := by
  rw [fullRecordGapTerm02393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02393_fast_pow_mod_ne_one

def fullRecordGapValue02394 : Nat := fullRecordGapCenterValue - 257308

theorem fullRecordGapTerm02394_eq_value :
    recordGapCenter - 257308 = fullRecordGapValue02394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02394 (fullRecordGapValue02394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02394_not_prime : ¬(recordGapCenter - 257308).Prime := by
  rw [fullRecordGapTerm02394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02394_fast_pow_mod_ne_one

def fullRecordGapValue02395 : Nat := fullRecordGapCenterValue - 257098

theorem fullRecordGapTerm02395_eq_value :
    recordGapCenter - 257098 = fullRecordGapValue02395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02395 (fullRecordGapValue02395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02395_not_prime : ¬(recordGapCenter - 257098).Prime := by
  rw [fullRecordGapTerm02395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02395_fast_pow_mod_ne_one

def fullRecordGapValue02396 : Nat := fullRecordGapCenterValue - 257038

theorem fullRecordGapTerm02396_eq_value :
    recordGapCenter - 257038 = fullRecordGapValue02396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02396 (fullRecordGapValue02396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02396_not_prime : ¬(recordGapCenter - 257038).Prime := by
  rw [fullRecordGapTerm02396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02396_fast_pow_mod_ne_one

def fullRecordGapValue02397 : Nat := fullRecordGapCenterValue - 256948

theorem fullRecordGapTerm02397_eq_value :
    recordGapCenter - 256948 = fullRecordGapValue02397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02397 (fullRecordGapValue02397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02397_not_prime : ¬(recordGapCenter - 256948).Prime := by
  rw [fullRecordGapTerm02397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02397_fast_pow_mod_ne_one

def fullRecordGapValue02398 : Nat := fullRecordGapCenterValue - 256822

theorem fullRecordGapTerm02398_eq_value :
    recordGapCenter - 256822 = fullRecordGapValue02398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02398 (fullRecordGapValue02398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02398_not_prime : ¬(recordGapCenter - 256822).Prime := by
  rw [fullRecordGapTerm02398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02398_fast_pow_mod_ne_one

def fullRecordGapValue02399 : Nat := fullRecordGapCenterValue - 256798

theorem fullRecordGapTerm02399_eq_value :
    recordGapCenter - 256798 = fullRecordGapValue02399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02399 (fullRecordGapValue02399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02399_not_prime : ¬(recordGapCenter - 256798).Prime := by
  rw [fullRecordGapTerm02399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02399_fast_pow_mod_ne_one

def fullRecordGapValue02400 : Nat := fullRecordGapCenterValue - 256702

theorem fullRecordGapTerm02400_eq_value :
    recordGapCenter - 256702 = fullRecordGapValue02400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02400 (fullRecordGapValue02400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02400_not_prime : ¬(recordGapCenter - 256702).Prime := by
  rw [fullRecordGapTerm02400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02400_fast_pow_mod_ne_one

def fullRecordGapValue02401 : Nat := fullRecordGapCenterValue - 256608

theorem fullRecordGapTerm02401_eq_value :
    recordGapCenter - 256608 = fullRecordGapValue02401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02401 (fullRecordGapValue02401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02401_not_prime : ¬(recordGapCenter - 256608).Prime := by
  rw [fullRecordGapTerm02401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02401_fast_pow_mod_ne_one

def fullRecordGapValue02402 : Nat := fullRecordGapCenterValue - 256324

theorem fullRecordGapTerm02402_eq_value :
    recordGapCenter - 256324 = fullRecordGapValue02402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02402 (fullRecordGapValue02402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02402_not_prime : ¬(recordGapCenter - 256324).Prime := by
  rw [fullRecordGapTerm02402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02402_fast_pow_mod_ne_one

def fullRecordGapValue02403 : Nat := fullRecordGapCenterValue - 256252

theorem fullRecordGapTerm02403_eq_value :
    recordGapCenter - 256252 = fullRecordGapValue02403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02403 (fullRecordGapValue02403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02403_not_prime : ¬(recordGapCenter - 256252).Prime := by
  rw [fullRecordGapTerm02403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02403_fast_pow_mod_ne_one

def fullRecordGapValue02404 : Nat := fullRecordGapCenterValue - 256198

theorem fullRecordGapTerm02404_eq_value :
    recordGapCenter - 256198 = fullRecordGapValue02404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02404 (fullRecordGapValue02404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02404_not_prime : ¬(recordGapCenter - 256198).Prime := by
  rw [fullRecordGapTerm02404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02404_fast_pow_mod_ne_one

def fullRecordGapValue02405 : Nat := fullRecordGapCenterValue - 256132

theorem fullRecordGapTerm02405_eq_value :
    recordGapCenter - 256132 = fullRecordGapValue02405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02405 (fullRecordGapValue02405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02405_not_prime : ¬(recordGapCenter - 256132).Prime := by
  rw [fullRecordGapTerm02405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02405_fast_pow_mod_ne_one

def fullRecordGapValue02406 : Nat := fullRecordGapCenterValue - 255988

theorem fullRecordGapTerm02406_eq_value :
    recordGapCenter - 255988 = fullRecordGapValue02406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02406 (fullRecordGapValue02406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02406_not_prime : ¬(recordGapCenter - 255988).Prime := by
  rw [fullRecordGapTerm02406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02406_fast_pow_mod_ne_one

def fullRecordGapValue02407 : Nat := fullRecordGapCenterValue - 255862

theorem fullRecordGapTerm02407_eq_value :
    recordGapCenter - 255862 = fullRecordGapValue02407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02407 (fullRecordGapValue02407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02407_not_prime : ¬(recordGapCenter - 255862).Prime := by
  rw [fullRecordGapTerm02407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02407_fast_pow_mod_ne_one

def fullRecordGapValue02408 : Nat := fullRecordGapCenterValue - 255628

theorem fullRecordGapTerm02408_eq_value :
    recordGapCenter - 255628 = fullRecordGapValue02408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02408 (fullRecordGapValue02408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02408_not_prime : ¬(recordGapCenter - 255628).Prime := by
  rw [fullRecordGapTerm02408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02408_fast_pow_mod_ne_one

def fullRecordGapValue02409 : Nat := fullRecordGapCenterValue - 255552

theorem fullRecordGapTerm02409_eq_value :
    recordGapCenter - 255552 = fullRecordGapValue02409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02409 (fullRecordGapValue02409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02409_not_prime : ¬(recordGapCenter - 255552).Prime := by
  rw [fullRecordGapTerm02409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02409_fast_pow_mod_ne_one

def fullRecordGapValue02410 : Nat := fullRecordGapCenterValue - 255412

theorem fullRecordGapTerm02410_eq_value :
    recordGapCenter - 255412 = fullRecordGapValue02410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02410 (fullRecordGapValue02410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02410_not_prime : ¬(recordGapCenter - 255412).Prime := by
  rw [fullRecordGapTerm02410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02410_fast_pow_mod_ne_one

def fullRecordGapValue02411 : Nat := fullRecordGapCenterValue - 254578

theorem fullRecordGapTerm02411_eq_value :
    recordGapCenter - 254578 = fullRecordGapValue02411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02411 (fullRecordGapValue02411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02411_not_prime : ¬(recordGapCenter - 254578).Prime := by
  rw [fullRecordGapTerm02411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02411_fast_pow_mod_ne_one

def fullRecordGapValue02412 : Nat := fullRecordGapCenterValue - 254482

theorem fullRecordGapTerm02412_eq_value :
    recordGapCenter - 254482 = fullRecordGapValue02412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02412 (fullRecordGapValue02412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02412_not_prime : ¬(recordGapCenter - 254482).Prime := by
  rw [fullRecordGapTerm02412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02412_fast_pow_mod_ne_one

def fullRecordGapValue02413 : Nat := fullRecordGapCenterValue - 254404

theorem fullRecordGapTerm02413_eq_value :
    recordGapCenter - 254404 = fullRecordGapValue02413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02413 (fullRecordGapValue02413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02413_not_prime : ¬(recordGapCenter - 254404).Prime := by
  rw [fullRecordGapTerm02413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02413_fast_pow_mod_ne_one

def fullRecordGapValue02414 : Nat := fullRecordGapCenterValue - 254314

theorem fullRecordGapTerm02414_eq_value :
    recordGapCenter - 254314 = fullRecordGapValue02414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02414 (fullRecordGapValue02414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02414_not_prime : ¬(recordGapCenter - 254314).Prime := by
  rw [fullRecordGapTerm02414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02414_fast_pow_mod_ne_one

def fullRecordGapValue02415 : Nat := fullRecordGapCenterValue - 254278

theorem fullRecordGapTerm02415_eq_value :
    recordGapCenter - 254278 = fullRecordGapValue02415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02415 (fullRecordGapValue02415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02415_not_prime : ¬(recordGapCenter - 254278).Prime := by
  rw [fullRecordGapTerm02415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02415_fast_pow_mod_ne_one

def fullRecordGapValue02416 : Nat := fullRecordGapCenterValue - 254074

theorem fullRecordGapTerm02416_eq_value :
    recordGapCenter - 254074 = fullRecordGapValue02416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02416 (fullRecordGapValue02416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02416_not_prime : ¬(recordGapCenter - 254074).Prime := by
  rw [fullRecordGapTerm02416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02416_fast_pow_mod_ne_one

def fullRecordGapValue02417 : Nat := fullRecordGapCenterValue - 254062

theorem fullRecordGapTerm02417_eq_value :
    recordGapCenter - 254062 = fullRecordGapValue02417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02417 (fullRecordGapValue02417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02417_not_prime : ¬(recordGapCenter - 254062).Prime := by
  rw [fullRecordGapTerm02417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02417_fast_pow_mod_ne_one

def fullRecordGapValue02418 : Nat := fullRecordGapCenterValue - 253852

theorem fullRecordGapTerm02418_eq_value :
    recordGapCenter - 253852 = fullRecordGapValue02418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02418 (fullRecordGapValue02418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02418_not_prime : ¬(recordGapCenter - 253852).Prime := by
  rw [fullRecordGapTerm02418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02418_fast_pow_mod_ne_one

def fullRecordGapValue02419 : Nat := fullRecordGapCenterValue - 253714

theorem fullRecordGapTerm02419_eq_value :
    recordGapCenter - 253714 = fullRecordGapValue02419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02419 (fullRecordGapValue02419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02419_not_prime : ¬(recordGapCenter - 253714).Prime := by
  rw [fullRecordGapTerm02419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02419_fast_pow_mod_ne_one

def fullRecordGapValue02420 : Nat := fullRecordGapCenterValue - 253684

theorem fullRecordGapTerm02420_eq_value :
    recordGapCenter - 253684 = fullRecordGapValue02420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02420 (fullRecordGapValue02420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02420_not_prime : ¬(recordGapCenter - 253684).Prime := by
  rw [fullRecordGapTerm02420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02420_fast_pow_mod_ne_one

def fullRecordGapValue02421 : Nat := fullRecordGapCenterValue - 253678

theorem fullRecordGapTerm02421_eq_value :
    recordGapCenter - 253678 = fullRecordGapValue02421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02421 (fullRecordGapValue02421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02421_not_prime : ¬(recordGapCenter - 253678).Prime := by
  rw [fullRecordGapTerm02421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02421_fast_pow_mod_ne_one

def fullRecordGapValue02422 : Nat := fullRecordGapCenterValue - 253654

theorem fullRecordGapTerm02422_eq_value :
    recordGapCenter - 253654 = fullRecordGapValue02422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02422 (fullRecordGapValue02422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02422_not_prime : ¬(recordGapCenter - 253654).Prime := by
  rw [fullRecordGapTerm02422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02422_fast_pow_mod_ne_one

def fullRecordGapValue02423 : Nat := fullRecordGapCenterValue - 253564

theorem fullRecordGapTerm02423_eq_value :
    recordGapCenter - 253564 = fullRecordGapValue02423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02423 (fullRecordGapValue02423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02423_not_prime : ¬(recordGapCenter - 253564).Prime := by
  rw [fullRecordGapTerm02423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02423_fast_pow_mod_ne_one

def fullRecordGapValue02424 : Nat := fullRecordGapCenterValue - 253468

theorem fullRecordGapTerm02424_eq_value :
    recordGapCenter - 253468 = fullRecordGapValue02424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02424 (fullRecordGapValue02424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02424_not_prime : ¬(recordGapCenter - 253468).Prime := by
  rw [fullRecordGapTerm02424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02424_fast_pow_mod_ne_one

def fullRecordGapValue02425 : Nat := fullRecordGapCenterValue - 253440

theorem fullRecordGapTerm02425_eq_value :
    recordGapCenter - 253440 = fullRecordGapValue02425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02425 (fullRecordGapValue02425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02425_not_prime : ¬(recordGapCenter - 253440).Prime := by
  rw [fullRecordGapTerm02425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02425_fast_pow_mod_ne_one

def fullRecordGapValue02426 : Nat := fullRecordGapCenterValue - 253348

theorem fullRecordGapTerm02426_eq_value :
    recordGapCenter - 253348 = fullRecordGapValue02426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02426 (fullRecordGapValue02426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02426_not_prime : ¬(recordGapCenter - 253348).Prime := by
  rw [fullRecordGapTerm02426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02426_fast_pow_mod_ne_one

def fullRecordGapValue02427 : Nat := fullRecordGapCenterValue - 253252

theorem fullRecordGapTerm02427_eq_value :
    recordGapCenter - 253252 = fullRecordGapValue02427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02427 (fullRecordGapValue02427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02427_not_prime : ¬(recordGapCenter - 253252).Prime := by
  rw [fullRecordGapTerm02427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02427_fast_pow_mod_ne_one

def fullRecordGapValue02428 : Nat := fullRecordGapCenterValue - 253222

theorem fullRecordGapTerm02428_eq_value :
    recordGapCenter - 253222 = fullRecordGapValue02428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02428 (fullRecordGapValue02428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02428_not_prime : ¬(recordGapCenter - 253222).Prime := by
  rw [fullRecordGapTerm02428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02428_fast_pow_mod_ne_one

def fullRecordGapValue02429 : Nat := fullRecordGapCenterValue - 252622

theorem fullRecordGapTerm02429_eq_value :
    recordGapCenter - 252622 = fullRecordGapValue02429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02429 (fullRecordGapValue02429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02429_not_prime : ¬(recordGapCenter - 252622).Prime := by
  rw [fullRecordGapTerm02429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02429_fast_pow_mod_ne_one

def fullRecordGapValue02430 : Nat := fullRecordGapCenterValue - 252514

theorem fullRecordGapTerm02430_eq_value :
    recordGapCenter - 252514 = fullRecordGapValue02430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02430 (fullRecordGapValue02430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02430_not_prime : ¬(recordGapCenter - 252514).Prime := by
  rw [fullRecordGapTerm02430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02430_fast_pow_mod_ne_one

def fullRecordGapValue02431 : Nat := fullRecordGapCenterValue - 252508

theorem fullRecordGapTerm02431_eq_value :
    recordGapCenter - 252508 = fullRecordGapValue02431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02431 (fullRecordGapValue02431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02431_not_prime : ¬(recordGapCenter - 252508).Prime := by
  rw [fullRecordGapTerm02431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02431_fast_pow_mod_ne_one

def fullRecordGapValue02432 : Nat := fullRecordGapCenterValue - 252412

theorem fullRecordGapTerm02432_eq_value :
    recordGapCenter - 252412 = fullRecordGapValue02432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02432 (fullRecordGapValue02432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02432_not_prime : ¬(recordGapCenter - 252412).Prime := by
  rw [fullRecordGapTerm02432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02432_fast_pow_mod_ne_one

def fullRecordGapValue02433 : Nat := fullRecordGapCenterValue - 252262

theorem fullRecordGapTerm02433_eq_value :
    recordGapCenter - 252262 = fullRecordGapValue02433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02433 (fullRecordGapValue02433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02433_not_prime : ¬(recordGapCenter - 252262).Prime := by
  rw [fullRecordGapTerm02433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02433_fast_pow_mod_ne_one

def fullRecordGapValue02434 : Nat := fullRecordGapCenterValue - 252082

theorem fullRecordGapTerm02434_eq_value :
    recordGapCenter - 252082 = fullRecordGapValue02434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02434 (fullRecordGapValue02434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02434_not_prime : ¬(recordGapCenter - 252082).Prime := by
  rw [fullRecordGapTerm02434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02434_fast_pow_mod_ne_one

def fullRecordGapValue02435 : Nat := fullRecordGapCenterValue - 252000

theorem fullRecordGapTerm02435_eq_value :
    recordGapCenter - 252000 = fullRecordGapValue02435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02435 (fullRecordGapValue02435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02435_not_prime : ¬(recordGapCenter - 252000).Prime := by
  rw [fullRecordGapTerm02435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02435_fast_pow_mod_ne_one

def fullRecordGapValue02436 : Nat := fullRecordGapCenterValue - 251422

theorem fullRecordGapTerm02436_eq_value :
    recordGapCenter - 251422 = fullRecordGapValue02436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02436 (fullRecordGapValue02436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02436_not_prime : ¬(recordGapCenter - 251422).Prime := by
  rw [fullRecordGapTerm02436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02436_fast_pow_mod_ne_one

def fullRecordGapValue02437 : Nat := fullRecordGapCenterValue - 251374

theorem fullRecordGapTerm02437_eq_value :
    recordGapCenter - 251374 = fullRecordGapValue02437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02437 (fullRecordGapValue02437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02437_not_prime : ¬(recordGapCenter - 251374).Prime := by
  rw [fullRecordGapTerm02437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02437_fast_pow_mod_ne_one

def fullRecordGapValue02438 : Nat := fullRecordGapCenterValue - 251242

theorem fullRecordGapTerm02438_eq_value :
    recordGapCenter - 251242 = fullRecordGapValue02438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02438 (fullRecordGapValue02438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02438_not_prime : ¬(recordGapCenter - 251242).Prime := by
  rw [fullRecordGapTerm02438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02438_fast_pow_mod_ne_one

def fullRecordGapValue02439 : Nat := fullRecordGapCenterValue - 251194

theorem fullRecordGapTerm02439_eq_value :
    recordGapCenter - 251194 = fullRecordGapValue02439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02439 (fullRecordGapValue02439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02439_not_prime : ¬(recordGapCenter - 251194).Prime := by
  rw [fullRecordGapTerm02439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02439_fast_pow_mod_ne_one

def fullRecordGapValue02440 : Nat := fullRecordGapCenterValue - 251164

theorem fullRecordGapTerm02440_eq_value :
    recordGapCenter - 251164 = fullRecordGapValue02440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02440 (fullRecordGapValue02440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02440_not_prime : ¬(recordGapCenter - 251164).Prime := by
  rw [fullRecordGapTerm02440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02440_fast_pow_mod_ne_one

def fullRecordGapValue02441 : Nat := fullRecordGapCenterValue - 251092

theorem fullRecordGapTerm02441_eq_value :
    recordGapCenter - 251092 = fullRecordGapValue02441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02441 (fullRecordGapValue02441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02441_not_prime : ¬(recordGapCenter - 251092).Prime := by
  rw [fullRecordGapTerm02441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02441_fast_pow_mod_ne_one

def fullRecordGapValue02442 : Nat := fullRecordGapCenterValue - 251044

theorem fullRecordGapTerm02442_eq_value :
    recordGapCenter - 251044 = fullRecordGapValue02442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02442 (fullRecordGapValue02442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02442_not_prime : ¬(recordGapCenter - 251044).Prime := by
  rw [fullRecordGapTerm02442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02442_fast_pow_mod_ne_one

def fullRecordGapValue02443 : Nat := fullRecordGapCenterValue - 250924

theorem fullRecordGapTerm02443_eq_value :
    recordGapCenter - 250924 = fullRecordGapValue02443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02443 (fullRecordGapValue02443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02443_not_prime : ¬(recordGapCenter - 250924).Prime := by
  rw [fullRecordGapTerm02443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02443_fast_pow_mod_ne_one

def fullRecordGapValue02444 : Nat := fullRecordGapCenterValue - 250882

theorem fullRecordGapTerm02444_eq_value :
    recordGapCenter - 250882 = fullRecordGapValue02444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02444 (fullRecordGapValue02444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02444_not_prime : ¬(recordGapCenter - 250882).Prime := by
  rw [fullRecordGapTerm02444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02444_fast_pow_mod_ne_one

def fullRecordGapValue02445 : Nat := fullRecordGapCenterValue - 250858

theorem fullRecordGapTerm02445_eq_value :
    recordGapCenter - 250858 = fullRecordGapValue02445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02445 (fullRecordGapValue02445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02445_not_prime : ¬(recordGapCenter - 250858).Prime := by
  rw [fullRecordGapTerm02445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02445_fast_pow_mod_ne_one

def fullRecordGapValue02446 : Nat := fullRecordGapCenterValue - 250798

theorem fullRecordGapTerm02446_eq_value :
    recordGapCenter - 250798 = fullRecordGapValue02446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02446 (fullRecordGapValue02446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02446_not_prime : ¬(recordGapCenter - 250798).Prime := by
  rw [fullRecordGapTerm02446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02446_fast_pow_mod_ne_one

def fullRecordGapValue02447 : Nat := fullRecordGapCenterValue - 250522

theorem fullRecordGapTerm02447_eq_value :
    recordGapCenter - 250522 = fullRecordGapValue02447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02447 (fullRecordGapValue02447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02447_not_prime : ¬(recordGapCenter - 250522).Prime := by
  rw [fullRecordGapTerm02447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02447_fast_pow_mod_ne_one

def fullRecordGapValue02448 : Nat := fullRecordGapCenterValue - 250462

theorem fullRecordGapTerm02448_eq_value :
    recordGapCenter - 250462 = fullRecordGapValue02448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02448 (fullRecordGapValue02448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02448_not_prime : ¬(recordGapCenter - 250462).Prime := by
  rw [fullRecordGapTerm02448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02448_fast_pow_mod_ne_one

def fullRecordGapValue02449 : Nat := fullRecordGapCenterValue - 250414

theorem fullRecordGapTerm02449_eq_value :
    recordGapCenter - 250414 = fullRecordGapValue02449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02449 (fullRecordGapValue02449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02449_not_prime : ¬(recordGapCenter - 250414).Prime := by
  rw [fullRecordGapTerm02449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02449_fast_pow_mod_ne_one

def fullRecordGapValue02450 : Nat := fullRecordGapCenterValue - 250402

theorem fullRecordGapTerm02450_eq_value :
    recordGapCenter - 250402 = fullRecordGapValue02450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02450 (fullRecordGapValue02450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02450_not_prime : ¬(recordGapCenter - 250402).Prime := by
  rw [fullRecordGapTerm02450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02450_fast_pow_mod_ne_one

def fullRecordGapValue02451 : Nat := fullRecordGapCenterValue - 250000

theorem fullRecordGapTerm02451_eq_value :
    recordGapCenter - 250000 = fullRecordGapValue02451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02451 (fullRecordGapValue02451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02451_not_prime : ¬(recordGapCenter - 250000).Prime := by
  rw [fullRecordGapTerm02451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02451_fast_pow_mod_ne_one

def fullRecordGapValue02452 : Nat := fullRecordGapCenterValue - 249988

theorem fullRecordGapTerm02452_eq_value :
    recordGapCenter - 249988 = fullRecordGapValue02452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02452 (fullRecordGapValue02452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02452_not_prime : ¬(recordGapCenter - 249988).Prime := by
  rw [fullRecordGapTerm02452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02452_fast_pow_mod_ne_one

def fullRecordGapValue02453 : Nat := fullRecordGapCenterValue - 249982

theorem fullRecordGapTerm02453_eq_value :
    recordGapCenter - 249982 = fullRecordGapValue02453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02453 (fullRecordGapValue02453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02453_not_prime : ¬(recordGapCenter - 249982).Prime := by
  rw [fullRecordGapTerm02453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02453_fast_pow_mod_ne_one

def fullRecordGapValue02454 : Nat := fullRecordGapCenterValue - 249598

theorem fullRecordGapTerm02454_eq_value :
    recordGapCenter - 249598 = fullRecordGapValue02454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02454 (fullRecordGapValue02454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02454_not_prime : ¬(recordGapCenter - 249598).Prime := by
  rw [fullRecordGapTerm02454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02454_fast_pow_mod_ne_one

def fullRecordGapValue02455 : Nat := fullRecordGapCenterValue - 249538

theorem fullRecordGapTerm02455_eq_value :
    recordGapCenter - 249538 = fullRecordGapValue02455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02455 (fullRecordGapValue02455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02455_not_prime : ¬(recordGapCenter - 249538).Prime := by
  rw [fullRecordGapTerm02455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02455_fast_pow_mod_ne_one

def fullRecordGapValue02456 : Nat := fullRecordGapCenterValue - 249532

theorem fullRecordGapTerm02456_eq_value :
    recordGapCenter - 249532 = fullRecordGapValue02456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02456 (fullRecordGapValue02456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02456_not_prime : ¬(recordGapCenter - 249532).Prime := by
  rw [fullRecordGapTerm02456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02456_fast_pow_mod_ne_one

def fullRecordGapValue02457 : Nat := fullRecordGapCenterValue - 249478

theorem fullRecordGapTerm02457_eq_value :
    recordGapCenter - 249478 = fullRecordGapValue02457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02457 (fullRecordGapValue02457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02457_not_prime : ¬(recordGapCenter - 249478).Prime := by
  rw [fullRecordGapTerm02457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02457_fast_pow_mod_ne_one

def fullRecordGapValue02458 : Nat := fullRecordGapCenterValue - 249388

theorem fullRecordGapTerm02458_eq_value :
    recordGapCenter - 249388 = fullRecordGapValue02458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02458 (fullRecordGapValue02458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02458_not_prime : ¬(recordGapCenter - 249388).Prime := by
  rw [fullRecordGapTerm02458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02458_fast_pow_mod_ne_one

def fullRecordGapValue02459 : Nat := fullRecordGapCenterValue - 248932

theorem fullRecordGapTerm02459_eq_value :
    recordGapCenter - 248932 = fullRecordGapValue02459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02459 (fullRecordGapValue02459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02459_not_prime : ¬(recordGapCenter - 248932).Prime := by
  rw [fullRecordGapTerm02459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02459_fast_pow_mod_ne_one

def fullRecordGapValue02460 : Nat := fullRecordGapCenterValue - 248764

theorem fullRecordGapTerm02460_eq_value :
    recordGapCenter - 248764 = fullRecordGapValue02460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02460 (fullRecordGapValue02460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02460_not_prime : ¬(recordGapCenter - 248764).Prime := by
  rw [fullRecordGapTerm02460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02460_fast_pow_mod_ne_one

def fullRecordGapValue02461 : Nat := fullRecordGapCenterValue - 248734

theorem fullRecordGapTerm02461_eq_value :
    recordGapCenter - 248734 = fullRecordGapValue02461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02461 (fullRecordGapValue02461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02461_not_prime : ¬(recordGapCenter - 248734).Prime := by
  rw [fullRecordGapTerm02461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02461_fast_pow_mod_ne_one

def fullRecordGapValue02462 : Nat := fullRecordGapCenterValue - 248674

theorem fullRecordGapTerm02462_eq_value :
    recordGapCenter - 248674 = fullRecordGapValue02462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02462 (fullRecordGapValue02462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02462_not_prime : ¬(recordGapCenter - 248674).Prime := by
  rw [fullRecordGapTerm02462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02462_fast_pow_mod_ne_one

def fullRecordGapValue02463 : Nat := fullRecordGapCenterValue - 248602

theorem fullRecordGapTerm02463_eq_value :
    recordGapCenter - 248602 = fullRecordGapValue02463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02463 (fullRecordGapValue02463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02463_not_prime : ¬(recordGapCenter - 248602).Prime := by
  rw [fullRecordGapTerm02463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02463_fast_pow_mod_ne_one

def fullRecordGapValue02464 : Nat := fullRecordGapCenterValue - 248554

theorem fullRecordGapTerm02464_eq_value :
    recordGapCenter - 248554 = fullRecordGapValue02464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02464 (fullRecordGapValue02464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02464_not_prime : ¬(recordGapCenter - 248554).Prime := by
  rw [fullRecordGapTerm02464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02464_fast_pow_mod_ne_one

def fullRecordGapValue02465 : Nat := fullRecordGapCenterValue - 248278

theorem fullRecordGapTerm02465_eq_value :
    recordGapCenter - 248278 = fullRecordGapValue02465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02465 (fullRecordGapValue02465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02465_not_prime : ¬(recordGapCenter - 248278).Prime := by
  rw [fullRecordGapTerm02465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02465_fast_pow_mod_ne_one

def fullRecordGapValue02466 : Nat := fullRecordGapCenterValue - 248194

theorem fullRecordGapTerm02466_eq_value :
    recordGapCenter - 248194 = fullRecordGapValue02466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02466 (fullRecordGapValue02466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02466_not_prime : ¬(recordGapCenter - 248194).Prime := by
  rw [fullRecordGapTerm02466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02466_fast_pow_mod_ne_one

def fullRecordGapValue02467 : Nat := fullRecordGapCenterValue - 248134

theorem fullRecordGapTerm02467_eq_value :
    recordGapCenter - 248134 = fullRecordGapValue02467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02467 (fullRecordGapValue02467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02467_not_prime : ¬(recordGapCenter - 248134).Prime := by
  rw [fullRecordGapTerm02467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02467_fast_pow_mod_ne_one

def fullRecordGapValue02468 : Nat := fullRecordGapCenterValue - 248068

theorem fullRecordGapTerm02468_eq_value :
    recordGapCenter - 248068 = fullRecordGapValue02468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02468 (fullRecordGapValue02468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02468_not_prime : ¬(recordGapCenter - 248068).Prime := by
  rw [fullRecordGapTerm02468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02468_fast_pow_mod_ne_one

def fullRecordGapValue02469 : Nat := fullRecordGapCenterValue - 248044

theorem fullRecordGapTerm02469_eq_value :
    recordGapCenter - 248044 = fullRecordGapValue02469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02469 (fullRecordGapValue02469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02469_not_prime : ¬(recordGapCenter - 248044).Prime := by
  rw [fullRecordGapTerm02469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02469_fast_pow_mod_ne_one

def fullRecordGapValue02470 : Nat := fullRecordGapCenterValue - 247774

theorem fullRecordGapTerm02470_eq_value :
    recordGapCenter - 247774 = fullRecordGapValue02470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02470 (fullRecordGapValue02470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02470_not_prime : ¬(recordGapCenter - 247774).Prime := by
  rw [fullRecordGapTerm02470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02470_fast_pow_mod_ne_one

def fullRecordGapValue02471 : Nat := fullRecordGapCenterValue - 247732

theorem fullRecordGapTerm02471_eq_value :
    recordGapCenter - 247732 = fullRecordGapValue02471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02471 (fullRecordGapValue02471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02471_not_prime : ¬(recordGapCenter - 247732).Prime := by
  rw [fullRecordGapTerm02471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02471_fast_pow_mod_ne_one

def fullRecordGapValue02472 : Nat := fullRecordGapCenterValue - 247642

theorem fullRecordGapTerm02472_eq_value :
    recordGapCenter - 247642 = fullRecordGapValue02472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02472 (fullRecordGapValue02472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02472_not_prime : ¬(recordGapCenter - 247642).Prime := by
  rw [fullRecordGapTerm02472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02472_fast_pow_mod_ne_one

def fullRecordGapValue02473 : Nat := fullRecordGapCenterValue - 247582

theorem fullRecordGapTerm02473_eq_value :
    recordGapCenter - 247582 = fullRecordGapValue02473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02473 (fullRecordGapValue02473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02473_not_prime : ¬(recordGapCenter - 247582).Prime := by
  rw [fullRecordGapTerm02473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02473_fast_pow_mod_ne_one

def fullRecordGapValue02474 : Nat := fullRecordGapCenterValue - 247474

theorem fullRecordGapTerm02474_eq_value :
    recordGapCenter - 247474 = fullRecordGapValue02474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02474 (fullRecordGapValue02474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02474_not_prime : ¬(recordGapCenter - 247474).Prime := by
  rw [fullRecordGapTerm02474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02474_fast_pow_mod_ne_one

def fullRecordGapValue02475 : Nat := fullRecordGapCenterValue - 247348

theorem fullRecordGapTerm02475_eq_value :
    recordGapCenter - 247348 = fullRecordGapValue02475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02475 (fullRecordGapValue02475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02475_not_prime : ¬(recordGapCenter - 247348).Prime := by
  rw [fullRecordGapTerm02475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02475_fast_pow_mod_ne_one

def fullRecordGapValue02476 : Nat := fullRecordGapCenterValue - 246838

theorem fullRecordGapTerm02476_eq_value :
    recordGapCenter - 246838 = fullRecordGapValue02476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02476 (fullRecordGapValue02476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02476_not_prime : ¬(recordGapCenter - 246838).Prime := by
  rw [fullRecordGapTerm02476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02476_fast_pow_mod_ne_one

def fullRecordGapValue02477 : Nat := fullRecordGapCenterValue - 246802

theorem fullRecordGapTerm02477_eq_value :
    recordGapCenter - 246802 = fullRecordGapValue02477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02477 (fullRecordGapValue02477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02477_not_prime : ¬(recordGapCenter - 246802).Prime := by
  rw [fullRecordGapTerm02477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02477_fast_pow_mod_ne_one

def fullRecordGapValue02478 : Nat := fullRecordGapCenterValue - 246754

theorem fullRecordGapTerm02478_eq_value :
    recordGapCenter - 246754 = fullRecordGapValue02478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02478 (fullRecordGapValue02478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02478_not_prime : ¬(recordGapCenter - 246754).Prime := by
  rw [fullRecordGapTerm02478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02478_fast_pow_mod_ne_one

def fullRecordGapValue02479 : Nat := fullRecordGapCenterValue - 246628

theorem fullRecordGapTerm02479_eq_value :
    recordGapCenter - 246628 = fullRecordGapValue02479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02479 (fullRecordGapValue02479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02479_not_prime : ¬(recordGapCenter - 246628).Prime := by
  rw [fullRecordGapTerm02479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02479_fast_pow_mod_ne_one

def fullRecordGapValue02480 : Nat := fullRecordGapCenterValue - 246622

theorem fullRecordGapTerm02480_eq_value :
    recordGapCenter - 246622 = fullRecordGapValue02480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02480 (fullRecordGapValue02480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02480_not_prime : ¬(recordGapCenter - 246622).Prime := by
  rw [fullRecordGapTerm02480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02480_fast_pow_mod_ne_one

def fullRecordGapValue02481 : Nat := fullRecordGapCenterValue - 246538

theorem fullRecordGapTerm02481_eq_value :
    recordGapCenter - 246538 = fullRecordGapValue02481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02481 (fullRecordGapValue02481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02481_not_prime : ¬(recordGapCenter - 246538).Prime := by
  rw [fullRecordGapTerm02481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02481_fast_pow_mod_ne_one

def fullRecordGapValue02482 : Nat := fullRecordGapCenterValue - 246508

theorem fullRecordGapTerm02482_eq_value :
    recordGapCenter - 246508 = fullRecordGapValue02482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02482 (fullRecordGapValue02482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02482_not_prime : ¬(recordGapCenter - 246508).Prime := by
  rw [fullRecordGapTerm02482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02482_fast_pow_mod_ne_one

def fullRecordGapValue02483 : Nat := fullRecordGapCenterValue - 246418

theorem fullRecordGapTerm02483_eq_value :
    recordGapCenter - 246418 = fullRecordGapValue02483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02483 (fullRecordGapValue02483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02483_not_prime : ¬(recordGapCenter - 246418).Prime := by
  rw [fullRecordGapTerm02483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02483_fast_pow_mod_ne_one

def fullRecordGapValue02484 : Nat := fullRecordGapCenterValue - 246412

theorem fullRecordGapTerm02484_eq_value :
    recordGapCenter - 246412 = fullRecordGapValue02484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02484 (fullRecordGapValue02484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02484_not_prime : ¬(recordGapCenter - 246412).Prime := by
  rw [fullRecordGapTerm02484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02484_fast_pow_mod_ne_one

def fullRecordGapValue02485 : Nat := fullRecordGapCenterValue - 246400

theorem fullRecordGapTerm02485_eq_value :
    recordGapCenter - 246400 = fullRecordGapValue02485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02485 (fullRecordGapValue02485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02485_not_prime : ¬(recordGapCenter - 246400).Prime := by
  rw [fullRecordGapTerm02485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02485_fast_pow_mod_ne_one

def fullRecordGapValue02486 : Nat := fullRecordGapCenterValue - 246244

theorem fullRecordGapTerm02486_eq_value :
    recordGapCenter - 246244 = fullRecordGapValue02486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02486 (fullRecordGapValue02486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02486_not_prime : ¬(recordGapCenter - 246244).Prime := by
  rw [fullRecordGapTerm02486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02486_fast_pow_mod_ne_one

def fullRecordGapValue02487 : Nat := fullRecordGapCenterValue - 246172

theorem fullRecordGapTerm02487_eq_value :
    recordGapCenter - 246172 = fullRecordGapValue02487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02487 (fullRecordGapValue02487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02487_not_prime : ¬(recordGapCenter - 246172).Prime := by
  rw [fullRecordGapTerm02487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02487_fast_pow_mod_ne_one

def fullRecordGapValue02488 : Nat := fullRecordGapCenterValue - 246154

theorem fullRecordGapTerm02488_eq_value :
    recordGapCenter - 246154 = fullRecordGapValue02488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02488 (fullRecordGapValue02488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02488_not_prime : ¬(recordGapCenter - 246154).Prime := by
  rw [fullRecordGapTerm02488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02488_fast_pow_mod_ne_one

def fullRecordGapValue02489 : Nat := fullRecordGapCenterValue - 245914

theorem fullRecordGapTerm02489_eq_value :
    recordGapCenter - 245914 = fullRecordGapValue02489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02489 (fullRecordGapValue02489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02489_not_prime : ¬(recordGapCenter - 245914).Prime := by
  rw [fullRecordGapTerm02489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02489_fast_pow_mod_ne_one

def fullRecordGapValue02490 : Nat := fullRecordGapCenterValue - 245884

theorem fullRecordGapTerm02490_eq_value :
    recordGapCenter - 245884 = fullRecordGapValue02490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02490 (fullRecordGapValue02490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02490_not_prime : ¬(recordGapCenter - 245884).Prime := by
  rw [fullRecordGapTerm02490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02490_fast_pow_mod_ne_one

def fullRecordGapValue02491 : Nat := fullRecordGapCenterValue - 245878

theorem fullRecordGapTerm02491_eq_value :
    recordGapCenter - 245878 = fullRecordGapValue02491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02491 (fullRecordGapValue02491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02491_not_prime : ¬(recordGapCenter - 245878).Prime := by
  rw [fullRecordGapTerm02491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02491_fast_pow_mod_ne_one

def fullRecordGapValue02492 : Nat := fullRecordGapCenterValue - 245782

theorem fullRecordGapTerm02492_eq_value :
    recordGapCenter - 245782 = fullRecordGapValue02492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02492 (fullRecordGapValue02492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02492_not_prime : ¬(recordGapCenter - 245782).Prime := by
  rw [fullRecordGapTerm02492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02492_fast_pow_mod_ne_one

def fullRecordGapValue02493 : Nat := fullRecordGapCenterValue - 245760

theorem fullRecordGapTerm02493_eq_value :
    recordGapCenter - 245760 = fullRecordGapValue02493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02493 (fullRecordGapValue02493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02493_not_prime : ¬(recordGapCenter - 245760).Prime := by
  rw [fullRecordGapTerm02493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02493_fast_pow_mod_ne_one

def fullRecordGapValue02494 : Nat := fullRecordGapCenterValue - 245734

theorem fullRecordGapTerm02494_eq_value :
    recordGapCenter - 245734 = fullRecordGapValue02494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02494 (fullRecordGapValue02494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02494_not_prime : ¬(recordGapCenter - 245734).Prime := by
  rw [fullRecordGapTerm02494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02494_fast_pow_mod_ne_one

def fullRecordGapValue02495 : Nat := fullRecordGapCenterValue - 245668

theorem fullRecordGapTerm02495_eq_value :
    recordGapCenter - 245668 = fullRecordGapValue02495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02495 (fullRecordGapValue02495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02495_not_prime : ¬(recordGapCenter - 245668).Prime := by
  rw [fullRecordGapTerm02495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02495_fast_pow_mod_ne_one

def fullRecordGapValue02496 : Nat := fullRecordGapCenterValue - 245452

theorem fullRecordGapTerm02496_eq_value :
    recordGapCenter - 245452 = fullRecordGapValue02496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02496 (fullRecordGapValue02496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02496_not_prime : ¬(recordGapCenter - 245452).Prime := by
  rw [fullRecordGapTerm02496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02496_fast_pow_mod_ne_one

def fullRecordGapValue02497 : Nat := fullRecordGapCenterValue - 245332

theorem fullRecordGapTerm02497_eq_value :
    recordGapCenter - 245332 = fullRecordGapValue02497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02497 (fullRecordGapValue02497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02497_not_prime : ¬(recordGapCenter - 245332).Prime := by
  rw [fullRecordGapTerm02497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02497_fast_pow_mod_ne_one

def fullRecordGapValue02498 : Nat := fullRecordGapCenterValue - 245188

theorem fullRecordGapTerm02498_eq_value :
    recordGapCenter - 245188 = fullRecordGapValue02498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02498 (fullRecordGapValue02498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02498_not_prime : ¬(recordGapCenter - 245188).Prime := by
  rw [fullRecordGapTerm02498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02498_fast_pow_mod_ne_one

def fullRecordGapValue02499 : Nat := fullRecordGapCenterValue - 244978

theorem fullRecordGapTerm02499_eq_value :
    recordGapCenter - 244978 = fullRecordGapValue02499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02499 (fullRecordGapValue02499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02499_not_prime : ¬(recordGapCenter - 244978).Prime := by
  rw [fullRecordGapTerm02499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02499_fast_pow_mod_ne_one

def fullRecordGapValue02500 : Nat := fullRecordGapCenterValue - 244944

theorem fullRecordGapTerm02500_eq_value :
    recordGapCenter - 244944 = fullRecordGapValue02500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02500 (fullRecordGapValue02500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02500_not_prime : ¬(recordGapCenter - 244944).Prime := by
  rw [fullRecordGapTerm02500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02500_fast_pow_mod_ne_one

def fullRecordGapValue02501 : Nat := fullRecordGapCenterValue - 244564

theorem fullRecordGapTerm02501_eq_value :
    recordGapCenter - 244564 = fullRecordGapValue02501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02501 (fullRecordGapValue02501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02501_not_prime : ¬(recordGapCenter - 244564).Prime := by
  rw [fullRecordGapTerm02501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02501_fast_pow_mod_ne_one

def fullRecordGapValue02502 : Nat := fullRecordGapCenterValue - 244558

theorem fullRecordGapTerm02502_eq_value :
    recordGapCenter - 244558 = fullRecordGapValue02502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02502 (fullRecordGapValue02502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02502_not_prime : ¬(recordGapCenter - 244558).Prime := by
  rw [fullRecordGapTerm02502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02502_fast_pow_mod_ne_one

def fullRecordGapValue02503 : Nat := fullRecordGapCenterValue - 244414

theorem fullRecordGapTerm02503_eq_value :
    recordGapCenter - 244414 = fullRecordGapValue02503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02503 (fullRecordGapValue02503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02503_not_prime : ¬(recordGapCenter - 244414).Prime := by
  rw [fullRecordGapTerm02503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02503_fast_pow_mod_ne_one

def fullRecordGapValue02504 : Nat := fullRecordGapCenterValue - 244234

theorem fullRecordGapTerm02504_eq_value :
    recordGapCenter - 244234 = fullRecordGapValue02504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02504 (fullRecordGapValue02504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02504_not_prime : ¬(recordGapCenter - 244234).Prime := by
  rw [fullRecordGapTerm02504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02504_fast_pow_mod_ne_one

def fullRecordGapValue02505 : Nat := fullRecordGapCenterValue - 244198

theorem fullRecordGapTerm02505_eq_value :
    recordGapCenter - 244198 = fullRecordGapValue02505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02505 (fullRecordGapValue02505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02505_not_prime : ¬(recordGapCenter - 244198).Prime := by
  rw [fullRecordGapTerm02505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02505_fast_pow_mod_ne_one

def fullRecordGapValue02506 : Nat := fullRecordGapCenterValue - 244102

theorem fullRecordGapTerm02506_eq_value :
    recordGapCenter - 244102 = fullRecordGapValue02506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02506 (fullRecordGapValue02506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02506_not_prime : ¬(recordGapCenter - 244102).Prime := by
  rw [fullRecordGapTerm02506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02506_fast_pow_mod_ne_one

def fullRecordGapValue02507 : Nat := fullRecordGapCenterValue - 244054

theorem fullRecordGapTerm02507_eq_value :
    recordGapCenter - 244054 = fullRecordGapValue02507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02507 (fullRecordGapValue02507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02507_not_prime : ¬(recordGapCenter - 244054).Prime := by
  rw [fullRecordGapTerm02507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02507_fast_pow_mod_ne_one

def fullRecordGapValue02508 : Nat := fullRecordGapCenterValue - 243778

theorem fullRecordGapTerm02508_eq_value :
    recordGapCenter - 243778 = fullRecordGapValue02508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02508 (fullRecordGapValue02508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02508_not_prime : ¬(recordGapCenter - 243778).Prime := by
  rw [fullRecordGapTerm02508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02508_fast_pow_mod_ne_one

def fullRecordGapValue02509 : Nat := fullRecordGapCenterValue - 243772

theorem fullRecordGapTerm02509_eq_value :
    recordGapCenter - 243772 = fullRecordGapValue02509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02509 (fullRecordGapValue02509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02509_not_prime : ¬(recordGapCenter - 243772).Prime := by
  rw [fullRecordGapTerm02509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02509_fast_pow_mod_ne_one

def fullRecordGapValue02510 : Nat := fullRecordGapCenterValue - 243604

theorem fullRecordGapTerm02510_eq_value :
    recordGapCenter - 243604 = fullRecordGapValue02510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02510 (fullRecordGapValue02510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02510_not_prime : ¬(recordGapCenter - 243604).Prime := by
  rw [fullRecordGapTerm02510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02510_fast_pow_mod_ne_one

def fullRecordGapValue02511 : Nat := fullRecordGapCenterValue - 243262

theorem fullRecordGapTerm02511_eq_value :
    recordGapCenter - 243262 = fullRecordGapValue02511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02511 (fullRecordGapValue02511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02511_not_prime : ¬(recordGapCenter - 243262).Prime := by
  rw [fullRecordGapTerm02511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02511_fast_pow_mod_ne_one

def fullRecordGapValue02512 : Nat := fullRecordGapCenterValue - 243172

theorem fullRecordGapTerm02512_eq_value :
    recordGapCenter - 243172 = fullRecordGapValue02512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02512 (fullRecordGapValue02512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02512_not_prime : ¬(recordGapCenter - 243172).Prime := by
  rw [fullRecordGapTerm02512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02512_fast_pow_mod_ne_one

def fullRecordGapValue02513 : Nat := fullRecordGapCenterValue - 243154

theorem fullRecordGapTerm02513_eq_value :
    recordGapCenter - 243154 = fullRecordGapValue02513 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02513_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02513 (fullRecordGapValue02513 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02513_not_prime : ¬(recordGapCenter - 243154).Prime := by
  rw [fullRecordGapTerm02513_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02513, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02513_fast_pow_mod_ne_one

def fullRecordGapValue02514 : Nat := fullRecordGapCenterValue - 242938

theorem fullRecordGapTerm02514_eq_value :
    recordGapCenter - 242938 = fullRecordGapValue02514 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02514_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02514 (fullRecordGapValue02514 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02514_not_prime : ¬(recordGapCenter - 242938).Prime := by
  rw [fullRecordGapTerm02514_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02514, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02514_fast_pow_mod_ne_one

def fullRecordGapValue02515 : Nat := fullRecordGapCenterValue - 242878

theorem fullRecordGapTerm02515_eq_value :
    recordGapCenter - 242878 = fullRecordGapValue02515 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02515_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02515 (fullRecordGapValue02515 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02515_not_prime : ¬(recordGapCenter - 242878).Prime := by
  rw [fullRecordGapTerm02515_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02515, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02515_fast_pow_mod_ne_one

def fullRecordGapValue02516 : Nat := fullRecordGapCenterValue - 242842

theorem fullRecordGapTerm02516_eq_value :
    recordGapCenter - 242842 = fullRecordGapValue02516 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02516_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02516 (fullRecordGapValue02516 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02516_not_prime : ¬(recordGapCenter - 242842).Prime := by
  rw [fullRecordGapTerm02516_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02516, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02516_fast_pow_mod_ne_one

def fullRecordGapValue02517 : Nat := fullRecordGapCenterValue - 242758

theorem fullRecordGapTerm02517_eq_value :
    recordGapCenter - 242758 = fullRecordGapValue02517 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02517_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02517 (fullRecordGapValue02517 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02517_not_prime : ¬(recordGapCenter - 242758).Prime := by
  rw [fullRecordGapTerm02517_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02517, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02517_fast_pow_mod_ne_one

def fullRecordGapValue02518 : Nat := fullRecordGapCenterValue - 242644

theorem fullRecordGapTerm02518_eq_value :
    recordGapCenter - 242644 = fullRecordGapValue02518 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02518_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02518 (fullRecordGapValue02518 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02518_not_prime : ¬(recordGapCenter - 242644).Prime := by
  rw [fullRecordGapTerm02518_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02518, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02518_fast_pow_mod_ne_one

def fullRecordGapValue02519 : Nat := fullRecordGapCenterValue - 242524

theorem fullRecordGapTerm02519_eq_value :
    recordGapCenter - 242524 = fullRecordGapValue02519 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02519_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02519 (fullRecordGapValue02519 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02519_not_prime : ¬(recordGapCenter - 242524).Prime := by
  rw [fullRecordGapTerm02519_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02519, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02519_fast_pow_mod_ne_one

def fullRecordGapValue02520 : Nat := fullRecordGapCenterValue - 242458

theorem fullRecordGapTerm02520_eq_value :
    recordGapCenter - 242458 = fullRecordGapValue02520 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02520_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02520 (fullRecordGapValue02520 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02520_not_prime : ¬(recordGapCenter - 242458).Prime := by
  rw [fullRecordGapTerm02520_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02520, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02520_fast_pow_mod_ne_one

def fullRecordGapValue02521 : Nat := fullRecordGapCenterValue - 242314

theorem fullRecordGapTerm02521_eq_value :
    recordGapCenter - 242314 = fullRecordGapValue02521 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02521_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02521 (fullRecordGapValue02521 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02521_not_prime : ¬(recordGapCenter - 242314).Prime := by
  rw [fullRecordGapTerm02521_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02521, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02521_fast_pow_mod_ne_one

def fullRecordGapValue02522 : Nat := fullRecordGapCenterValue - 242134

theorem fullRecordGapTerm02522_eq_value :
    recordGapCenter - 242134 = fullRecordGapValue02522 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02522_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02522 (fullRecordGapValue02522 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02522_not_prime : ¬(recordGapCenter - 242134).Prime := by
  rw [fullRecordGapTerm02522_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02522, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02522_fast_pow_mod_ne_one

def fullRecordGapValue02523 : Nat := fullRecordGapCenterValue - 242002

theorem fullRecordGapTerm02523_eq_value :
    recordGapCenter - 242002 = fullRecordGapValue02523 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02523_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02523 (fullRecordGapValue02523 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02523_not_prime : ¬(recordGapCenter - 242002).Prime := by
  rw [fullRecordGapTerm02523_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02523, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02523_fast_pow_mod_ne_one

def fullRecordGapValue02524 : Nat := fullRecordGapCenterValue - 241920

theorem fullRecordGapTerm02524_eq_value :
    recordGapCenter - 241920 = fullRecordGapValue02524 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02524_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02524 (fullRecordGapValue02524 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02524_not_prime : ¬(recordGapCenter - 241920).Prime := by
  rw [fullRecordGapTerm02524_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02524, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02524_fast_pow_mod_ne_one

def fullRecordGapValue02525 : Nat := fullRecordGapCenterValue - 241882

theorem fullRecordGapTerm02525_eq_value :
    recordGapCenter - 241882 = fullRecordGapValue02525 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02525_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02525 (fullRecordGapValue02525 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02525_not_prime : ¬(recordGapCenter - 241882).Prime := by
  rw [fullRecordGapTerm02525_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02525, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02525_fast_pow_mod_ne_one

def fullRecordGapValue02526 : Nat := fullRecordGapCenterValue - 241372

theorem fullRecordGapTerm02526_eq_value :
    recordGapCenter - 241372 = fullRecordGapValue02526 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02526_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02526 (fullRecordGapValue02526 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02526_not_prime : ¬(recordGapCenter - 241372).Prime := by
  rw [fullRecordGapTerm02526_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02526, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02526_fast_pow_mod_ne_one

def fullRecordGapValue02527 : Nat := fullRecordGapCenterValue - 241342

theorem fullRecordGapTerm02527_eq_value :
    recordGapCenter - 241342 = fullRecordGapValue02527 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02527_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02527 (fullRecordGapValue02527 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02527_not_prime : ¬(recordGapCenter - 241342).Prime := by
  rw [fullRecordGapTerm02527_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02527, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02527_fast_pow_mod_ne_one

def fullRecordGapValue02528 : Nat := fullRecordGapCenterValue - 241294

theorem fullRecordGapTerm02528_eq_value :
    recordGapCenter - 241294 = fullRecordGapValue02528 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02528_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02528 (fullRecordGapValue02528 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02528_not_prime : ¬(recordGapCenter - 241294).Prime := by
  rw [fullRecordGapTerm02528_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02528, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02528_fast_pow_mod_ne_one

def fullRecordGapValue02529 : Nat := fullRecordGapCenterValue - 240742

theorem fullRecordGapTerm02529_eq_value :
    recordGapCenter - 240742 = fullRecordGapValue02529 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02529_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02529 (fullRecordGapValue02529 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02529_not_prime : ¬(recordGapCenter - 240742).Prime := by
  rw [fullRecordGapTerm02529_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02529, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02529_fast_pow_mod_ne_one

def fullRecordGapValue02530 : Nat := fullRecordGapCenterValue - 240532

theorem fullRecordGapTerm02530_eq_value :
    recordGapCenter - 240532 = fullRecordGapValue02530 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02530_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02530 (fullRecordGapValue02530 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02530_not_prime : ¬(recordGapCenter - 240532).Prime := by
  rw [fullRecordGapTerm02530_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02530, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02530_fast_pow_mod_ne_one

def fullRecordGapValue02531 : Nat := fullRecordGapCenterValue - 240418

theorem fullRecordGapTerm02531_eq_value :
    recordGapCenter - 240418 = fullRecordGapValue02531 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02531_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02531 (fullRecordGapValue02531 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02531_not_prime : ¬(recordGapCenter - 240418).Prime := by
  rw [fullRecordGapTerm02531_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02531, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02531_fast_pow_mod_ne_one

def fullRecordGapValue02532 : Nat := fullRecordGapCenterValue - 240412

theorem fullRecordGapTerm02532_eq_value :
    recordGapCenter - 240412 = fullRecordGapValue02532 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02532_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02532 (fullRecordGapValue02532 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02532_not_prime : ¬(recordGapCenter - 240412).Prime := by
  rw [fullRecordGapTerm02532_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02532, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02532_fast_pow_mod_ne_one

def fullRecordGapValue02533 : Nat := fullRecordGapCenterValue - 240148

theorem fullRecordGapTerm02533_eq_value :
    recordGapCenter - 240148 = fullRecordGapValue02533 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02533_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02533 (fullRecordGapValue02533 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02533_not_prime : ¬(recordGapCenter - 240148).Prime := by
  rw [fullRecordGapTerm02533_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02533, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02533_fast_pow_mod_ne_one

def fullRecordGapValue02534 : Nat := fullRecordGapCenterValue - 240100

theorem fullRecordGapTerm02534_eq_value :
    recordGapCenter - 240100 = fullRecordGapValue02534 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02534_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02534 (fullRecordGapValue02534 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02534_not_prime : ¬(recordGapCenter - 240100).Prime := by
  rw [fullRecordGapTerm02534_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02534, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02534_fast_pow_mod_ne_one

def fullRecordGapValue02535 : Nat := fullRecordGapCenterValue - 240022

theorem fullRecordGapTerm02535_eq_value :
    recordGapCenter - 240022 = fullRecordGapValue02535 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02535_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02535 (fullRecordGapValue02535 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02535_not_prime : ¬(recordGapCenter - 240022).Prime := by
  rw [fullRecordGapTerm02535_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02535, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02535_fast_pow_mod_ne_one

def fullRecordGapValue02536 : Nat := fullRecordGapCenterValue - 240000

theorem fullRecordGapTerm02536_eq_value :
    recordGapCenter - 240000 = fullRecordGapValue02536 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02536_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02536 (fullRecordGapValue02536 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02536_not_prime : ¬(recordGapCenter - 240000).Prime := by
  rw [fullRecordGapTerm02536_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02536, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02536_fast_pow_mod_ne_one

def fullRecordGapValue02537 : Nat := fullRecordGapCenterValue - 239662

theorem fullRecordGapTerm02537_eq_value :
    recordGapCenter - 239662 = fullRecordGapValue02537 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02537_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02537 (fullRecordGapValue02537 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02537_not_prime : ¬(recordGapCenter - 239662).Prime := by
  rw [fullRecordGapTerm02537_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02537, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02537_fast_pow_mod_ne_one

def fullRecordGapValue02538 : Nat := fullRecordGapCenterValue - 239332

theorem fullRecordGapTerm02538_eq_value :
    recordGapCenter - 239332 = fullRecordGapValue02538 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02538_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02538 (fullRecordGapValue02538 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02538_not_prime : ¬(recordGapCenter - 239332).Prime := by
  rw [fullRecordGapTerm02538_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02538, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02538_fast_pow_mod_ne_one

def fullRecordGapValue02539 : Nat := fullRecordGapCenterValue - 239182

theorem fullRecordGapTerm02539_eq_value :
    recordGapCenter - 239182 = fullRecordGapValue02539 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02539_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02539 (fullRecordGapValue02539 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02539_not_prime : ¬(recordGapCenter - 239182).Prime := by
  rw [fullRecordGapTerm02539_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02539, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02539_fast_pow_mod_ne_one

def fullRecordGapValue02540 : Nat := fullRecordGapCenterValue - 239164

theorem fullRecordGapTerm02540_eq_value :
    recordGapCenter - 239164 = fullRecordGapValue02540 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02540_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02540 (fullRecordGapValue02540 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02540_not_prime : ¬(recordGapCenter - 239164).Prime := by
  rw [fullRecordGapTerm02540_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02540, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02540_fast_pow_mod_ne_one

def fullRecordGapValue02541 : Nat := fullRecordGapCenterValue - 239098

theorem fullRecordGapTerm02541_eq_value :
    recordGapCenter - 239098 = fullRecordGapValue02541 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02541_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02541 (fullRecordGapValue02541 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02541_not_prime : ¬(recordGapCenter - 239098).Prime := by
  rw [fullRecordGapTerm02541_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02541, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02541_fast_pow_mod_ne_one

def fullRecordGapValue02542 : Nat := fullRecordGapCenterValue - 238978

theorem fullRecordGapTerm02542_eq_value :
    recordGapCenter - 238978 = fullRecordGapValue02542 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02542_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02542 (fullRecordGapValue02542 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02542_not_prime : ¬(recordGapCenter - 238978).Prime := by
  rw [fullRecordGapTerm02542_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02542, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02542_fast_pow_mod_ne_one

def fullRecordGapValue02543 : Nat := fullRecordGapCenterValue - 238894

theorem fullRecordGapTerm02543_eq_value :
    recordGapCenter - 238894 = fullRecordGapValue02543 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02543_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02543 (fullRecordGapValue02543 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02543_not_prime : ¬(recordGapCenter - 238894).Prime := by
  rw [fullRecordGapTerm02543_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02543, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02543_fast_pow_mod_ne_one

def fullRecordGapValue02544 : Nat := fullRecordGapCenterValue - 238828

theorem fullRecordGapTerm02544_eq_value :
    recordGapCenter - 238828 = fullRecordGapValue02544 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02544_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02544 (fullRecordGapValue02544 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02544_not_prime : ¬(recordGapCenter - 238828).Prime := by
  rw [fullRecordGapTerm02544_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02544, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02544_fast_pow_mod_ne_one

def fullRecordGapValue02545 : Nat := fullRecordGapCenterValue - 238324

theorem fullRecordGapTerm02545_eq_value :
    recordGapCenter - 238324 = fullRecordGapValue02545 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02545_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02545 (fullRecordGapValue02545 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02545_not_prime : ¬(recordGapCenter - 238324).Prime := by
  rw [fullRecordGapTerm02545_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02545, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02545_fast_pow_mod_ne_one

def fullRecordGapValue02546 : Nat := fullRecordGapCenterValue - 238318

theorem fullRecordGapTerm02546_eq_value :
    recordGapCenter - 238318 = fullRecordGapValue02546 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02546_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02546 (fullRecordGapValue02546 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02546_not_prime : ¬(recordGapCenter - 238318).Prime := by
  rw [fullRecordGapTerm02546_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02546, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02546_fast_pow_mod_ne_one

def fullRecordGapValue02547 : Nat := fullRecordGapCenterValue - 237862

theorem fullRecordGapTerm02547_eq_value :
    recordGapCenter - 237862 = fullRecordGapValue02547 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02547_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02547 (fullRecordGapValue02547 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02547_not_prime : ¬(recordGapCenter - 237862).Prime := by
  rw [fullRecordGapTerm02547_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02547, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02547_fast_pow_mod_ne_one

def fullRecordGapValue02548 : Nat := fullRecordGapCenterValue - 237814

theorem fullRecordGapTerm02548_eq_value :
    recordGapCenter - 237814 = fullRecordGapValue02548 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02548_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02548 (fullRecordGapValue02548 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02548_not_prime : ¬(recordGapCenter - 237814).Prime := by
  rw [fullRecordGapTerm02548_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02548, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02548_fast_pow_mod_ne_one

def fullRecordGapValue02549 : Nat := fullRecordGapCenterValue - 237514

theorem fullRecordGapTerm02549_eq_value :
    recordGapCenter - 237514 = fullRecordGapValue02549 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02549_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02549 (fullRecordGapValue02549 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02549_not_prime : ¬(recordGapCenter - 237514).Prime := by
  rw [fullRecordGapTerm02549_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02549, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02549_fast_pow_mod_ne_one

def fullRecordGapValue02550 : Nat := fullRecordGapCenterValue - 237502

theorem fullRecordGapTerm02550_eq_value :
    recordGapCenter - 237502 = fullRecordGapValue02550 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02550_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02550 (fullRecordGapValue02550 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02550_not_prime : ¬(recordGapCenter - 237502).Prime := by
  rw [fullRecordGapTerm02550_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02550, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02550_fast_pow_mod_ne_one

def fullRecordGapValue02551 : Nat := fullRecordGapCenterValue - 237382

theorem fullRecordGapTerm02551_eq_value :
    recordGapCenter - 237382 = fullRecordGapValue02551 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02551_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02551 (fullRecordGapValue02551 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02551_not_prime : ¬(recordGapCenter - 237382).Prime := by
  rw [fullRecordGapTerm02551_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02551, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02551_fast_pow_mod_ne_one

def fullRecordGapValue02552 : Nat := fullRecordGapCenterValue - 237160

theorem fullRecordGapTerm02552_eq_value :
    recordGapCenter - 237160 = fullRecordGapValue02552 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02552_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02552 (fullRecordGapValue02552 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02552_not_prime : ¬(recordGapCenter - 237160).Prime := by
  rw [fullRecordGapTerm02552_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02552, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02552_fast_pow_mod_ne_one

def fullRecordGapValue02553 : Nat := fullRecordGapCenterValue - 237052

theorem fullRecordGapTerm02553_eq_value :
    recordGapCenter - 237052 = fullRecordGapValue02553 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02553_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02553 (fullRecordGapValue02553 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02553_not_prime : ¬(recordGapCenter - 237052).Prime := by
  rw [fullRecordGapTerm02553_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02553, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02553_fast_pow_mod_ne_one

def fullRecordGapValue02554 : Nat := fullRecordGapCenterValue - 236932

theorem fullRecordGapTerm02554_eq_value :
    recordGapCenter - 236932 = fullRecordGapValue02554 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02554_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02554 (fullRecordGapValue02554 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02554_not_prime : ¬(recordGapCenter - 236932).Prime := by
  rw [fullRecordGapTerm02554_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02554, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02554_fast_pow_mod_ne_one

def fullRecordGapValue02555 : Nat := fullRecordGapCenterValue - 236554

theorem fullRecordGapTerm02555_eq_value :
    recordGapCenter - 236554 = fullRecordGapValue02555 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02555_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02555 (fullRecordGapValue02555 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02555_not_prime : ¬(recordGapCenter - 236554).Prime := by
  rw [fullRecordGapTerm02555_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02555, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02555_fast_pow_mod_ne_one

def fullRecordGapValue02556 : Nat := fullRecordGapCenterValue - 236544

theorem fullRecordGapTerm02556_eq_value :
    recordGapCenter - 236544 = fullRecordGapValue02556 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02556_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02556 (fullRecordGapValue02556 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02556_not_prime : ¬(recordGapCenter - 236544).Prime := by
  rw [fullRecordGapTerm02556_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02556, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02556_fast_pow_mod_ne_one

def fullRecordGapValue02557 : Nat := fullRecordGapCenterValue - 236338

theorem fullRecordGapTerm02557_eq_value :
    recordGapCenter - 236338 = fullRecordGapValue02557 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02557_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02557 (fullRecordGapValue02557 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02557_not_prime : ¬(recordGapCenter - 236338).Prime := by
  rw [fullRecordGapTerm02557_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02557, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02557_fast_pow_mod_ne_one

def fullRecordGapValue02558 : Nat := fullRecordGapCenterValue - 236332

theorem fullRecordGapTerm02558_eq_value :
    recordGapCenter - 236332 = fullRecordGapValue02558 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02558_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02558 (fullRecordGapValue02558 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02558_not_prime : ¬(recordGapCenter - 236332).Prime := by
  rw [fullRecordGapTerm02558_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02558, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02558_fast_pow_mod_ne_one

def fullRecordGapValue02559 : Nat := fullRecordGapCenterValue - 236250

theorem fullRecordGapTerm02559_eq_value :
    recordGapCenter - 236250 = fullRecordGapValue02559 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02559_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02559 (fullRecordGapValue02559 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02559_not_prime : ¬(recordGapCenter - 236250).Prime := by
  rw [fullRecordGapTerm02559_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02559, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02559_fast_pow_mod_ne_one

def fullRecordGapValue02560 : Nat := fullRecordGapCenterValue - 236212

theorem fullRecordGapTerm02560_eq_value :
    recordGapCenter - 236212 = fullRecordGapValue02560 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02560_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02560 (fullRecordGapValue02560 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02560_not_prime : ¬(recordGapCenter - 236212).Prime := by
  rw [fullRecordGapTerm02560_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02560, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02560_fast_pow_mod_ne_one

end PrimeFactorUnimodality
