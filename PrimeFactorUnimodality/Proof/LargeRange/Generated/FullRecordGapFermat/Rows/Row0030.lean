import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue07425 : Nat := fullRecordGapCenterValue + 427796

theorem fullRecordGapTerm07425_eq_value :
    recordGapCenter + 427796 = fullRecordGapValue07425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07425 (fullRecordGapValue07425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07425_not_prime : ¬(recordGapCenter + 427796).Prime := by
  rw [fullRecordGapTerm07425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07425_fast_pow_mod_ne_one

def fullRecordGapValue07426 : Nat := fullRecordGapCenterValue + 427886

theorem fullRecordGapTerm07426_eq_value :
    recordGapCenter + 427886 = fullRecordGapValue07426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07426 (fullRecordGapValue07426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07426_not_prime : ¬(recordGapCenter + 427886).Prime := by
  rw [fullRecordGapTerm07426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07426_fast_pow_mod_ne_one

def fullRecordGapValue07427 : Nat := fullRecordGapCenterValue + 427998

theorem fullRecordGapTerm07427_eq_value :
    recordGapCenter + 427998 = fullRecordGapValue07427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07427 (fullRecordGapValue07427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07427_not_prime : ¬(recordGapCenter + 427998).Prime := by
  rw [fullRecordGapTerm07427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07427_fast_pow_mod_ne_one

def fullRecordGapValue07428 : Nat := fullRecordGapCenterValue + 428018

theorem fullRecordGapTerm07428_eq_value :
    recordGapCenter + 428018 = fullRecordGapValue07428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07428 (fullRecordGapValue07428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07428_not_prime : ¬(recordGapCenter + 428018).Prime := by
  rw [fullRecordGapTerm07428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07428_fast_pow_mod_ne_one

def fullRecordGapValue07429 : Nat := fullRecordGapCenterValue + 428066

theorem fullRecordGapTerm07429_eq_value :
    recordGapCenter + 428066 = fullRecordGapValue07429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07429 (fullRecordGapValue07429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07429_not_prime : ¬(recordGapCenter + 428066).Prime := by
  rw [fullRecordGapTerm07429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07429_fast_pow_mod_ne_one

def fullRecordGapValue07430 : Nat := fullRecordGapCenterValue + 428082

theorem fullRecordGapTerm07430_eq_value :
    recordGapCenter + 428082 = fullRecordGapValue07430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07430 (fullRecordGapValue07430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07430_not_prime : ¬(recordGapCenter + 428082).Prime := by
  rw [fullRecordGapTerm07430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07430_fast_pow_mod_ne_one

def fullRecordGapValue07431 : Nat := fullRecordGapCenterValue + 428102

theorem fullRecordGapTerm07431_eq_value :
    recordGapCenter + 428102 = fullRecordGapValue07431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07431 (fullRecordGapValue07431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07431_not_prime : ¬(recordGapCenter + 428102).Prime := by
  rw [fullRecordGapTerm07431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07431_fast_pow_mod_ne_one

def fullRecordGapValue07432 : Nat := fullRecordGapCenterValue + 428118

theorem fullRecordGapTerm07432_eq_value :
    recordGapCenter + 428118 = fullRecordGapValue07432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07432 (fullRecordGapValue07432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07432_not_prime : ¬(recordGapCenter + 428118).Prime := by
  rw [fullRecordGapTerm07432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07432_fast_pow_mod_ne_one

def fullRecordGapValue07433 : Nat := fullRecordGapCenterValue + 428132

theorem fullRecordGapTerm07433_eq_value :
    recordGapCenter + 428132 = fullRecordGapValue07433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07433 (fullRecordGapValue07433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07433_not_prime : ¬(recordGapCenter + 428132).Prime := by
  rw [fullRecordGapTerm07433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07433_fast_pow_mod_ne_one

def fullRecordGapValue07434 : Nat := fullRecordGapCenterValue + 428216

theorem fullRecordGapTerm07434_eq_value :
    recordGapCenter + 428216 = fullRecordGapValue07434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07434 (fullRecordGapValue07434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07434_not_prime : ¬(recordGapCenter + 428216).Prime := by
  rw [fullRecordGapTerm07434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07434_fast_pow_mod_ne_one

def fullRecordGapValue07435 : Nat := fullRecordGapCenterValue + 428228

theorem fullRecordGapTerm07435_eq_value :
    recordGapCenter + 428228 = fullRecordGapValue07435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07435 (fullRecordGapValue07435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07435_not_prime : ¬(recordGapCenter + 428228).Prime := by
  rw [fullRecordGapTerm07435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07435_fast_pow_mod_ne_one

def fullRecordGapValue07436 : Nat := fullRecordGapCenterValue + 428258

theorem fullRecordGapTerm07436_eq_value :
    recordGapCenter + 428258 = fullRecordGapValue07436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07436 (fullRecordGapValue07436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07436_not_prime : ¬(recordGapCenter + 428258).Prime := by
  rw [fullRecordGapTerm07436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07436_fast_pow_mod_ne_one

def fullRecordGapValue07437 : Nat := fullRecordGapCenterValue + 428276

theorem fullRecordGapTerm07437_eq_value :
    recordGapCenter + 428276 = fullRecordGapValue07437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07437 (fullRecordGapValue07437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07437_not_prime : ¬(recordGapCenter + 428276).Prime := by
  rw [fullRecordGapTerm07437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07437_fast_pow_mod_ne_one

def fullRecordGapValue07438 : Nat := fullRecordGapCenterValue + 428282

theorem fullRecordGapTerm07438_eq_value :
    recordGapCenter + 428282 = fullRecordGapValue07438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07438 (fullRecordGapValue07438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07438_not_prime : ¬(recordGapCenter + 428282).Prime := by
  rw [fullRecordGapTerm07438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07438_fast_pow_mod_ne_one

def fullRecordGapValue07439 : Nat := fullRecordGapCenterValue + 428396

theorem fullRecordGapTerm07439_eq_value :
    recordGapCenter + 428396 = fullRecordGapValue07439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07439 (fullRecordGapValue07439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07439_not_prime : ¬(recordGapCenter + 428396).Prime := by
  rw [fullRecordGapTerm07439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07439_fast_pow_mod_ne_one

def fullRecordGapValue07440 : Nat := fullRecordGapCenterValue + 428426

theorem fullRecordGapTerm07440_eq_value :
    recordGapCenter + 428426 = fullRecordGapValue07440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07440 (fullRecordGapValue07440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07440_not_prime : ¬(recordGapCenter + 428426).Prime := by
  rw [fullRecordGapTerm07440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07440_fast_pow_mod_ne_one

def fullRecordGapValue07441 : Nat := fullRecordGapCenterValue + 428438

theorem fullRecordGapTerm07441_eq_value :
    recordGapCenter + 428438 = fullRecordGapValue07441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07441 (fullRecordGapValue07441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07441_not_prime : ¬(recordGapCenter + 428438).Prime := by
  rw [fullRecordGapTerm07441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07441_fast_pow_mod_ne_one

def fullRecordGapValue07442 : Nat := fullRecordGapCenterValue + 428486

theorem fullRecordGapTerm07442_eq_value :
    recordGapCenter + 428486 = fullRecordGapValue07442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07442 (fullRecordGapValue07442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07442_not_prime : ¬(recordGapCenter + 428486).Prime := by
  rw [fullRecordGapTerm07442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07442_fast_pow_mod_ne_one

def fullRecordGapValue07443 : Nat := fullRecordGapCenterValue + 428652

theorem fullRecordGapTerm07443_eq_value :
    recordGapCenter + 428652 = fullRecordGapValue07443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07443 (fullRecordGapValue07443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07443_not_prime : ¬(recordGapCenter + 428652).Prime := by
  rw [fullRecordGapTerm07443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07443_fast_pow_mod_ne_one

def fullRecordGapValue07444 : Nat := fullRecordGapCenterValue + 428762

theorem fullRecordGapTerm07444_eq_value :
    recordGapCenter + 428762 = fullRecordGapValue07444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07444 (fullRecordGapValue07444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07444_not_prime : ¬(recordGapCenter + 428762).Prime := by
  rw [fullRecordGapTerm07444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07444_fast_pow_mod_ne_one

def fullRecordGapValue07445 : Nat := fullRecordGapCenterValue + 428838

theorem fullRecordGapTerm07445_eq_value :
    recordGapCenter + 428838 = fullRecordGapValue07445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07445 (fullRecordGapValue07445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07445_not_prime : ¬(recordGapCenter + 428838).Prime := by
  rw [fullRecordGapTerm07445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07445_fast_pow_mod_ne_one

def fullRecordGapValue07446 : Nat := fullRecordGapCenterValue + 428888

theorem fullRecordGapTerm07446_eq_value :
    recordGapCenter + 428888 = fullRecordGapValue07446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07446 (fullRecordGapValue07446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07446_not_prime : ¬(recordGapCenter + 428888).Prime := by
  rw [fullRecordGapTerm07446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07446_fast_pow_mod_ne_one

def fullRecordGapValue07447 : Nat := fullRecordGapCenterValue + 428898

theorem fullRecordGapTerm07447_eq_value :
    recordGapCenter + 428898 = fullRecordGapValue07447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07447 (fullRecordGapValue07447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07447_not_prime : ¬(recordGapCenter + 428898).Prime := by
  rw [fullRecordGapTerm07447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07447_fast_pow_mod_ne_one

def fullRecordGapValue07448 : Nat := fullRecordGapCenterValue + 429038

theorem fullRecordGapTerm07448_eq_value :
    recordGapCenter + 429038 = fullRecordGapValue07448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07448 (fullRecordGapValue07448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07448_not_prime : ¬(recordGapCenter + 429038).Prime := by
  rw [fullRecordGapTerm07448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07448_fast_pow_mod_ne_one

def fullRecordGapValue07449 : Nat := fullRecordGapCenterValue + 429356

theorem fullRecordGapTerm07449_eq_value :
    recordGapCenter + 429356 = fullRecordGapValue07449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07449 (fullRecordGapValue07449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07449_not_prime : ¬(recordGapCenter + 429356).Prime := by
  rw [fullRecordGapTerm07449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07449_fast_pow_mod_ne_one

def fullRecordGapValue07450 : Nat := fullRecordGapCenterValue + 429558

theorem fullRecordGapTerm07450_eq_value :
    recordGapCenter + 429558 = fullRecordGapValue07450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07450 (fullRecordGapValue07450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07450_not_prime : ¬(recordGapCenter + 429558).Prime := by
  rw [fullRecordGapTerm07450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07450_fast_pow_mod_ne_one

def fullRecordGapValue07451 : Nat := fullRecordGapCenterValue + 429578

theorem fullRecordGapTerm07451_eq_value :
    recordGapCenter + 429578 = fullRecordGapValue07451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07451 (fullRecordGapValue07451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07451_not_prime : ¬(recordGapCenter + 429578).Prime := by
  rw [fullRecordGapTerm07451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07451_fast_pow_mod_ne_one

def fullRecordGapValue07452 : Nat := fullRecordGapCenterValue + 429698

theorem fullRecordGapTerm07452_eq_value :
    recordGapCenter + 429698 = fullRecordGapValue07452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07452 (fullRecordGapValue07452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07452_not_prime : ¬(recordGapCenter + 429698).Prime := by
  rw [fullRecordGapTerm07452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07452_fast_pow_mod_ne_one

def fullRecordGapValue07453 : Nat := fullRecordGapCenterValue + 429752

theorem fullRecordGapTerm07453_eq_value :
    recordGapCenter + 429752 = fullRecordGapValue07453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07453 (fullRecordGapValue07453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07453_not_prime : ¬(recordGapCenter + 429752).Prime := by
  rw [fullRecordGapTerm07453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07453_fast_pow_mod_ne_one

def fullRecordGapValue07454 : Nat := fullRecordGapCenterValue + 429782

theorem fullRecordGapTerm07454_eq_value :
    recordGapCenter + 429782 = fullRecordGapValue07454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07454 (fullRecordGapValue07454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07454_not_prime : ¬(recordGapCenter + 429782).Prime := by
  rw [fullRecordGapTerm07454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07454_fast_pow_mod_ne_one

def fullRecordGapValue07455 : Nat := fullRecordGapCenterValue + 429882

theorem fullRecordGapTerm07455_eq_value :
    recordGapCenter + 429882 = fullRecordGapValue07455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07455 (fullRecordGapValue07455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07455_not_prime : ¬(recordGapCenter + 429882).Prime := by
  rw [fullRecordGapTerm07455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07455_fast_pow_mod_ne_one

def fullRecordGapValue07456 : Nat := fullRecordGapCenterValue + 429978

theorem fullRecordGapTerm07456_eq_value :
    recordGapCenter + 429978 = fullRecordGapValue07456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07456 (fullRecordGapValue07456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07456_not_prime : ¬(recordGapCenter + 429978).Prime := by
  rw [fullRecordGapTerm07456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07456_fast_pow_mod_ne_one

def fullRecordGapValue07457 : Nat := fullRecordGapCenterValue + 430158

theorem fullRecordGapTerm07457_eq_value :
    recordGapCenter + 430158 = fullRecordGapValue07457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07457 (fullRecordGapValue07457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07457_not_prime : ¬(recordGapCenter + 430158).Prime := by
  rw [fullRecordGapTerm07457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07457_fast_pow_mod_ne_one

def fullRecordGapValue07458 : Nat := fullRecordGapCenterValue + 430242

theorem fullRecordGapTerm07458_eq_value :
    recordGapCenter + 430242 = fullRecordGapValue07458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07458 (fullRecordGapValue07458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07458_not_prime : ¬(recordGapCenter + 430242).Prime := by
  rw [fullRecordGapTerm07458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07458_fast_pow_mod_ne_one

def fullRecordGapValue07459 : Nat := fullRecordGapCenterValue + 430266

theorem fullRecordGapTerm07459_eq_value :
    recordGapCenter + 430266 = fullRecordGapValue07459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07459 (fullRecordGapValue07459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07459_not_prime : ¬(recordGapCenter + 430266).Prime := by
  rw [fullRecordGapTerm07459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07459_fast_pow_mod_ne_one

def fullRecordGapValue07460 : Nat := fullRecordGapCenterValue + 430278

theorem fullRecordGapTerm07460_eq_value :
    recordGapCenter + 430278 = fullRecordGapValue07460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07460 (fullRecordGapValue07460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07460_not_prime : ¬(recordGapCenter + 430278).Prime := by
  rw [fullRecordGapTerm07460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07460_fast_pow_mod_ne_one

def fullRecordGapValue07461 : Nat := fullRecordGapCenterValue + 430286

theorem fullRecordGapTerm07461_eq_value :
    recordGapCenter + 430286 = fullRecordGapValue07461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07461 (fullRecordGapValue07461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07461_not_prime : ¬(recordGapCenter + 430286).Prime := by
  rw [fullRecordGapTerm07461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07461_fast_pow_mod_ne_one

def fullRecordGapValue07462 : Nat := fullRecordGapCenterValue + 430328

theorem fullRecordGapTerm07462_eq_value :
    recordGapCenter + 430328 = fullRecordGapValue07462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07462 (fullRecordGapValue07462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07462_not_prime : ¬(recordGapCenter + 430328).Prime := by
  rw [fullRecordGapTerm07462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07462_fast_pow_mod_ne_one

def fullRecordGapValue07463 : Nat := fullRecordGapCenterValue + 430446

theorem fullRecordGapTerm07463_eq_value :
    recordGapCenter + 430446 = fullRecordGapValue07463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07463 (fullRecordGapValue07463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07463_not_prime : ¬(recordGapCenter + 430446).Prime := by
  rw [fullRecordGapTerm07463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07463_fast_pow_mod_ne_one

def fullRecordGapValue07464 : Nat := fullRecordGapCenterValue + 430662

theorem fullRecordGapTerm07464_eq_value :
    recordGapCenter + 430662 = fullRecordGapValue07464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07464 (fullRecordGapValue07464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07464_not_prime : ¬(recordGapCenter + 430662).Prime := by
  rw [fullRecordGapTerm07464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07464_fast_pow_mod_ne_one

def fullRecordGapValue07465 : Nat := fullRecordGapCenterValue + 430706

theorem fullRecordGapTerm07465_eq_value :
    recordGapCenter + 430706 = fullRecordGapValue07465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07465 (fullRecordGapValue07465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07465_not_prime : ¬(recordGapCenter + 430706).Prime := by
  rw [fullRecordGapTerm07465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07465_fast_pow_mod_ne_one

def fullRecordGapValue07466 : Nat := fullRecordGapCenterValue + 430796

theorem fullRecordGapTerm07466_eq_value :
    recordGapCenter + 430796 = fullRecordGapValue07466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07466 (fullRecordGapValue07466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07466_not_prime : ¬(recordGapCenter + 430796).Prime := by
  rw [fullRecordGapTerm07466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07466_fast_pow_mod_ne_one

def fullRecordGapValue07467 : Nat := fullRecordGapCenterValue + 430886

theorem fullRecordGapTerm07467_eq_value :
    recordGapCenter + 430886 = fullRecordGapValue07467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07467 (fullRecordGapValue07467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07467_not_prime : ¬(recordGapCenter + 430886).Prime := by
  rw [fullRecordGapTerm07467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07467_fast_pow_mod_ne_one

def fullRecordGapValue07468 : Nat := fullRecordGapCenterValue + 430922

theorem fullRecordGapTerm07468_eq_value :
    recordGapCenter + 430922 = fullRecordGapValue07468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07468 (fullRecordGapValue07468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07468_not_prime : ¬(recordGapCenter + 430922).Prime := by
  rw [fullRecordGapTerm07468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07468_fast_pow_mod_ne_one

def fullRecordGapValue07469 : Nat := fullRecordGapCenterValue + 430988

theorem fullRecordGapTerm07469_eq_value :
    recordGapCenter + 430988 = fullRecordGapValue07469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07469 (fullRecordGapValue07469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07469_not_prime : ¬(recordGapCenter + 430988).Prime := by
  rw [fullRecordGapTerm07469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07469_fast_pow_mod_ne_one

def fullRecordGapValue07470 : Nat := fullRecordGapCenterValue + 431058

theorem fullRecordGapTerm07470_eq_value :
    recordGapCenter + 431058 = fullRecordGapValue07470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07470 (fullRecordGapValue07470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07470_not_prime : ¬(recordGapCenter + 431058).Prime := by
  rw [fullRecordGapTerm07470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07470_fast_pow_mod_ne_one

def fullRecordGapValue07471 : Nat := fullRecordGapCenterValue + 431286

theorem fullRecordGapTerm07471_eq_value :
    recordGapCenter + 431286 = fullRecordGapValue07471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07471 (fullRecordGapValue07471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07471_not_prime : ¬(recordGapCenter + 431286).Prime := by
  rw [fullRecordGapTerm07471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07471_fast_pow_mod_ne_one

def fullRecordGapValue07472 : Nat := fullRecordGapCenterValue + 431322

theorem fullRecordGapTerm07472_eq_value :
    recordGapCenter + 431322 = fullRecordGapValue07472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07472 (fullRecordGapValue07472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07472_not_prime : ¬(recordGapCenter + 431322).Prime := by
  rw [fullRecordGapTerm07472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07472_fast_pow_mod_ne_one

def fullRecordGapValue07473 : Nat := fullRecordGapCenterValue + 431336

theorem fullRecordGapTerm07473_eq_value :
    recordGapCenter + 431336 = fullRecordGapValue07473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07473 (fullRecordGapValue07473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07473_not_prime : ¬(recordGapCenter + 431336).Prime := by
  rw [fullRecordGapTerm07473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07473_fast_pow_mod_ne_one

def fullRecordGapValue07474 : Nat := fullRecordGapCenterValue + 431502

theorem fullRecordGapTerm07474_eq_value :
    recordGapCenter + 431502 = fullRecordGapValue07474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07474 (fullRecordGapValue07474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07474_not_prime : ¬(recordGapCenter + 431502).Prime := by
  rw [fullRecordGapTerm07474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07474_fast_pow_mod_ne_one

def fullRecordGapValue07475 : Nat := fullRecordGapCenterValue + 431666

theorem fullRecordGapTerm07475_eq_value :
    recordGapCenter + 431666 = fullRecordGapValue07475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07475 (fullRecordGapValue07475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07475_not_prime : ¬(recordGapCenter + 431666).Prime := by
  rw [fullRecordGapTerm07475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07475_fast_pow_mod_ne_one

def fullRecordGapValue07476 : Nat := fullRecordGapCenterValue + 431672

theorem fullRecordGapTerm07476_eq_value :
    recordGapCenter + 431672 = fullRecordGapValue07476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07476 (fullRecordGapValue07476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07476_not_prime : ¬(recordGapCenter + 431672).Prime := by
  rw [fullRecordGapTerm07476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07476_fast_pow_mod_ne_one

def fullRecordGapValue07477 : Nat := fullRecordGapCenterValue + 431778

theorem fullRecordGapTerm07477_eq_value :
    recordGapCenter + 431778 = fullRecordGapValue07477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07477 (fullRecordGapValue07477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07477_not_prime : ¬(recordGapCenter + 431778).Prime := by
  rw [fullRecordGapTerm07477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07477_fast_pow_mod_ne_one

def fullRecordGapValue07478 : Nat := fullRecordGapCenterValue + 431798

theorem fullRecordGapTerm07478_eq_value :
    recordGapCenter + 431798 = fullRecordGapValue07478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07478 (fullRecordGapValue07478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07478_not_prime : ¬(recordGapCenter + 431798).Prime := by
  rw [fullRecordGapTerm07478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07478_fast_pow_mod_ne_one

def fullRecordGapValue07479 : Nat := fullRecordGapCenterValue + 431826

theorem fullRecordGapTerm07479_eq_value :
    recordGapCenter + 431826 = fullRecordGapValue07479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07479 (fullRecordGapValue07479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07479_not_prime : ¬(recordGapCenter + 431826).Prime := by
  rw [fullRecordGapTerm07479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07479_fast_pow_mod_ne_one

def fullRecordGapValue07480 : Nat := fullRecordGapCenterValue + 432008

theorem fullRecordGapTerm07480_eq_value :
    recordGapCenter + 432008 = fullRecordGapValue07480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07480 (fullRecordGapValue07480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07480_not_prime : ¬(recordGapCenter + 432008).Prime := by
  rw [fullRecordGapTerm07480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07480_fast_pow_mod_ne_one

def fullRecordGapValue07481 : Nat := fullRecordGapCenterValue + 432392

theorem fullRecordGapTerm07481_eq_value :
    recordGapCenter + 432392 = fullRecordGapValue07481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07481 (fullRecordGapValue07481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07481_not_prime : ¬(recordGapCenter + 432392).Prime := by
  rw [fullRecordGapTerm07481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07481_fast_pow_mod_ne_one

def fullRecordGapValue07482 : Nat := fullRecordGapCenterValue + 432462

theorem fullRecordGapTerm07482_eq_value :
    recordGapCenter + 432462 = fullRecordGapValue07482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07482 (fullRecordGapValue07482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07482_not_prime : ¬(recordGapCenter + 432462).Prime := by
  rw [fullRecordGapTerm07482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07482_fast_pow_mod_ne_one

def fullRecordGapValue07483 : Nat := fullRecordGapCenterValue + 432518

theorem fullRecordGapTerm07483_eq_value :
    recordGapCenter + 432518 = fullRecordGapValue07483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07483 (fullRecordGapValue07483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07483_not_prime : ¬(recordGapCenter + 432518).Prime := by
  rw [fullRecordGapTerm07483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07483_fast_pow_mod_ne_one

def fullRecordGapValue07484 : Nat := fullRecordGapCenterValue + 432716

theorem fullRecordGapTerm07484_eq_value :
    recordGapCenter + 432716 = fullRecordGapValue07484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07484 (fullRecordGapValue07484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07484_not_prime : ¬(recordGapCenter + 432716).Prime := by
  rw [fullRecordGapTerm07484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07484_fast_pow_mod_ne_one

def fullRecordGapValue07485 : Nat := fullRecordGapCenterValue + 432728

theorem fullRecordGapTerm07485_eq_value :
    recordGapCenter + 432728 = fullRecordGapValue07485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07485 (fullRecordGapValue07485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07485_not_prime : ¬(recordGapCenter + 432728).Prime := by
  rw [fullRecordGapTerm07485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07485_fast_pow_mod_ne_one

def fullRecordGapValue07486 : Nat := fullRecordGapCenterValue + 432902

theorem fullRecordGapTerm07486_eq_value :
    recordGapCenter + 432902 = fullRecordGapValue07486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07486 (fullRecordGapValue07486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07486_not_prime : ¬(recordGapCenter + 432902).Prime := by
  rw [fullRecordGapTerm07486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07486_fast_pow_mod_ne_one

def fullRecordGapValue07487 : Nat := fullRecordGapCenterValue + 432962

theorem fullRecordGapTerm07487_eq_value :
    recordGapCenter + 432962 = fullRecordGapValue07487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07487 (fullRecordGapValue07487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07487_not_prime : ¬(recordGapCenter + 432962).Prime := by
  rw [fullRecordGapTerm07487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07487_fast_pow_mod_ne_one

def fullRecordGapValue07488 : Nat := fullRecordGapCenterValue + 432968

theorem fullRecordGapTerm07488_eq_value :
    recordGapCenter + 432968 = fullRecordGapValue07488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07488 (fullRecordGapValue07488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07488_not_prime : ¬(recordGapCenter + 432968).Prime := by
  rw [fullRecordGapTerm07488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07488_fast_pow_mod_ne_one

def fullRecordGapValue07489 : Nat := fullRecordGapCenterValue + 433038

theorem fullRecordGapTerm07489_eq_value :
    recordGapCenter + 433038 = fullRecordGapValue07489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07489 (fullRecordGapValue07489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07489_not_prime : ¬(recordGapCenter + 433038).Prime := by
  rw [fullRecordGapTerm07489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07489_fast_pow_mod_ne_one

def fullRecordGapValue07490 : Nat := fullRecordGapCenterValue + 433052

theorem fullRecordGapTerm07490_eq_value :
    recordGapCenter + 433052 = fullRecordGapValue07490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07490 (fullRecordGapValue07490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07490_not_prime : ¬(recordGapCenter + 433052).Prime := by
  rw [fullRecordGapTerm07490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07490_fast_pow_mod_ne_one

def fullRecordGapValue07491 : Nat := fullRecordGapCenterValue + 433106

theorem fullRecordGapTerm07491_eq_value :
    recordGapCenter + 433106 = fullRecordGapValue07491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07491 (fullRecordGapValue07491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07491_not_prime : ¬(recordGapCenter + 433106).Prime := by
  rw [fullRecordGapTerm07491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07491_fast_pow_mod_ne_one

def fullRecordGapValue07492 : Nat := fullRecordGapCenterValue + 433148

theorem fullRecordGapTerm07492_eq_value :
    recordGapCenter + 433148 = fullRecordGapValue07492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07492 (fullRecordGapValue07492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07492_not_prime : ¬(recordGapCenter + 433148).Prime := by
  rw [fullRecordGapTerm07492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07492_fast_pow_mod_ne_one

def fullRecordGapValue07493 : Nat := fullRecordGapCenterValue + 433190

theorem fullRecordGapTerm07493_eq_value :
    recordGapCenter + 433190 = fullRecordGapValue07493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07493 (fullRecordGapValue07493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07493_not_prime : ¬(recordGapCenter + 433190).Prime := by
  rw [fullRecordGapTerm07493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07493_fast_pow_mod_ne_one

def fullRecordGapValue07494 : Nat := fullRecordGapCenterValue + 433298

theorem fullRecordGapTerm07494_eq_value :
    recordGapCenter + 433298 = fullRecordGapValue07494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07494 (fullRecordGapValue07494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07494_not_prime : ¬(recordGapCenter + 433298).Prime := by
  rw [fullRecordGapTerm07494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07494_fast_pow_mod_ne_one

def fullRecordGapValue07495 : Nat := fullRecordGapCenterValue + 433406

theorem fullRecordGapTerm07495_eq_value :
    recordGapCenter + 433406 = fullRecordGapValue07495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07495 (fullRecordGapValue07495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07495_not_prime : ¬(recordGapCenter + 433406).Prime := by
  rw [fullRecordGapTerm07495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07495_fast_pow_mod_ne_one

def fullRecordGapValue07496 : Nat := fullRecordGapCenterValue + 433626

theorem fullRecordGapTerm07496_eq_value :
    recordGapCenter + 433626 = fullRecordGapValue07496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07496 (fullRecordGapValue07496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07496_not_prime : ¬(recordGapCenter + 433626).Prime := by
  rw [fullRecordGapTerm07496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07496_fast_pow_mod_ne_one

def fullRecordGapValue07497 : Nat := fullRecordGapCenterValue + 433658

theorem fullRecordGapTerm07497_eq_value :
    recordGapCenter + 433658 = fullRecordGapValue07497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07497 (fullRecordGapValue07497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07497_not_prime : ¬(recordGapCenter + 433658).Prime := by
  rw [fullRecordGapTerm07497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07497_fast_pow_mod_ne_one

def fullRecordGapValue07498 : Nat := fullRecordGapCenterValue + 433662

theorem fullRecordGapTerm07498_eq_value :
    recordGapCenter + 433662 = fullRecordGapValue07498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07498 (fullRecordGapValue07498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07498_not_prime : ¬(recordGapCenter + 433662).Prime := by
  rw [fullRecordGapTerm07498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07498_fast_pow_mod_ne_one

def fullRecordGapValue07499 : Nat := fullRecordGapCenterValue + 433718

theorem fullRecordGapTerm07499_eq_value :
    recordGapCenter + 433718 = fullRecordGapValue07499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07499 (fullRecordGapValue07499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07499_not_prime : ¬(recordGapCenter + 433718).Prime := by
  rw [fullRecordGapTerm07499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07499_fast_pow_mod_ne_one

def fullRecordGapValue07500 : Nat := fullRecordGapCenterValue + 433722

theorem fullRecordGapTerm07500_eq_value :
    recordGapCenter + 433722 = fullRecordGapValue07500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07500 (fullRecordGapValue07500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07500_not_prime : ¬(recordGapCenter + 433722).Prime := by
  rw [fullRecordGapTerm07500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07500_fast_pow_mod_ne_one

def fullRecordGapValue07501 : Nat := fullRecordGapCenterValue + 433802

theorem fullRecordGapTerm07501_eq_value :
    recordGapCenter + 433802 = fullRecordGapValue07501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07501 (fullRecordGapValue07501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07501_not_prime : ¬(recordGapCenter + 433802).Prime := by
  rw [fullRecordGapTerm07501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07501_fast_pow_mod_ne_one

def fullRecordGapValue07502 : Nat := fullRecordGapCenterValue + 433910

theorem fullRecordGapTerm07502_eq_value :
    recordGapCenter + 433910 = fullRecordGapValue07502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07502 (fullRecordGapValue07502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07502_not_prime : ¬(recordGapCenter + 433910).Prime := by
  rw [fullRecordGapTerm07502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07502_fast_pow_mod_ne_one

def fullRecordGapValue07503 : Nat := fullRecordGapCenterValue + 433970

theorem fullRecordGapTerm07503_eq_value :
    recordGapCenter + 433970 = fullRecordGapValue07503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07503 (fullRecordGapValue07503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07503_not_prime : ¬(recordGapCenter + 433970).Prime := by
  rw [fullRecordGapTerm07503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07503_fast_pow_mod_ne_one

def fullRecordGapValue07504 : Nat := fullRecordGapCenterValue + 434022

theorem fullRecordGapTerm07504_eq_value :
    recordGapCenter + 434022 = fullRecordGapValue07504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07504 (fullRecordGapValue07504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07504_not_prime : ¬(recordGapCenter + 434022).Prime := by
  rw [fullRecordGapTerm07504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07504_fast_pow_mod_ne_one

def fullRecordGapValue07505 : Nat := fullRecordGapCenterValue + 434046

theorem fullRecordGapTerm07505_eq_value :
    recordGapCenter + 434046 = fullRecordGapValue07505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07505 (fullRecordGapValue07505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07505_not_prime : ¬(recordGapCenter + 434046).Prime := by
  rw [fullRecordGapTerm07505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07505_fast_pow_mod_ne_one

def fullRecordGapValue07506 : Nat := fullRecordGapCenterValue + 434162

theorem fullRecordGapTerm07506_eq_value :
    recordGapCenter + 434162 = fullRecordGapValue07506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07506 (fullRecordGapValue07506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07506_not_prime : ¬(recordGapCenter + 434162).Prime := by
  rw [fullRecordGapTerm07506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07506_fast_pow_mod_ne_one

def fullRecordGapValue07507 : Nat := fullRecordGapCenterValue + 434222

theorem fullRecordGapTerm07507_eq_value :
    recordGapCenter + 434222 = fullRecordGapValue07507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07507 (fullRecordGapValue07507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07507_not_prime : ¬(recordGapCenter + 434222).Prime := by
  rw [fullRecordGapTerm07507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07507_fast_pow_mod_ne_one

def fullRecordGapValue07508 : Nat := fullRecordGapCenterValue + 434270

theorem fullRecordGapTerm07508_eq_value :
    recordGapCenter + 434270 = fullRecordGapValue07508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07508 (fullRecordGapValue07508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07508_not_prime : ¬(recordGapCenter + 434270).Prime := by
  rw [fullRecordGapTerm07508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07508_fast_pow_mod_ne_one

def fullRecordGapValue07509 : Nat := fullRecordGapCenterValue + 434438

theorem fullRecordGapTerm07509_eq_value :
    recordGapCenter + 434438 = fullRecordGapValue07509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07509 (fullRecordGapValue07509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07509_not_prime : ¬(recordGapCenter + 434438).Prime := by
  rw [fullRecordGapTerm07509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07509_fast_pow_mod_ne_one

def fullRecordGapValue07510 : Nat := fullRecordGapCenterValue + 434570

theorem fullRecordGapTerm07510_eq_value :
    recordGapCenter + 434570 = fullRecordGapValue07510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07510 (fullRecordGapValue07510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07510_not_prime : ¬(recordGapCenter + 434570).Prime := by
  rw [fullRecordGapTerm07510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07510_fast_pow_mod_ne_one

def fullRecordGapValue07511 : Nat := fullRecordGapCenterValue + 434702

theorem fullRecordGapTerm07511_eq_value :
    recordGapCenter + 434702 = fullRecordGapValue07511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07511 (fullRecordGapValue07511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07511_not_prime : ¬(recordGapCenter + 434702).Prime := by
  rw [fullRecordGapTerm07511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07511_fast_pow_mod_ne_one

def fullRecordGapValue07512 : Nat := fullRecordGapCenterValue + 434802

theorem fullRecordGapTerm07512_eq_value :
    recordGapCenter + 434802 = fullRecordGapValue07512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07512 (fullRecordGapValue07512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07512_not_prime : ¬(recordGapCenter + 434802).Prime := by
  rw [fullRecordGapTerm07512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07512_fast_pow_mod_ne_one

def fullRecordGapValue07513 : Nat := fullRecordGapCenterValue + 434822

theorem fullRecordGapTerm07513_eq_value :
    recordGapCenter + 434822 = fullRecordGapValue07513 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07513_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07513 (fullRecordGapValue07513 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07513_not_prime : ¬(recordGapCenter + 434822).Prime := by
  rw [fullRecordGapTerm07513_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07513, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07513_fast_pow_mod_ne_one

def fullRecordGapValue07514 : Nat := fullRecordGapCenterValue + 434886

theorem fullRecordGapTerm07514_eq_value :
    recordGapCenter + 434886 = fullRecordGapValue07514 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07514_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07514 (fullRecordGapValue07514 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07514_not_prime : ¬(recordGapCenter + 434886).Prime := by
  rw [fullRecordGapTerm07514_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07514, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07514_fast_pow_mod_ne_one

def fullRecordGapValue07515 : Nat := fullRecordGapCenterValue + 435146

theorem fullRecordGapTerm07515_eq_value :
    recordGapCenter + 435146 = fullRecordGapValue07515 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07515_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07515 (fullRecordGapValue07515 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07515_not_prime : ¬(recordGapCenter + 435146).Prime := by
  rw [fullRecordGapTerm07515_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07515, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07515_fast_pow_mod_ne_one

def fullRecordGapValue07516 : Nat := fullRecordGapCenterValue + 435170

theorem fullRecordGapTerm07516_eq_value :
    recordGapCenter + 435170 = fullRecordGapValue07516 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07516_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07516 (fullRecordGapValue07516 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07516_not_prime : ¬(recordGapCenter + 435170).Prime := by
  rw [fullRecordGapTerm07516_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07516, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07516_fast_pow_mod_ne_one

def fullRecordGapValue07517 : Nat := fullRecordGapCenterValue + 435282

theorem fullRecordGapTerm07517_eq_value :
    recordGapCenter + 435282 = fullRecordGapValue07517 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07517_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07517 (fullRecordGapValue07517 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07517_not_prime : ¬(recordGapCenter + 435282).Prime := by
  rw [fullRecordGapTerm07517_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07517, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07517_fast_pow_mod_ne_one

def fullRecordGapValue07518 : Nat := fullRecordGapCenterValue + 435362

theorem fullRecordGapTerm07518_eq_value :
    recordGapCenter + 435362 = fullRecordGapValue07518 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07518_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07518 (fullRecordGapValue07518 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07518_not_prime : ¬(recordGapCenter + 435362).Prime := by
  rw [fullRecordGapTerm07518_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07518, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07518_fast_pow_mod_ne_one

def fullRecordGapValue07519 : Nat := fullRecordGapCenterValue + 435542

theorem fullRecordGapTerm07519_eq_value :
    recordGapCenter + 435542 = fullRecordGapValue07519 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07519_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07519 (fullRecordGapValue07519 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07519_not_prime : ¬(recordGapCenter + 435542).Prime := by
  rw [fullRecordGapTerm07519_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07519, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07519_fast_pow_mod_ne_one

def fullRecordGapValue07520 : Nat := fullRecordGapCenterValue + 435572

theorem fullRecordGapTerm07520_eq_value :
    recordGapCenter + 435572 = fullRecordGapValue07520 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07520_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07520 (fullRecordGapValue07520 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07520_not_prime : ¬(recordGapCenter + 435572).Prime := by
  rw [fullRecordGapTerm07520_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07520, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07520_fast_pow_mod_ne_one

def fullRecordGapValue07521 : Nat := fullRecordGapCenterValue + 435668

theorem fullRecordGapTerm07521_eq_value :
    recordGapCenter + 435668 = fullRecordGapValue07521 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07521_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07521 (fullRecordGapValue07521 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07521_not_prime : ¬(recordGapCenter + 435668).Prime := by
  rw [fullRecordGapTerm07521_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07521, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07521_fast_pow_mod_ne_one

def fullRecordGapValue07522 : Nat := fullRecordGapCenterValue + 435692

theorem fullRecordGapTerm07522_eq_value :
    recordGapCenter + 435692 = fullRecordGapValue07522 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07522_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07522 (fullRecordGapValue07522 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07522_not_prime : ¬(recordGapCenter + 435692).Prime := by
  rw [fullRecordGapTerm07522_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07522, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07522_fast_pow_mod_ne_one

def fullRecordGapValue07523 : Nat := fullRecordGapCenterValue + 435716

theorem fullRecordGapTerm07523_eq_value :
    recordGapCenter + 435716 = fullRecordGapValue07523 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07523_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07523 (fullRecordGapValue07523 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07523_not_prime : ¬(recordGapCenter + 435716).Prime := by
  rw [fullRecordGapTerm07523_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07523, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07523_fast_pow_mod_ne_one

def fullRecordGapValue07524 : Nat := fullRecordGapCenterValue + 435738

theorem fullRecordGapTerm07524_eq_value :
    recordGapCenter + 435738 = fullRecordGapValue07524 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07524_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07524 (fullRecordGapValue07524 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07524_not_prime : ¬(recordGapCenter + 435738).Prime := by
  rw [fullRecordGapTerm07524_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07524, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07524_fast_pow_mod_ne_one

def fullRecordGapValue07525 : Nat := fullRecordGapCenterValue + 435752

theorem fullRecordGapTerm07525_eq_value :
    recordGapCenter + 435752 = fullRecordGapValue07525 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07525_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07525 (fullRecordGapValue07525 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07525_not_prime : ¬(recordGapCenter + 435752).Prime := by
  rw [fullRecordGapTerm07525_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07525, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07525_fast_pow_mod_ne_one

def fullRecordGapValue07526 : Nat := fullRecordGapCenterValue + 435818

theorem fullRecordGapTerm07526_eq_value :
    recordGapCenter + 435818 = fullRecordGapValue07526 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07526_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07526 (fullRecordGapValue07526 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07526_not_prime : ¬(recordGapCenter + 435818).Prime := by
  rw [fullRecordGapTerm07526_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07526, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07526_fast_pow_mod_ne_one

def fullRecordGapValue07527 : Nat := fullRecordGapCenterValue + 435836

theorem fullRecordGapTerm07527_eq_value :
    recordGapCenter + 435836 = fullRecordGapValue07527 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07527_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07527 (fullRecordGapValue07527 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07527_not_prime : ¬(recordGapCenter + 435836).Prime := by
  rw [fullRecordGapTerm07527_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07527, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07527_fast_pow_mod_ne_one

def fullRecordGapValue07528 : Nat := fullRecordGapCenterValue + 435866

theorem fullRecordGapTerm07528_eq_value :
    recordGapCenter + 435866 = fullRecordGapValue07528 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07528_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07528 (fullRecordGapValue07528 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07528_not_prime : ¬(recordGapCenter + 435866).Prime := by
  rw [fullRecordGapTerm07528_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07528, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07528_fast_pow_mod_ne_one

def fullRecordGapValue07529 : Nat := fullRecordGapCenterValue + 436026

theorem fullRecordGapTerm07529_eq_value :
    recordGapCenter + 436026 = fullRecordGapValue07529 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07529_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07529 (fullRecordGapValue07529 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07529_not_prime : ¬(recordGapCenter + 436026).Prime := by
  rw [fullRecordGapTerm07529_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07529, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07529_fast_pow_mod_ne_one

def fullRecordGapValue07530 : Nat := fullRecordGapCenterValue + 436052

theorem fullRecordGapTerm07530_eq_value :
    recordGapCenter + 436052 = fullRecordGapValue07530 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07530_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07530 (fullRecordGapValue07530 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07530_not_prime : ¬(recordGapCenter + 436052).Prime := by
  rw [fullRecordGapTerm07530_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07530, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07530_fast_pow_mod_ne_one

def fullRecordGapValue07531 : Nat := fullRecordGapCenterValue + 436070

theorem fullRecordGapTerm07531_eq_value :
    recordGapCenter + 436070 = fullRecordGapValue07531 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07531_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07531 (fullRecordGapValue07531 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07531_not_prime : ¬(recordGapCenter + 436070).Prime := by
  rw [fullRecordGapTerm07531_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07531, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07531_fast_pow_mod_ne_one

def fullRecordGapValue07532 : Nat := fullRecordGapCenterValue + 436166

theorem fullRecordGapTerm07532_eq_value :
    recordGapCenter + 436166 = fullRecordGapValue07532 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07532_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07532 (fullRecordGapValue07532 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07532_not_prime : ¬(recordGapCenter + 436166).Prime := by
  rw [fullRecordGapTerm07532_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07532, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07532_fast_pow_mod_ne_one

def fullRecordGapValue07533 : Nat := fullRecordGapCenterValue + 436242

theorem fullRecordGapTerm07533_eq_value :
    recordGapCenter + 436242 = fullRecordGapValue07533 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07533_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07533 (fullRecordGapValue07533 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07533_not_prime : ¬(recordGapCenter + 436242).Prime := by
  rw [fullRecordGapTerm07533_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07533, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07533_fast_pow_mod_ne_one

def fullRecordGapValue07534 : Nat := fullRecordGapCenterValue + 436298

theorem fullRecordGapTerm07534_eq_value :
    recordGapCenter + 436298 = fullRecordGapValue07534 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07534_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07534 (fullRecordGapValue07534 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07534_not_prime : ¬(recordGapCenter + 436298).Prime := by
  rw [fullRecordGapTerm07534_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07534, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07534_fast_pow_mod_ne_one

def fullRecordGapValue07535 : Nat := fullRecordGapCenterValue + 436466

theorem fullRecordGapTerm07535_eq_value :
    recordGapCenter + 436466 = fullRecordGapValue07535 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07535_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07535 (fullRecordGapValue07535 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07535_not_prime : ¬(recordGapCenter + 436466).Prime := by
  rw [fullRecordGapTerm07535_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07535, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07535_fast_pow_mod_ne_one

def fullRecordGapValue07536 : Nat := fullRecordGapCenterValue + 436472

theorem fullRecordGapTerm07536_eq_value :
    recordGapCenter + 436472 = fullRecordGapValue07536 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07536_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07536 (fullRecordGapValue07536 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07536_not_prime : ¬(recordGapCenter + 436472).Prime := by
  rw [fullRecordGapTerm07536_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07536, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07536_fast_pow_mod_ne_one

def fullRecordGapValue07537 : Nat := fullRecordGapCenterValue + 436490

theorem fullRecordGapTerm07537_eq_value :
    recordGapCenter + 436490 = fullRecordGapValue07537 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07537_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07537 (fullRecordGapValue07537 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07537_not_prime : ¬(recordGapCenter + 436490).Prime := by
  rw [fullRecordGapTerm07537_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07537, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07537_fast_pow_mod_ne_one

def fullRecordGapValue07538 : Nat := fullRecordGapCenterValue + 436532

theorem fullRecordGapTerm07538_eq_value :
    recordGapCenter + 436532 = fullRecordGapValue07538 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07538_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07538 (fullRecordGapValue07538 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07538_not_prime : ¬(recordGapCenter + 436532).Prime := by
  rw [fullRecordGapTerm07538_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07538, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07538_fast_pow_mod_ne_one

def fullRecordGapValue07539 : Nat := fullRecordGapCenterValue + 436556

theorem fullRecordGapTerm07539_eq_value :
    recordGapCenter + 436556 = fullRecordGapValue07539 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07539_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07539 (fullRecordGapValue07539 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07539_not_prime : ¬(recordGapCenter + 436556).Prime := by
  rw [fullRecordGapTerm07539_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07539, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07539_fast_pow_mod_ne_one

def fullRecordGapValue07540 : Nat := fullRecordGapCenterValue + 436578

theorem fullRecordGapTerm07540_eq_value :
    recordGapCenter + 436578 = fullRecordGapValue07540 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07540_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07540 (fullRecordGapValue07540 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07540_not_prime : ¬(recordGapCenter + 436578).Prime := by
  rw [fullRecordGapTerm07540_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07540, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07540_fast_pow_mod_ne_one

def fullRecordGapValue07541 : Nat := fullRecordGapCenterValue + 436602

theorem fullRecordGapTerm07541_eq_value :
    recordGapCenter + 436602 = fullRecordGapValue07541 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07541_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07541 (fullRecordGapValue07541 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07541_not_prime : ¬(recordGapCenter + 436602).Prime := by
  rw [fullRecordGapTerm07541_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07541, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07541_fast_pow_mod_ne_one

def fullRecordGapValue07542 : Nat := fullRecordGapCenterValue + 436616

theorem fullRecordGapTerm07542_eq_value :
    recordGapCenter + 436616 = fullRecordGapValue07542 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07542_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07542 (fullRecordGapValue07542 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07542_not_prime : ¬(recordGapCenter + 436616).Prime := by
  rw [fullRecordGapTerm07542_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07542, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07542_fast_pow_mod_ne_one

def fullRecordGapValue07543 : Nat := fullRecordGapCenterValue + 436782

theorem fullRecordGapTerm07543_eq_value :
    recordGapCenter + 436782 = fullRecordGapValue07543 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07543_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07543 (fullRecordGapValue07543 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07543_not_prime : ¬(recordGapCenter + 436782).Prime := by
  rw [fullRecordGapTerm07543_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07543, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07543_fast_pow_mod_ne_one

def fullRecordGapValue07544 : Nat := fullRecordGapCenterValue + 436808

theorem fullRecordGapTerm07544_eq_value :
    recordGapCenter + 436808 = fullRecordGapValue07544 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07544_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07544 (fullRecordGapValue07544 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07544_not_prime : ¬(recordGapCenter + 436808).Prime := by
  rw [fullRecordGapTerm07544_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07544, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07544_fast_pow_mod_ne_one

def fullRecordGapValue07545 : Nat := fullRecordGapCenterValue + 436838

theorem fullRecordGapTerm07545_eq_value :
    recordGapCenter + 436838 = fullRecordGapValue07545 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07545_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07545 (fullRecordGapValue07545 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07545_not_prime : ¬(recordGapCenter + 436838).Prime := by
  rw [fullRecordGapTerm07545_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07545, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07545_fast_pow_mod_ne_one

def fullRecordGapValue07546 : Nat := fullRecordGapCenterValue + 437012

theorem fullRecordGapTerm07546_eq_value :
    recordGapCenter + 437012 = fullRecordGapValue07546 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07546_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07546 (fullRecordGapValue07546 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07546_not_prime : ¬(recordGapCenter + 437012).Prime := by
  rw [fullRecordGapTerm07546_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07546, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07546_fast_pow_mod_ne_one

def fullRecordGapValue07547 : Nat := fullRecordGapCenterValue + 437042

theorem fullRecordGapTerm07547_eq_value :
    recordGapCenter + 437042 = fullRecordGapValue07547 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07547_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07547 (fullRecordGapValue07547 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07547_not_prime : ¬(recordGapCenter + 437042).Prime := by
  rw [fullRecordGapTerm07547_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07547, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07547_fast_pow_mod_ne_one

def fullRecordGapValue07548 : Nat := fullRecordGapCenterValue + 437102

theorem fullRecordGapTerm07548_eq_value :
    recordGapCenter + 437102 = fullRecordGapValue07548 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07548_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07548 (fullRecordGapValue07548 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07548_not_prime : ¬(recordGapCenter + 437102).Prime := by
  rw [fullRecordGapTerm07548_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07548, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07548_fast_pow_mod_ne_one

def fullRecordGapValue07549 : Nat := fullRecordGapCenterValue + 437252

theorem fullRecordGapTerm07549_eq_value :
    recordGapCenter + 437252 = fullRecordGapValue07549 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07549_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07549 (fullRecordGapValue07549 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07549_not_prime : ¬(recordGapCenter + 437252).Prime := by
  rw [fullRecordGapTerm07549_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07549, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07549_fast_pow_mod_ne_one

def fullRecordGapValue07550 : Nat := fullRecordGapCenterValue + 437336

theorem fullRecordGapTerm07550_eq_value :
    recordGapCenter + 437336 = fullRecordGapValue07550 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07550_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07550 (fullRecordGapValue07550 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07550_not_prime : ¬(recordGapCenter + 437336).Prime := by
  rw [fullRecordGapTerm07550_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07550, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07550_fast_pow_mod_ne_one

def fullRecordGapValue07551 : Nat := fullRecordGapCenterValue + 437406

theorem fullRecordGapTerm07551_eq_value :
    recordGapCenter + 437406 = fullRecordGapValue07551 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07551_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07551 (fullRecordGapValue07551 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07551_not_prime : ¬(recordGapCenter + 437406).Prime := by
  rw [fullRecordGapTerm07551_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07551, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07551_fast_pow_mod_ne_one

def fullRecordGapValue07552 : Nat := fullRecordGapCenterValue + 437432

theorem fullRecordGapTerm07552_eq_value :
    recordGapCenter + 437432 = fullRecordGapValue07552 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07552_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07552 (fullRecordGapValue07552 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07552_not_prime : ¬(recordGapCenter + 437432).Prime := by
  rw [fullRecordGapTerm07552_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07552, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07552_fast_pow_mod_ne_one

def fullRecordGapValue07553 : Nat := fullRecordGapCenterValue + 437442

theorem fullRecordGapTerm07553_eq_value :
    recordGapCenter + 437442 = fullRecordGapValue07553 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07553_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07553 (fullRecordGapValue07553 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07553_not_prime : ¬(recordGapCenter + 437442).Prime := by
  rw [fullRecordGapTerm07553_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07553, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07553_fast_pow_mod_ne_one

def fullRecordGapValue07554 : Nat := fullRecordGapCenterValue + 437498

theorem fullRecordGapTerm07554_eq_value :
    recordGapCenter + 437498 = fullRecordGapValue07554 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07554_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07554 (fullRecordGapValue07554 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07554_not_prime : ¬(recordGapCenter + 437498).Prime := by
  rw [fullRecordGapTerm07554_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07554, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07554_fast_pow_mod_ne_one

def fullRecordGapValue07555 : Nat := fullRecordGapCenterValue + 437516

theorem fullRecordGapTerm07555_eq_value :
    recordGapCenter + 437516 = fullRecordGapValue07555 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07555_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07555 (fullRecordGapValue07555 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07555_not_prime : ¬(recordGapCenter + 437516).Prime := by
  rw [fullRecordGapTerm07555_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07555, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07555_fast_pow_mod_ne_one

def fullRecordGapValue07556 : Nat := fullRecordGapCenterValue + 437538

theorem fullRecordGapTerm07556_eq_value :
    recordGapCenter + 437538 = fullRecordGapValue07556 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07556_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07556 (fullRecordGapValue07556 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07556_not_prime : ¬(recordGapCenter + 437538).Prime := by
  rw [fullRecordGapTerm07556_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07556, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07556_fast_pow_mod_ne_one

def fullRecordGapValue07557 : Nat := fullRecordGapCenterValue + 437588

theorem fullRecordGapTerm07557_eq_value :
    recordGapCenter + 437588 = fullRecordGapValue07557 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07557_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07557 (fullRecordGapValue07557 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07557_not_prime : ¬(recordGapCenter + 437588).Prime := by
  rw [fullRecordGapTerm07557_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07557, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07557_fast_pow_mod_ne_one

def fullRecordGapValue07558 : Nat := fullRecordGapCenterValue + 437678

theorem fullRecordGapTerm07558_eq_value :
    recordGapCenter + 437678 = fullRecordGapValue07558 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07558_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07558 (fullRecordGapValue07558 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07558_not_prime : ¬(recordGapCenter + 437678).Prime := by
  rw [fullRecordGapTerm07558_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07558, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07558_fast_pow_mod_ne_one

def fullRecordGapValue07559 : Nat := fullRecordGapCenterValue + 437732

theorem fullRecordGapTerm07559_eq_value :
    recordGapCenter + 437732 = fullRecordGapValue07559 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07559_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07559 (fullRecordGapValue07559 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07559_not_prime : ¬(recordGapCenter + 437732).Prime := by
  rw [fullRecordGapTerm07559_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07559, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07559_fast_pow_mod_ne_one

def fullRecordGapValue07560 : Nat := fullRecordGapCenterValue + 437768

theorem fullRecordGapTerm07560_eq_value :
    recordGapCenter + 437768 = fullRecordGapValue07560 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07560_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07560 (fullRecordGapValue07560 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07560_not_prime : ¬(recordGapCenter + 437768).Prime := by
  rw [fullRecordGapTerm07560_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07560, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07560_fast_pow_mod_ne_one

def fullRecordGapValue07561 : Nat := fullRecordGapCenterValue + 437816

theorem fullRecordGapTerm07561_eq_value :
    recordGapCenter + 437816 = fullRecordGapValue07561 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07561_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07561 (fullRecordGapValue07561 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07561_not_prime : ¬(recordGapCenter + 437816).Prime := by
  rw [fullRecordGapTerm07561_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07561, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07561_fast_pow_mod_ne_one

def fullRecordGapValue07562 : Nat := fullRecordGapCenterValue + 437838

theorem fullRecordGapTerm07562_eq_value :
    recordGapCenter + 437838 = fullRecordGapValue07562 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07562_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07562 (fullRecordGapValue07562 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07562_not_prime : ¬(recordGapCenter + 437838).Prime := by
  rw [fullRecordGapTerm07562_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07562, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07562_fast_pow_mod_ne_one

def fullRecordGapValue07563 : Nat := fullRecordGapCenterValue + 437876

theorem fullRecordGapTerm07563_eq_value :
    recordGapCenter + 437876 = fullRecordGapValue07563 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07563_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07563 (fullRecordGapValue07563 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07563_not_prime : ¬(recordGapCenter + 437876).Prime := by
  rw [fullRecordGapTerm07563_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07563, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07563_fast_pow_mod_ne_one

def fullRecordGapValue07564 : Nat := fullRecordGapCenterValue + 438182

theorem fullRecordGapTerm07564_eq_value :
    recordGapCenter + 438182 = fullRecordGapValue07564 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07564_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07564 (fullRecordGapValue07564 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07564_not_prime : ¬(recordGapCenter + 438182).Prime := by
  rw [fullRecordGapTerm07564_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07564, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07564_fast_pow_mod_ne_one

def fullRecordGapValue07565 : Nat := fullRecordGapCenterValue + 438188

theorem fullRecordGapTerm07565_eq_value :
    recordGapCenter + 438188 = fullRecordGapValue07565 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07565_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07565 (fullRecordGapValue07565 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07565_not_prime : ¬(recordGapCenter + 438188).Prime := by
  rw [fullRecordGapTerm07565_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07565, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07565_fast_pow_mod_ne_one

def fullRecordGapValue07566 : Nat := fullRecordGapCenterValue + 438222

theorem fullRecordGapTerm07566_eq_value :
    recordGapCenter + 438222 = fullRecordGapValue07566 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07566_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07566 (fullRecordGapValue07566 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07566_not_prime : ¬(recordGapCenter + 438222).Prime := by
  rw [fullRecordGapTerm07566_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07566, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07566_fast_pow_mod_ne_one

def fullRecordGapValue07567 : Nat := fullRecordGapCenterValue + 438296

theorem fullRecordGapTerm07567_eq_value :
    recordGapCenter + 438296 = fullRecordGapValue07567 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07567_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07567 (fullRecordGapValue07567 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07567_not_prime : ¬(recordGapCenter + 438296).Prime := by
  rw [fullRecordGapTerm07567_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07567, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07567_fast_pow_mod_ne_one

def fullRecordGapValue07568 : Nat := fullRecordGapCenterValue + 438356

theorem fullRecordGapTerm07568_eq_value :
    recordGapCenter + 438356 = fullRecordGapValue07568 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07568_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07568 (fullRecordGapValue07568 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07568_not_prime : ¬(recordGapCenter + 438356).Prime := by
  rw [fullRecordGapTerm07568_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07568, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07568_fast_pow_mod_ne_one

def fullRecordGapValue07569 : Nat := fullRecordGapCenterValue + 438378

theorem fullRecordGapTerm07569_eq_value :
    recordGapCenter + 438378 = fullRecordGapValue07569 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07569_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07569 (fullRecordGapValue07569 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07569_not_prime : ¬(recordGapCenter + 438378).Prime := by
  rw [fullRecordGapTerm07569_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07569, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07569_fast_pow_mod_ne_one

def fullRecordGapValue07570 : Nat := fullRecordGapCenterValue + 438392

theorem fullRecordGapTerm07570_eq_value :
    recordGapCenter + 438392 = fullRecordGapValue07570 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07570_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07570 (fullRecordGapValue07570 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07570_not_prime : ¬(recordGapCenter + 438392).Prime := by
  rw [fullRecordGapTerm07570_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07570, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07570_fast_pow_mod_ne_one

def fullRecordGapValue07571 : Nat := fullRecordGapCenterValue + 438722

theorem fullRecordGapTerm07571_eq_value :
    recordGapCenter + 438722 = fullRecordGapValue07571 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07571_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07571 (fullRecordGapValue07571 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07571_not_prime : ¬(recordGapCenter + 438722).Prime := by
  rw [fullRecordGapTerm07571_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07571, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07571_fast_pow_mod_ne_one

def fullRecordGapValue07572 : Nat := fullRecordGapCenterValue + 438726

theorem fullRecordGapTerm07572_eq_value :
    recordGapCenter + 438726 = fullRecordGapValue07572 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07572_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07572 (fullRecordGapValue07572 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07572_not_prime : ¬(recordGapCenter + 438726).Prime := by
  rw [fullRecordGapTerm07572_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07572, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07572_fast_pow_mod_ne_one

def fullRecordGapValue07573 : Nat := fullRecordGapCenterValue + 438846

theorem fullRecordGapTerm07573_eq_value :
    recordGapCenter + 438846 = fullRecordGapValue07573 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07573_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07573 (fullRecordGapValue07573 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07573_not_prime : ¬(recordGapCenter + 438846).Prime := by
  rw [fullRecordGapTerm07573_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07573, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07573_fast_pow_mod_ne_one

def fullRecordGapValue07574 : Nat := fullRecordGapCenterValue + 438926

theorem fullRecordGapTerm07574_eq_value :
    recordGapCenter + 438926 = fullRecordGapValue07574 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07574_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07574 (fullRecordGapValue07574 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07574_not_prime : ¬(recordGapCenter + 438926).Prime := by
  rw [fullRecordGapTerm07574_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07574, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07574_fast_pow_mod_ne_one

def fullRecordGapValue07575 : Nat := fullRecordGapCenterValue + 439086

theorem fullRecordGapTerm07575_eq_value :
    recordGapCenter + 439086 = fullRecordGapValue07575 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07575_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07575 (fullRecordGapValue07575 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07575_not_prime : ¬(recordGapCenter + 439086).Prime := by
  rw [fullRecordGapTerm07575_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07575, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07575_fast_pow_mod_ne_one

def fullRecordGapValue07576 : Nat := fullRecordGapCenterValue + 439230

theorem fullRecordGapTerm07576_eq_value :
    recordGapCenter + 439230 = fullRecordGapValue07576 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07576_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07576 (fullRecordGapValue07576 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07576_not_prime : ¬(recordGapCenter + 439230).Prime := by
  rw [fullRecordGapTerm07576_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07576, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07576_fast_pow_mod_ne_one

def fullRecordGapValue07577 : Nat := fullRecordGapCenterValue + 439316

theorem fullRecordGapTerm07577_eq_value :
    recordGapCenter + 439316 = fullRecordGapValue07577 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07577_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07577 (fullRecordGapValue07577 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07577_not_prime : ¬(recordGapCenter + 439316).Prime := by
  rw [fullRecordGapTerm07577_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07577, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07577_fast_pow_mod_ne_one

def fullRecordGapValue07578 : Nat := fullRecordGapCenterValue + 439352

theorem fullRecordGapTerm07578_eq_value :
    recordGapCenter + 439352 = fullRecordGapValue07578 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07578_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07578 (fullRecordGapValue07578 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07578_not_prime : ¬(recordGapCenter + 439352).Prime := by
  rw [fullRecordGapTerm07578_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07578, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07578_fast_pow_mod_ne_one

def fullRecordGapValue07579 : Nat := fullRecordGapCenterValue + 439430

theorem fullRecordGapTerm07579_eq_value :
    recordGapCenter + 439430 = fullRecordGapValue07579 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07579_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07579 (fullRecordGapValue07579 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07579_not_prime : ¬(recordGapCenter + 439430).Prime := by
  rw [fullRecordGapTerm07579_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07579, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07579_fast_pow_mod_ne_one

def fullRecordGapValue07580 : Nat := fullRecordGapCenterValue + 439442

theorem fullRecordGapTerm07580_eq_value :
    recordGapCenter + 439442 = fullRecordGapValue07580 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07580_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07580 (fullRecordGapValue07580 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07580_not_prime : ¬(recordGapCenter + 439442).Prime := by
  rw [fullRecordGapTerm07580_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07580, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07580_fast_pow_mod_ne_one

def fullRecordGapValue07581 : Nat := fullRecordGapCenterValue + 439458

theorem fullRecordGapTerm07581_eq_value :
    recordGapCenter + 439458 = fullRecordGapValue07581 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07581_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07581 (fullRecordGapValue07581 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07581_not_prime : ¬(recordGapCenter + 439458).Prime := by
  rw [fullRecordGapTerm07581_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07581, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07581_fast_pow_mod_ne_one

def fullRecordGapValue07582 : Nat := fullRecordGapCenterValue + 439598

theorem fullRecordGapTerm07582_eq_value :
    recordGapCenter + 439598 = fullRecordGapValue07582 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07582_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07582 (fullRecordGapValue07582 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07582_not_prime : ¬(recordGapCenter + 439598).Prime := by
  rw [fullRecordGapTerm07582_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07582, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07582_fast_pow_mod_ne_one

def fullRecordGapValue07583 : Nat := fullRecordGapCenterValue + 439646

theorem fullRecordGapTerm07583_eq_value :
    recordGapCenter + 439646 = fullRecordGapValue07583 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07583_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07583 (fullRecordGapValue07583 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07583_not_prime : ¬(recordGapCenter + 439646).Prime := by
  rw [fullRecordGapTerm07583_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07583, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07583_fast_pow_mod_ne_one

def fullRecordGapValue07584 : Nat := fullRecordGapCenterValue + 439652

theorem fullRecordGapTerm07584_eq_value :
    recordGapCenter + 439652 = fullRecordGapValue07584 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07584_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07584 (fullRecordGapValue07584 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07584_not_prime : ¬(recordGapCenter + 439652).Prime := by
  rw [fullRecordGapTerm07584_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07584, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07584_fast_pow_mod_ne_one

def fullRecordGapValue07585 : Nat := fullRecordGapCenterValue + 439832

theorem fullRecordGapTerm07585_eq_value :
    recordGapCenter + 439832 = fullRecordGapValue07585 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07585_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07585 (fullRecordGapValue07585 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07585_not_prime : ¬(recordGapCenter + 439832).Prime := by
  rw [fullRecordGapTerm07585_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07585, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07585_fast_pow_mod_ne_one

def fullRecordGapValue07586 : Nat := fullRecordGapCenterValue + 439862

theorem fullRecordGapTerm07586_eq_value :
    recordGapCenter + 439862 = fullRecordGapValue07586 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07586_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07586 (fullRecordGapValue07586 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07586_not_prime : ¬(recordGapCenter + 439862).Prime := by
  rw [fullRecordGapTerm07586_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07586, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07586_fast_pow_mod_ne_one

def fullRecordGapValue07587 : Nat := fullRecordGapCenterValue + 439910

theorem fullRecordGapTerm07587_eq_value :
    recordGapCenter + 439910 = fullRecordGapValue07587 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07587_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07587 (fullRecordGapValue07587 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07587_not_prime : ¬(recordGapCenter + 439910).Prime := by
  rw [fullRecordGapTerm07587_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07587, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07587_fast_pow_mod_ne_one

def fullRecordGapValue07588 : Nat := fullRecordGapCenterValue + 439962

theorem fullRecordGapTerm07588_eq_value :
    recordGapCenter + 439962 = fullRecordGapValue07588 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07588_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07588 (fullRecordGapValue07588 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07588_not_prime : ¬(recordGapCenter + 439962).Prime := by
  rw [fullRecordGapTerm07588_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07588, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07588_fast_pow_mod_ne_one

def fullRecordGapValue07589 : Nat := fullRecordGapCenterValue + 440072

theorem fullRecordGapTerm07589_eq_value :
    recordGapCenter + 440072 = fullRecordGapValue07589 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07589_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07589 (fullRecordGapValue07589 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07589_not_prime : ¬(recordGapCenter + 440072).Prime := by
  rw [fullRecordGapTerm07589_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07589, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07589_fast_pow_mod_ne_one

def fullRecordGapValue07590 : Nat := fullRecordGapCenterValue + 440178

theorem fullRecordGapTerm07590_eq_value :
    recordGapCenter + 440178 = fullRecordGapValue07590 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07590_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07590 (fullRecordGapValue07590 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07590_not_prime : ¬(recordGapCenter + 440178).Prime := by
  rw [fullRecordGapTerm07590_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07590, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07590_fast_pow_mod_ne_one

def fullRecordGapValue07591 : Nat := fullRecordGapCenterValue + 440210

theorem fullRecordGapTerm07591_eq_value :
    recordGapCenter + 440210 = fullRecordGapValue07591 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07591_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07591 (fullRecordGapValue07591 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07591_not_prime : ¬(recordGapCenter + 440210).Prime := by
  rw [fullRecordGapTerm07591_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07591, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07591_fast_pow_mod_ne_one

def fullRecordGapValue07592 : Nat := fullRecordGapCenterValue + 440246

theorem fullRecordGapTerm07592_eq_value :
    recordGapCenter + 440246 = fullRecordGapValue07592 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07592_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07592 (fullRecordGapValue07592 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07592_not_prime : ¬(recordGapCenter + 440246).Prime := by
  rw [fullRecordGapTerm07592_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07592, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07592_fast_pow_mod_ne_one

def fullRecordGapValue07593 : Nat := fullRecordGapCenterValue + 440408

theorem fullRecordGapTerm07593_eq_value :
    recordGapCenter + 440408 = fullRecordGapValue07593 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07593_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07593 (fullRecordGapValue07593 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07593_not_prime : ¬(recordGapCenter + 440408).Prime := by
  rw [fullRecordGapTerm07593_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07593, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07593_fast_pow_mod_ne_one

def fullRecordGapValue07594 : Nat := fullRecordGapCenterValue + 440456

theorem fullRecordGapTerm07594_eq_value :
    recordGapCenter + 440456 = fullRecordGapValue07594 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07594_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07594 (fullRecordGapValue07594 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07594_not_prime : ¬(recordGapCenter + 440456).Prime := by
  rw [fullRecordGapTerm07594_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07594, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07594_fast_pow_mod_ne_one

def fullRecordGapValue07595 : Nat := fullRecordGapCenterValue + 440718

theorem fullRecordGapTerm07595_eq_value :
    recordGapCenter + 440718 = fullRecordGapValue07595 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07595_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07595 (fullRecordGapValue07595 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07595_not_prime : ¬(recordGapCenter + 440718).Prime := by
  rw [fullRecordGapTerm07595_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07595, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07595_fast_pow_mod_ne_one

def fullRecordGapValue07596 : Nat := fullRecordGapCenterValue + 440738

theorem fullRecordGapTerm07596_eq_value :
    recordGapCenter + 440738 = fullRecordGapValue07596 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07596_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07596 (fullRecordGapValue07596 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07596_not_prime : ¬(recordGapCenter + 440738).Prime := by
  rw [fullRecordGapTerm07596_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07596, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07596_fast_pow_mod_ne_one

def fullRecordGapValue07597 : Nat := fullRecordGapCenterValue + 440798

theorem fullRecordGapTerm07597_eq_value :
    recordGapCenter + 440798 = fullRecordGapValue07597 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07597_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07597 (fullRecordGapValue07597 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07597_not_prime : ¬(recordGapCenter + 440798).Prime := by
  rw [fullRecordGapTerm07597_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07597, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07597_fast_pow_mod_ne_one

def fullRecordGapValue07598 : Nat := fullRecordGapCenterValue + 440822

theorem fullRecordGapTerm07598_eq_value :
    recordGapCenter + 440822 = fullRecordGapValue07598 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07598_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07598 (fullRecordGapValue07598 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07598_not_prime : ¬(recordGapCenter + 440822).Prime := by
  rw [fullRecordGapTerm07598_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07598, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07598_fast_pow_mod_ne_one

def fullRecordGapValue07599 : Nat := fullRecordGapCenterValue + 440826

theorem fullRecordGapTerm07599_eq_value :
    recordGapCenter + 440826 = fullRecordGapValue07599 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07599_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07599 (fullRecordGapValue07599 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07599_not_prime : ¬(recordGapCenter + 440826).Prime := by
  rw [fullRecordGapTerm07599_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07599, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07599_fast_pow_mod_ne_one

def fullRecordGapValue07600 : Nat := fullRecordGapCenterValue + 440862

theorem fullRecordGapTerm07600_eq_value :
    recordGapCenter + 440862 = fullRecordGapValue07600 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07600_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07600 (fullRecordGapValue07600 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07600_not_prime : ¬(recordGapCenter + 440862).Prime := by
  rw [fullRecordGapTerm07600_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07600, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07600_fast_pow_mod_ne_one

def fullRecordGapValue07601 : Nat := fullRecordGapCenterValue + 441102

theorem fullRecordGapTerm07601_eq_value :
    recordGapCenter + 441102 = fullRecordGapValue07601 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07601_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07601 (fullRecordGapValue07601 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07601_not_prime : ¬(recordGapCenter + 441102).Prime := by
  rw [fullRecordGapTerm07601_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07601, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07601_fast_pow_mod_ne_one

def fullRecordGapValue07602 : Nat := fullRecordGapCenterValue + 441110

theorem fullRecordGapTerm07602_eq_value :
    recordGapCenter + 441110 = fullRecordGapValue07602 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07602_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07602 (fullRecordGapValue07602 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07602_not_prime : ¬(recordGapCenter + 441110).Prime := by
  rw [fullRecordGapTerm07602_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07602, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07602_fast_pow_mod_ne_one

def fullRecordGapValue07603 : Nat := fullRecordGapCenterValue + 441282

theorem fullRecordGapTerm07603_eq_value :
    recordGapCenter + 441282 = fullRecordGapValue07603 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07603_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07603 (fullRecordGapValue07603 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07603_not_prime : ¬(recordGapCenter + 441282).Prime := by
  rw [fullRecordGapTerm07603_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07603, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07603_fast_pow_mod_ne_one

def fullRecordGapValue07604 : Nat := fullRecordGapCenterValue + 441290

theorem fullRecordGapTerm07604_eq_value :
    recordGapCenter + 441290 = fullRecordGapValue07604 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07604_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07604 (fullRecordGapValue07604 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07604_not_prime : ¬(recordGapCenter + 441290).Prime := by
  rw [fullRecordGapTerm07604_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07604, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07604_fast_pow_mod_ne_one

def fullRecordGapValue07605 : Nat := fullRecordGapCenterValue + 441318

theorem fullRecordGapTerm07605_eq_value :
    recordGapCenter + 441318 = fullRecordGapValue07605 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07605_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07605 (fullRecordGapValue07605 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07605_not_prime : ¬(recordGapCenter + 441318).Prime := by
  rw [fullRecordGapTerm07605_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07605, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07605_fast_pow_mod_ne_one

def fullRecordGapValue07606 : Nat := fullRecordGapCenterValue + 441362

theorem fullRecordGapTerm07606_eq_value :
    recordGapCenter + 441362 = fullRecordGapValue07606 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07606_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07606 (fullRecordGapValue07606 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07606_not_prime : ¬(recordGapCenter + 441362).Prime := by
  rw [fullRecordGapTerm07606_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07606, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07606_fast_pow_mod_ne_one

def fullRecordGapValue07607 : Nat := fullRecordGapCenterValue + 441366

theorem fullRecordGapTerm07607_eq_value :
    recordGapCenter + 441366 = fullRecordGapValue07607 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07607_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07607 (fullRecordGapValue07607 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07607_not_prime : ¬(recordGapCenter + 441366).Prime := by
  rw [fullRecordGapTerm07607_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07607, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07607_fast_pow_mod_ne_one

def fullRecordGapValue07608 : Nat := fullRecordGapCenterValue + 441542

theorem fullRecordGapTerm07608_eq_value :
    recordGapCenter + 441542 = fullRecordGapValue07608 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07608_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07608 (fullRecordGapValue07608 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07608_not_prime : ¬(recordGapCenter + 441542).Prime := by
  rw [fullRecordGapTerm07608_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07608, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07608_fast_pow_mod_ne_one

def fullRecordGapValue07609 : Nat := fullRecordGapCenterValue + 441578

theorem fullRecordGapTerm07609_eq_value :
    recordGapCenter + 441578 = fullRecordGapValue07609 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07609_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07609 (fullRecordGapValue07609 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07609_not_prime : ¬(recordGapCenter + 441578).Prime := by
  rw [fullRecordGapTerm07609_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07609, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07609_fast_pow_mod_ne_one

def fullRecordGapValue07610 : Nat := fullRecordGapCenterValue + 441582

theorem fullRecordGapTerm07610_eq_value :
    recordGapCenter + 441582 = fullRecordGapValue07610 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07610_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07610 (fullRecordGapValue07610 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07610_not_prime : ¬(recordGapCenter + 441582).Prime := by
  rw [fullRecordGapTerm07610_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07610, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07610_fast_pow_mod_ne_one

def fullRecordGapValue07611 : Nat := fullRecordGapCenterValue + 441722

theorem fullRecordGapTerm07611_eq_value :
    recordGapCenter + 441722 = fullRecordGapValue07611 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07611_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07611 (fullRecordGapValue07611 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07611_not_prime : ¬(recordGapCenter + 441722).Prime := by
  rw [fullRecordGapTerm07611_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07611, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07611_fast_pow_mod_ne_one

def fullRecordGapValue07612 : Nat := fullRecordGapCenterValue + 441746

theorem fullRecordGapTerm07612_eq_value :
    recordGapCenter + 441746 = fullRecordGapValue07612 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07612_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07612 (fullRecordGapValue07612 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07612_not_prime : ¬(recordGapCenter + 441746).Prime := by
  rw [fullRecordGapTerm07612_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07612, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07612_fast_pow_mod_ne_one

def fullRecordGapValue07613 : Nat := fullRecordGapCenterValue + 441758

theorem fullRecordGapTerm07613_eq_value :
    recordGapCenter + 441758 = fullRecordGapValue07613 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07613_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07613 (fullRecordGapValue07613 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07613_not_prime : ¬(recordGapCenter + 441758).Prime := by
  rw [fullRecordGapTerm07613_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07613, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07613_fast_pow_mod_ne_one

def fullRecordGapValue07614 : Nat := fullRecordGapCenterValue + 441806

theorem fullRecordGapTerm07614_eq_value :
    recordGapCenter + 441806 = fullRecordGapValue07614 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07614_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07614 (fullRecordGapValue07614 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07614_not_prime : ¬(recordGapCenter + 441806).Prime := by
  rw [fullRecordGapTerm07614_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07614, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07614_fast_pow_mod_ne_one

def fullRecordGapValue07615 : Nat := fullRecordGapCenterValue + 441858

theorem fullRecordGapTerm07615_eq_value :
    recordGapCenter + 441858 = fullRecordGapValue07615 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07615_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07615 (fullRecordGapValue07615 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07615_not_prime : ¬(recordGapCenter + 441858).Prime := by
  rw [fullRecordGapTerm07615_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07615, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07615_fast_pow_mod_ne_one

def fullRecordGapValue07616 : Nat := fullRecordGapCenterValue + 441906

theorem fullRecordGapTerm07616_eq_value :
    recordGapCenter + 441906 = fullRecordGapValue07616 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07616_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07616 (fullRecordGapValue07616 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07616_not_prime : ¬(recordGapCenter + 441906).Prime := by
  rw [fullRecordGapTerm07616_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07616, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07616_fast_pow_mod_ne_one

def fullRecordGapValue07617 : Nat := fullRecordGapCenterValue + 441992

theorem fullRecordGapTerm07617_eq_value :
    recordGapCenter + 441992 = fullRecordGapValue07617 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07617_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07617 (fullRecordGapValue07617 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07617_not_prime : ¬(recordGapCenter + 441992).Prime := by
  rw [fullRecordGapTerm07617_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07617, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07617_fast_pow_mod_ne_one

def fullRecordGapValue07618 : Nat := fullRecordGapCenterValue + 442158

theorem fullRecordGapTerm07618_eq_value :
    recordGapCenter + 442158 = fullRecordGapValue07618 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07618_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07618 (fullRecordGapValue07618 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07618_not_prime : ¬(recordGapCenter + 442158).Prime := by
  rw [fullRecordGapTerm07618_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07618, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07618_fast_pow_mod_ne_one

def fullRecordGapValue07619 : Nat := fullRecordGapCenterValue + 442172

theorem fullRecordGapTerm07619_eq_value :
    recordGapCenter + 442172 = fullRecordGapValue07619 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07619_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07619 (fullRecordGapValue07619 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07619_not_prime : ¬(recordGapCenter + 442172).Prime := by
  rw [fullRecordGapTerm07619_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07619, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07619_fast_pow_mod_ne_one

def fullRecordGapValue07620 : Nat := fullRecordGapCenterValue + 442268

theorem fullRecordGapTerm07620_eq_value :
    recordGapCenter + 442268 = fullRecordGapValue07620 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07620_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07620 (fullRecordGapValue07620 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07620_not_prime : ¬(recordGapCenter + 442268).Prime := by
  rw [fullRecordGapTerm07620_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07620, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07620_fast_pow_mod_ne_one

def fullRecordGapValue07621 : Nat := fullRecordGapCenterValue + 442418

theorem fullRecordGapTerm07621_eq_value :
    recordGapCenter + 442418 = fullRecordGapValue07621 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07621_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07621 (fullRecordGapValue07621 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07621_not_prime : ¬(recordGapCenter + 442418).Prime := by
  rw [fullRecordGapTerm07621_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07621, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07621_fast_pow_mod_ne_one

def fullRecordGapValue07622 : Nat := fullRecordGapCenterValue + 442466

theorem fullRecordGapTerm07622_eq_value :
    recordGapCenter + 442466 = fullRecordGapValue07622 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07622_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07622 (fullRecordGapValue07622 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07622_not_prime : ¬(recordGapCenter + 442466).Prime := by
  rw [fullRecordGapTerm07622_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07622, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07622_fast_pow_mod_ne_one

def fullRecordGapValue07623 : Nat := fullRecordGapCenterValue + 442478

theorem fullRecordGapTerm07623_eq_value :
    recordGapCenter + 442478 = fullRecordGapValue07623 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07623_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07623 (fullRecordGapValue07623 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07623_not_prime : ¬(recordGapCenter + 442478).Prime := by
  rw [fullRecordGapTerm07623_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07623, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07623_fast_pow_mod_ne_one

def fullRecordGapValue07624 : Nat := fullRecordGapCenterValue + 442626

theorem fullRecordGapTerm07624_eq_value :
    recordGapCenter + 442626 = fullRecordGapValue07624 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07624_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07624 (fullRecordGapValue07624 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07624_not_prime : ¬(recordGapCenter + 442626).Prime := by
  rw [fullRecordGapTerm07624_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07624, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07624_fast_pow_mod_ne_one

def fullRecordGapValue07625 : Nat := fullRecordGapCenterValue + 442698

theorem fullRecordGapTerm07625_eq_value :
    recordGapCenter + 442698 = fullRecordGapValue07625 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07625_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07625 (fullRecordGapValue07625 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07625_not_prime : ¬(recordGapCenter + 442698).Prime := by
  rw [fullRecordGapTerm07625_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07625, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07625_fast_pow_mod_ne_one

def fullRecordGapValue07626 : Nat := fullRecordGapCenterValue + 442808

theorem fullRecordGapTerm07626_eq_value :
    recordGapCenter + 442808 = fullRecordGapValue07626 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07626_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07626 (fullRecordGapValue07626 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07626_not_prime : ¬(recordGapCenter + 442808).Prime := by
  rw [fullRecordGapTerm07626_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07626, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07626_fast_pow_mod_ne_one

def fullRecordGapValue07627 : Nat := fullRecordGapCenterValue + 442916

theorem fullRecordGapTerm07627_eq_value :
    recordGapCenter + 442916 = fullRecordGapValue07627 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07627_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07627 (fullRecordGapValue07627 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07627_not_prime : ¬(recordGapCenter + 442916).Prime := by
  rw [fullRecordGapTerm07627_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07627, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07627_fast_pow_mod_ne_one

def fullRecordGapValue07628 : Nat := fullRecordGapCenterValue + 443012

theorem fullRecordGapTerm07628_eq_value :
    recordGapCenter + 443012 = fullRecordGapValue07628 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07628_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07628 (fullRecordGapValue07628 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07628_not_prime : ¬(recordGapCenter + 443012).Prime := by
  rw [fullRecordGapTerm07628_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07628, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07628_fast_pow_mod_ne_one

def fullRecordGapValue07629 : Nat := fullRecordGapCenterValue + 443018

theorem fullRecordGapTerm07629_eq_value :
    recordGapCenter + 443018 = fullRecordGapValue07629 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07629_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07629 (fullRecordGapValue07629 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07629_not_prime : ¬(recordGapCenter + 443018).Prime := by
  rw [fullRecordGapTerm07629_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07629, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07629_fast_pow_mod_ne_one

def fullRecordGapValue07630 : Nat := fullRecordGapCenterValue + 443048

theorem fullRecordGapTerm07630_eq_value :
    recordGapCenter + 443048 = fullRecordGapValue07630 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07630_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07630 (fullRecordGapValue07630 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07630_not_prime : ¬(recordGapCenter + 443048).Prime := by
  rw [fullRecordGapTerm07630_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07630, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07630_fast_pow_mod_ne_one

def fullRecordGapValue07631 : Nat := fullRecordGapCenterValue + 443082

theorem fullRecordGapTerm07631_eq_value :
    recordGapCenter + 443082 = fullRecordGapValue07631 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07631_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07631 (fullRecordGapValue07631 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07631_not_prime : ¬(recordGapCenter + 443082).Prime := by
  rw [fullRecordGapTerm07631_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07631, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07631_fast_pow_mod_ne_one

def fullRecordGapValue07632 : Nat := fullRecordGapCenterValue + 443192

theorem fullRecordGapTerm07632_eq_value :
    recordGapCenter + 443192 = fullRecordGapValue07632 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07632_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07632 (fullRecordGapValue07632 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07632_not_prime : ¬(recordGapCenter + 443192).Prime := by
  rw [fullRecordGapTerm07632_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07632, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07632_fast_pow_mod_ne_one

def fullRecordGapValue07633 : Nat := fullRecordGapCenterValue + 443306

theorem fullRecordGapTerm07633_eq_value :
    recordGapCenter + 443306 = fullRecordGapValue07633 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07633_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07633 (fullRecordGapValue07633 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07633_not_prime : ¬(recordGapCenter + 443306).Prime := by
  rw [fullRecordGapTerm07633_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07633, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07633_fast_pow_mod_ne_one

def fullRecordGapValue07634 : Nat := fullRecordGapCenterValue + 443396

theorem fullRecordGapTerm07634_eq_value :
    recordGapCenter + 443396 = fullRecordGapValue07634 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07634_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07634 (fullRecordGapValue07634 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07634_not_prime : ¬(recordGapCenter + 443396).Prime := by
  rw [fullRecordGapTerm07634_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07634, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07634_fast_pow_mod_ne_one

def fullRecordGapValue07635 : Nat := fullRecordGapCenterValue + 443426

theorem fullRecordGapTerm07635_eq_value :
    recordGapCenter + 443426 = fullRecordGapValue07635 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07635_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07635 (fullRecordGapValue07635 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07635_not_prime : ¬(recordGapCenter + 443426).Prime := by
  rw [fullRecordGapTerm07635_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07635, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07635_fast_pow_mod_ne_one

def fullRecordGapValue07636 : Nat := fullRecordGapCenterValue + 443438

theorem fullRecordGapTerm07636_eq_value :
    recordGapCenter + 443438 = fullRecordGapValue07636 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07636_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07636 (fullRecordGapValue07636 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07636_not_prime : ¬(recordGapCenter + 443438).Prime := by
  rw [fullRecordGapTerm07636_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07636, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07636_fast_pow_mod_ne_one

def fullRecordGapValue07637 : Nat := fullRecordGapCenterValue + 443528

theorem fullRecordGapTerm07637_eq_value :
    recordGapCenter + 443528 = fullRecordGapValue07637 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07637_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07637 (fullRecordGapValue07637 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07637_not_prime : ¬(recordGapCenter + 443528).Prime := by
  rw [fullRecordGapTerm07637_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07637, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07637_fast_pow_mod_ne_one

def fullRecordGapValue07638 : Nat := fullRecordGapCenterValue + 443570

theorem fullRecordGapTerm07638_eq_value :
    recordGapCenter + 443570 = fullRecordGapValue07638 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07638_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07638 (fullRecordGapValue07638 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07638_not_prime : ¬(recordGapCenter + 443570).Prime := by
  rw [fullRecordGapTerm07638_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07638, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07638_fast_pow_mod_ne_one

def fullRecordGapValue07639 : Nat := fullRecordGapCenterValue + 443636

theorem fullRecordGapTerm07639_eq_value :
    recordGapCenter + 443636 = fullRecordGapValue07639 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07639_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07639 (fullRecordGapValue07639 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07639_not_prime : ¬(recordGapCenter + 443636).Prime := by
  rw [fullRecordGapTerm07639_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07639, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07639_fast_pow_mod_ne_one

def fullRecordGapValue07640 : Nat := fullRecordGapCenterValue + 443658

theorem fullRecordGapTerm07640_eq_value :
    recordGapCenter + 443658 = fullRecordGapValue07640 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07640_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07640 (fullRecordGapValue07640 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07640_not_prime : ¬(recordGapCenter + 443658).Prime := by
  rw [fullRecordGapTerm07640_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07640, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07640_fast_pow_mod_ne_one

def fullRecordGapValue07641 : Nat := fullRecordGapCenterValue + 443882

theorem fullRecordGapTerm07641_eq_value :
    recordGapCenter + 443882 = fullRecordGapValue07641 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07641_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07641 (fullRecordGapValue07641 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07641_not_prime : ¬(recordGapCenter + 443882).Prime := by
  rw [fullRecordGapTerm07641_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07641, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07641_fast_pow_mod_ne_one

def fullRecordGapValue07642 : Nat := fullRecordGapCenterValue + 444008

theorem fullRecordGapTerm07642_eq_value :
    recordGapCenter + 444008 = fullRecordGapValue07642 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07642_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07642 (fullRecordGapValue07642 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07642_not_prime : ¬(recordGapCenter + 444008).Prime := by
  rw [fullRecordGapTerm07642_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07642, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07642_fast_pow_mod_ne_one

def fullRecordGapValue07643 : Nat := fullRecordGapCenterValue + 444126

theorem fullRecordGapTerm07643_eq_value :
    recordGapCenter + 444126 = fullRecordGapValue07643 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07643_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07643 (fullRecordGapValue07643 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07643_not_prime : ¬(recordGapCenter + 444126).Prime := by
  rw [fullRecordGapTerm07643_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07643, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07643_fast_pow_mod_ne_one

def fullRecordGapValue07644 : Nat := fullRecordGapCenterValue + 444162

theorem fullRecordGapTerm07644_eq_value :
    recordGapCenter + 444162 = fullRecordGapValue07644 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07644_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07644 (fullRecordGapValue07644 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07644_not_prime : ¬(recordGapCenter + 444162).Prime := by
  rw [fullRecordGapTerm07644_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07644, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07644_fast_pow_mod_ne_one

def fullRecordGapValue07645 : Nat := fullRecordGapCenterValue + 444326

theorem fullRecordGapTerm07645_eq_value :
    recordGapCenter + 444326 = fullRecordGapValue07645 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07645_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07645 (fullRecordGapValue07645 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07645_not_prime : ¬(recordGapCenter + 444326).Prime := by
  rw [fullRecordGapTerm07645_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07645, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07645_fast_pow_mod_ne_one

def fullRecordGapValue07646 : Nat := fullRecordGapCenterValue + 444386

theorem fullRecordGapTerm07646_eq_value :
    recordGapCenter + 444386 = fullRecordGapValue07646 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07646_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07646 (fullRecordGapValue07646 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07646_not_prime : ¬(recordGapCenter + 444386).Prime := by
  rw [fullRecordGapTerm07646_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07646, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07646_fast_pow_mod_ne_one

def fullRecordGapValue07647 : Nat := fullRecordGapCenterValue + 444398

theorem fullRecordGapTerm07647_eq_value :
    recordGapCenter + 444398 = fullRecordGapValue07647 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07647_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07647 (fullRecordGapValue07647 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07647_not_prime : ¬(recordGapCenter + 444398).Prime := by
  rw [fullRecordGapTerm07647_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07647, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07647_fast_pow_mod_ne_one

def fullRecordGapValue07648 : Nat := fullRecordGapCenterValue + 444426

theorem fullRecordGapTerm07648_eq_value :
    recordGapCenter + 444426 = fullRecordGapValue07648 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07648_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07648 (fullRecordGapValue07648 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07648_not_prime : ¬(recordGapCenter + 444426).Prime := by
  rw [fullRecordGapTerm07648_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07648, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07648_fast_pow_mod_ne_one

def fullRecordGapValue07649 : Nat := fullRecordGapCenterValue + 444476

theorem fullRecordGapTerm07649_eq_value :
    recordGapCenter + 444476 = fullRecordGapValue07649 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07649_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07649 (fullRecordGapValue07649 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07649_not_prime : ¬(recordGapCenter + 444476).Prime := by
  rw [fullRecordGapTerm07649_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07649, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07649_fast_pow_mod_ne_one

def fullRecordGapValue07650 : Nat := fullRecordGapCenterValue + 444530

theorem fullRecordGapTerm07650_eq_value :
    recordGapCenter + 444530 = fullRecordGapValue07650 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07650_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07650 (fullRecordGapValue07650 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07650_not_prime : ¬(recordGapCenter + 444530).Prime := by
  rw [fullRecordGapTerm07650_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07650, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07650_fast_pow_mod_ne_one

def fullRecordGapValue07651 : Nat := fullRecordGapCenterValue + 444558

theorem fullRecordGapTerm07651_eq_value :
    recordGapCenter + 444558 = fullRecordGapValue07651 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07651_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07651 (fullRecordGapValue07651 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07651_not_prime : ¬(recordGapCenter + 444558).Prime := by
  rw [fullRecordGapTerm07651_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07651, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07651_fast_pow_mod_ne_one

def fullRecordGapValue07652 : Nat := fullRecordGapCenterValue + 444806

theorem fullRecordGapTerm07652_eq_value :
    recordGapCenter + 444806 = fullRecordGapValue07652 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07652_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07652 (fullRecordGapValue07652 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07652_not_prime : ¬(recordGapCenter + 444806).Prime := by
  rw [fullRecordGapTerm07652_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07652, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07652_fast_pow_mod_ne_one

def fullRecordGapValue07653 : Nat := fullRecordGapCenterValue + 444908

theorem fullRecordGapTerm07653_eq_value :
    recordGapCenter + 444908 = fullRecordGapValue07653 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07653_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07653 (fullRecordGapValue07653 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07653_not_prime : ¬(recordGapCenter + 444908).Prime := by
  rw [fullRecordGapTerm07653_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07653, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07653_fast_pow_mod_ne_one

def fullRecordGapValue07654 : Nat := fullRecordGapCenterValue + 444966

theorem fullRecordGapTerm07654_eq_value :
    recordGapCenter + 444966 = fullRecordGapValue07654 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07654_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07654 (fullRecordGapValue07654 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07654_not_prime : ¬(recordGapCenter + 444966).Prime := by
  rw [fullRecordGapTerm07654_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07654, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07654_fast_pow_mod_ne_one

def fullRecordGapValue07655 : Nat := fullRecordGapCenterValue + 444998

theorem fullRecordGapTerm07655_eq_value :
    recordGapCenter + 444998 = fullRecordGapValue07655 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07655_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07655 (fullRecordGapValue07655 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07655_not_prime : ¬(recordGapCenter + 444998).Prime := by
  rw [fullRecordGapTerm07655_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07655, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07655_fast_pow_mod_ne_one

def fullRecordGapValue07656 : Nat := fullRecordGapCenterValue + 445002

theorem fullRecordGapTerm07656_eq_value :
    recordGapCenter + 445002 = fullRecordGapValue07656 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07656_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07656 (fullRecordGapValue07656 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07656_not_prime : ¬(recordGapCenter + 445002).Prime := by
  rw [fullRecordGapTerm07656_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07656, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07656_fast_pow_mod_ne_one

def fullRecordGapValue07657 : Nat := fullRecordGapCenterValue + 445022

theorem fullRecordGapTerm07657_eq_value :
    recordGapCenter + 445022 = fullRecordGapValue07657 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07657_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07657 (fullRecordGapValue07657 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07657_not_prime : ¬(recordGapCenter + 445022).Prime := by
  rw [fullRecordGapTerm07657_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07657, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07657_fast_pow_mod_ne_one

def fullRecordGapValue07658 : Nat := fullRecordGapCenterValue + 445070

theorem fullRecordGapTerm07658_eq_value :
    recordGapCenter + 445070 = fullRecordGapValue07658 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07658_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07658 (fullRecordGapValue07658 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07658_not_prime : ¬(recordGapCenter + 445070).Prime := by
  rw [fullRecordGapTerm07658_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07658, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07658_fast_pow_mod_ne_one

def fullRecordGapValue07659 : Nat := fullRecordGapCenterValue + 445106

theorem fullRecordGapTerm07659_eq_value :
    recordGapCenter + 445106 = fullRecordGapValue07659 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07659_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07659 (fullRecordGapValue07659 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07659_not_prime : ¬(recordGapCenter + 445106).Prime := by
  rw [fullRecordGapTerm07659_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07659, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07659_fast_pow_mod_ne_one

def fullRecordGapValue07660 : Nat := fullRecordGapCenterValue + 445112

theorem fullRecordGapTerm07660_eq_value :
    recordGapCenter + 445112 = fullRecordGapValue07660 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07660_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07660 (fullRecordGapValue07660 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07660_not_prime : ¬(recordGapCenter + 445112).Prime := by
  rw [fullRecordGapTerm07660_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07660, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07660_fast_pow_mod_ne_one

def fullRecordGapValue07661 : Nat := fullRecordGapCenterValue + 445182

theorem fullRecordGapTerm07661_eq_value :
    recordGapCenter + 445182 = fullRecordGapValue07661 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07661_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07661 (fullRecordGapValue07661 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07661_not_prime : ¬(recordGapCenter + 445182).Prime := by
  rw [fullRecordGapTerm07661_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07661, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07661_fast_pow_mod_ne_one

def fullRecordGapValue07662 : Nat := fullRecordGapCenterValue + 445202

theorem fullRecordGapTerm07662_eq_value :
    recordGapCenter + 445202 = fullRecordGapValue07662 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07662_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07662 (fullRecordGapValue07662 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07662_not_prime : ¬(recordGapCenter + 445202).Prime := by
  rw [fullRecordGapTerm07662_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07662, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07662_fast_pow_mod_ne_one

def fullRecordGapValue07663 : Nat := fullRecordGapCenterValue + 445226

theorem fullRecordGapTerm07663_eq_value :
    recordGapCenter + 445226 = fullRecordGapValue07663 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07663_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07663 (fullRecordGapValue07663 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07663_not_prime : ¬(recordGapCenter + 445226).Prime := by
  rw [fullRecordGapTerm07663_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07663, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07663_fast_pow_mod_ne_one

def fullRecordGapValue07664 : Nat := fullRecordGapCenterValue + 445268

theorem fullRecordGapTerm07664_eq_value :
    recordGapCenter + 445268 = fullRecordGapValue07664 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07664_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07664 (fullRecordGapValue07664 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07664_not_prime : ¬(recordGapCenter + 445268).Prime := by
  rw [fullRecordGapTerm07664_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07664, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07664_fast_pow_mod_ne_one

def fullRecordGapValue07665 : Nat := fullRecordGapCenterValue + 445292

theorem fullRecordGapTerm07665_eq_value :
    recordGapCenter + 445292 = fullRecordGapValue07665 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07665_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07665 (fullRecordGapValue07665 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07665_not_prime : ¬(recordGapCenter + 445292).Prime := by
  rw [fullRecordGapTerm07665_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07665, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07665_fast_pow_mod_ne_one

def fullRecordGapValue07666 : Nat := fullRecordGapCenterValue + 445358

theorem fullRecordGapTerm07666_eq_value :
    recordGapCenter + 445358 = fullRecordGapValue07666 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07666_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07666 (fullRecordGapValue07666 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07666_not_prime : ¬(recordGapCenter + 445358).Prime := by
  rw [fullRecordGapTerm07666_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07666, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07666_fast_pow_mod_ne_one

def fullRecordGapValue07667 : Nat := fullRecordGapCenterValue + 445448

theorem fullRecordGapTerm07667_eq_value :
    recordGapCenter + 445448 = fullRecordGapValue07667 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07667_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07667 (fullRecordGapValue07667 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07667_not_prime : ¬(recordGapCenter + 445448).Prime := by
  rw [fullRecordGapTerm07667_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07667, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07667_fast_pow_mod_ne_one

def fullRecordGapValue07668 : Nat := fullRecordGapCenterValue + 445490

theorem fullRecordGapTerm07668_eq_value :
    recordGapCenter + 445490 = fullRecordGapValue07668 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07668_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07668 (fullRecordGapValue07668 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07668_not_prime : ¬(recordGapCenter + 445490).Prime := by
  rw [fullRecordGapTerm07668_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07668, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07668_fast_pow_mod_ne_one

def fullRecordGapValue07669 : Nat := fullRecordGapCenterValue + 445646

theorem fullRecordGapTerm07669_eq_value :
    recordGapCenter + 445646 = fullRecordGapValue07669 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07669_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07669 (fullRecordGapValue07669 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07669_not_prime : ¬(recordGapCenter + 445646).Prime := by
  rw [fullRecordGapTerm07669_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07669, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07669_fast_pow_mod_ne_one

def fullRecordGapValue07670 : Nat := fullRecordGapCenterValue + 445722

theorem fullRecordGapTerm07670_eq_value :
    recordGapCenter + 445722 = fullRecordGapValue07670 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07670_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07670 (fullRecordGapValue07670 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07670_not_prime : ¬(recordGapCenter + 445722).Prime := by
  rw [fullRecordGapTerm07670_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07670, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07670_fast_pow_mod_ne_one

def fullRecordGapValue07671 : Nat := fullRecordGapCenterValue + 445736

theorem fullRecordGapTerm07671_eq_value :
    recordGapCenter + 445736 = fullRecordGapValue07671 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07671_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07671 (fullRecordGapValue07671 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07671_not_prime : ¬(recordGapCenter + 445736).Prime := by
  rw [fullRecordGapTerm07671_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07671, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07671_fast_pow_mod_ne_one

def fullRecordGapValue07672 : Nat := fullRecordGapCenterValue + 445772

theorem fullRecordGapTerm07672_eq_value :
    recordGapCenter + 445772 = fullRecordGapValue07672 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07672_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07672 (fullRecordGapValue07672 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07672_not_prime : ¬(recordGapCenter + 445772).Prime := by
  rw [fullRecordGapTerm07672_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07672, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07672_fast_pow_mod_ne_one

def fullRecordGapValue07673 : Nat := fullRecordGapCenterValue + 445790

theorem fullRecordGapTerm07673_eq_value :
    recordGapCenter + 445790 = fullRecordGapValue07673 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07673_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07673 (fullRecordGapValue07673 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07673_not_prime : ¬(recordGapCenter + 445790).Prime := by
  rw [fullRecordGapTerm07673_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07673, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07673_fast_pow_mod_ne_one

def fullRecordGapValue07674 : Nat := fullRecordGapCenterValue + 445838

theorem fullRecordGapTerm07674_eq_value :
    recordGapCenter + 445838 = fullRecordGapValue07674 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07674_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07674 (fullRecordGapValue07674 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07674_not_prime : ¬(recordGapCenter + 445838).Prime := by
  rw [fullRecordGapTerm07674_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07674, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07674_fast_pow_mod_ne_one

def fullRecordGapValue07675 : Nat := fullRecordGapCenterValue + 445862

theorem fullRecordGapTerm07675_eq_value :
    recordGapCenter + 445862 = fullRecordGapValue07675 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07675_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07675 (fullRecordGapValue07675 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07675_not_prime : ¬(recordGapCenter + 445862).Prime := by
  rw [fullRecordGapTerm07675_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07675, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07675_fast_pow_mod_ne_one

def fullRecordGapValue07676 : Nat := fullRecordGapCenterValue + 445868

theorem fullRecordGapTerm07676_eq_value :
    recordGapCenter + 445868 = fullRecordGapValue07676 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07676_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07676 (fullRecordGapValue07676 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07676_not_prime : ¬(recordGapCenter + 445868).Prime := by
  rw [fullRecordGapTerm07676_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07676, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07676_fast_pow_mod_ne_one

def fullRecordGapValue07677 : Nat := fullRecordGapCenterValue + 445902

theorem fullRecordGapTerm07677_eq_value :
    recordGapCenter + 445902 = fullRecordGapValue07677 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07677_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07677 (fullRecordGapValue07677 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07677_not_prime : ¬(recordGapCenter + 445902).Prime := by
  rw [fullRecordGapTerm07677_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07677, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07677_fast_pow_mod_ne_one

def fullRecordGapValue07678 : Nat := fullRecordGapCenterValue + 445938

theorem fullRecordGapTerm07678_eq_value :
    recordGapCenter + 445938 = fullRecordGapValue07678 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07678_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07678 (fullRecordGapValue07678 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07678_not_prime : ¬(recordGapCenter + 445938).Prime := by
  rw [fullRecordGapTerm07678_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07678, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07678_fast_pow_mod_ne_one

def fullRecordGapValue07679 : Nat := fullRecordGapCenterValue + 445982

theorem fullRecordGapTerm07679_eq_value :
    recordGapCenter + 445982 = fullRecordGapValue07679 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07679_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07679 (fullRecordGapValue07679 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07679_not_prime : ¬(recordGapCenter + 445982).Prime := by
  rw [fullRecordGapTerm07679_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07679, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07679_fast_pow_mod_ne_one

def fullRecordGapValue07680 : Nat := fullRecordGapCenterValue + 446036

theorem fullRecordGapTerm07680_eq_value :
    recordGapCenter + 446036 = fullRecordGapValue07680 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral07680_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue07680 (fullRecordGapValue07680 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07680_not_prime : ¬(recordGapCenter + 446036).Prime := by
  rw [fullRecordGapTerm07680_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue07680, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral07680_fast_pow_mod_ne_one

end PrimeFactorUnimodality
