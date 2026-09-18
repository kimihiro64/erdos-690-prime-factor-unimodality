import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue06401 : Nat := fullRecordGapCenterValue + 348482

theorem fullRecordGapTerm06401_eq_value :
    recordGapCenter + 348482 = fullRecordGapValue06401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06401 (fullRecordGapValue06401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06401_not_prime : ¬(recordGapCenter + 348482).Prime := by
  rw [fullRecordGapTerm06401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06401_fast_pow_mod_ne_one

def fullRecordGapValue06402 : Nat := fullRecordGapCenterValue + 348632

theorem fullRecordGapTerm06402_eq_value :
    recordGapCenter + 348632 = fullRecordGapValue06402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06402 (fullRecordGapValue06402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06402_not_prime : ¬(recordGapCenter + 348632).Prime := by
  rw [fullRecordGapTerm06402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06402_fast_pow_mod_ne_one

def fullRecordGapValue06403 : Nat := fullRecordGapCenterValue + 348666

theorem fullRecordGapTerm06403_eq_value :
    recordGapCenter + 348666 = fullRecordGapValue06403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06403 (fullRecordGapValue06403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06403_not_prime : ¬(recordGapCenter + 348666).Prime := by
  rw [fullRecordGapTerm06403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06403_fast_pow_mod_ne_one

def fullRecordGapValue06404 : Nat := fullRecordGapCenterValue + 348716

theorem fullRecordGapTerm06404_eq_value :
    recordGapCenter + 348716 = fullRecordGapValue06404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06404 (fullRecordGapValue06404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06404_not_prime : ¬(recordGapCenter + 348716).Prime := by
  rw [fullRecordGapTerm06404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06404_fast_pow_mod_ne_one

def fullRecordGapValue06405 : Nat := fullRecordGapCenterValue + 348882

theorem fullRecordGapTerm06405_eq_value :
    recordGapCenter + 348882 = fullRecordGapValue06405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06405 (fullRecordGapValue06405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06405_not_prime : ¬(recordGapCenter + 348882).Prime := by
  rw [fullRecordGapTerm06405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06405_fast_pow_mod_ne_one

def fullRecordGapValue06406 : Nat := fullRecordGapCenterValue + 349142

theorem fullRecordGapTerm06406_eq_value :
    recordGapCenter + 349142 = fullRecordGapValue06406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06406 (fullRecordGapValue06406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06406_not_prime : ¬(recordGapCenter + 349142).Prime := by
  rw [fullRecordGapTerm06406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06406_fast_pow_mod_ne_one

def fullRecordGapValue06407 : Nat := fullRecordGapCenterValue + 349196

theorem fullRecordGapTerm06407_eq_value :
    recordGapCenter + 349196 = fullRecordGapValue06407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06407 (fullRecordGapValue06407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06407_not_prime : ¬(recordGapCenter + 349196).Prime := by
  rw [fullRecordGapTerm06407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06407_fast_pow_mod_ne_one

def fullRecordGapValue06408 : Nat := fullRecordGapCenterValue + 349242

theorem fullRecordGapTerm06408_eq_value :
    recordGapCenter + 349242 = fullRecordGapValue06408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06408 (fullRecordGapValue06408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06408_not_prime : ¬(recordGapCenter + 349242).Prime := by
  rw [fullRecordGapTerm06408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06408_fast_pow_mod_ne_one

def fullRecordGapValue06409 : Nat := fullRecordGapCenterValue + 349266

theorem fullRecordGapTerm06409_eq_value :
    recordGapCenter + 349266 = fullRecordGapValue06409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06409 (fullRecordGapValue06409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06409_not_prime : ¬(recordGapCenter + 349266).Prime := by
  rw [fullRecordGapTerm06409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06409_fast_pow_mod_ne_one

def fullRecordGapValue06410 : Nat := fullRecordGapCenterValue + 349298

theorem fullRecordGapTerm06410_eq_value :
    recordGapCenter + 349298 = fullRecordGapValue06410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06410 (fullRecordGapValue06410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06410_not_prime : ¬(recordGapCenter + 349298).Prime := by
  rw [fullRecordGapTerm06410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06410_fast_pow_mod_ne_one

def fullRecordGapValue06411 : Nat := fullRecordGapCenterValue + 349352

theorem fullRecordGapTerm06411_eq_value :
    recordGapCenter + 349352 = fullRecordGapValue06411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06411 (fullRecordGapValue06411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06411_not_prime : ¬(recordGapCenter + 349352).Prime := by
  rw [fullRecordGapTerm06411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06411_fast_pow_mod_ne_one

def fullRecordGapValue06412 : Nat := fullRecordGapCenterValue + 349358

theorem fullRecordGapTerm06412_eq_value :
    recordGapCenter + 349358 = fullRecordGapValue06412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06412 (fullRecordGapValue06412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06412_not_prime : ¬(recordGapCenter + 349358).Prime := by
  rw [fullRecordGapTerm06412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06412_fast_pow_mod_ne_one

def fullRecordGapValue06413 : Nat := fullRecordGapCenterValue + 349386

theorem fullRecordGapTerm06413_eq_value :
    recordGapCenter + 349386 = fullRecordGapValue06413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06413 (fullRecordGapValue06413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06413_not_prime : ¬(recordGapCenter + 349386).Prime := by
  rw [fullRecordGapTerm06413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06413_fast_pow_mod_ne_one

def fullRecordGapValue06414 : Nat := fullRecordGapCenterValue + 349458

theorem fullRecordGapTerm06414_eq_value :
    recordGapCenter + 349458 = fullRecordGapValue06414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06414 (fullRecordGapValue06414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06414_not_prime : ¬(recordGapCenter + 349458).Prime := by
  rw [fullRecordGapTerm06414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06414_fast_pow_mod_ne_one

def fullRecordGapValue06415 : Nat := fullRecordGapCenterValue + 349626

theorem fullRecordGapTerm06415_eq_value :
    recordGapCenter + 349626 = fullRecordGapValue06415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06415 (fullRecordGapValue06415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06415_not_prime : ¬(recordGapCenter + 349626).Prime := by
  rw [fullRecordGapTerm06415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06415_fast_pow_mod_ne_one

def fullRecordGapValue06416 : Nat := fullRecordGapCenterValue + 349658

theorem fullRecordGapTerm06416_eq_value :
    recordGapCenter + 349658 = fullRecordGapValue06416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06416 (fullRecordGapValue06416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06416_not_prime : ¬(recordGapCenter + 349658).Prime := by
  rw [fullRecordGapTerm06416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06416_fast_pow_mod_ne_one

def fullRecordGapValue06417 : Nat := fullRecordGapCenterValue + 349718

theorem fullRecordGapTerm06417_eq_value :
    recordGapCenter + 349718 = fullRecordGapValue06417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06417 (fullRecordGapValue06417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06417_not_prime : ¬(recordGapCenter + 349718).Prime := by
  rw [fullRecordGapTerm06417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06417_fast_pow_mod_ne_one

def fullRecordGapValue06418 : Nat := fullRecordGapCenterValue + 349736

theorem fullRecordGapTerm06418_eq_value :
    recordGapCenter + 349736 = fullRecordGapValue06418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06418 (fullRecordGapValue06418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06418_not_prime : ¬(recordGapCenter + 349736).Prime := by
  rw [fullRecordGapTerm06418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06418_fast_pow_mod_ne_one

def fullRecordGapValue06419 : Nat := fullRecordGapCenterValue + 349886

theorem fullRecordGapTerm06419_eq_value :
    recordGapCenter + 349886 = fullRecordGapValue06419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06419 (fullRecordGapValue06419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06419_not_prime : ¬(recordGapCenter + 349886).Prime := by
  rw [fullRecordGapTerm06419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06419_fast_pow_mod_ne_one

def fullRecordGapValue06420 : Nat := fullRecordGapCenterValue + 349920

theorem fullRecordGapTerm06420_eq_value :
    recordGapCenter + 349920 = fullRecordGapValue06420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06420 (fullRecordGapValue06420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06420_not_prime : ¬(recordGapCenter + 349920).Prime := by
  rw [fullRecordGapTerm06420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06420_fast_pow_mod_ne_one

def fullRecordGapValue06421 : Nat := fullRecordGapCenterValue + 349926

theorem fullRecordGapTerm06421_eq_value :
    recordGapCenter + 349926 = fullRecordGapValue06421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06421 (fullRecordGapValue06421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06421_not_prime : ¬(recordGapCenter + 349926).Prime := by
  rw [fullRecordGapTerm06421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06421_fast_pow_mod_ne_one

def fullRecordGapValue06422 : Nat := fullRecordGapCenterValue + 350000

theorem fullRecordGapTerm06422_eq_value :
    recordGapCenter + 350000 = fullRecordGapValue06422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06422 (fullRecordGapValue06422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06422_not_prime : ¬(recordGapCenter + 350000).Prime := by
  rw [fullRecordGapTerm06422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06422_fast_pow_mod_ne_one

def fullRecordGapValue06423 : Nat := fullRecordGapCenterValue + 350072

theorem fullRecordGapTerm06423_eq_value :
    recordGapCenter + 350072 = fullRecordGapValue06423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06423 (fullRecordGapValue06423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06423_not_prime : ¬(recordGapCenter + 350072).Prime := by
  rw [fullRecordGapTerm06423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06423_fast_pow_mod_ne_one

def fullRecordGapValue06424 : Nat := fullRecordGapCenterValue + 350156

theorem fullRecordGapTerm06424_eq_value :
    recordGapCenter + 350156 = fullRecordGapValue06424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06424 (fullRecordGapValue06424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06424_not_prime : ¬(recordGapCenter + 350156).Prime := by
  rw [fullRecordGapTerm06424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06424_fast_pow_mod_ne_one

def fullRecordGapValue06425 : Nat := fullRecordGapCenterValue + 350282

theorem fullRecordGapTerm06425_eq_value :
    recordGapCenter + 350282 = fullRecordGapValue06425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06425 (fullRecordGapValue06425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06425_not_prime : ¬(recordGapCenter + 350282).Prime := by
  rw [fullRecordGapTerm06425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06425_fast_pow_mod_ne_one

def fullRecordGapValue06426 : Nat := fullRecordGapCenterValue + 350312

theorem fullRecordGapTerm06426_eq_value :
    recordGapCenter + 350312 = fullRecordGapValue06426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06426 (fullRecordGapValue06426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06426_not_prime : ¬(recordGapCenter + 350312).Prime := by
  rw [fullRecordGapTerm06426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06426_fast_pow_mod_ne_one

def fullRecordGapValue06427 : Nat := fullRecordGapCenterValue + 350408

theorem fullRecordGapTerm06427_eq_value :
    recordGapCenter + 350408 = fullRecordGapValue06427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06427 (fullRecordGapValue06427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06427_not_prime : ¬(recordGapCenter + 350408).Prime := by
  rw [fullRecordGapTerm06427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06427_fast_pow_mod_ne_one

def fullRecordGapValue06428 : Nat := fullRecordGapCenterValue + 350418

theorem fullRecordGapTerm06428_eq_value :
    recordGapCenter + 350418 = fullRecordGapValue06428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06428 (fullRecordGapValue06428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06428_not_prime : ¬(recordGapCenter + 350418).Prime := by
  rw [fullRecordGapTerm06428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06428_fast_pow_mod_ne_one

def fullRecordGapValue06429 : Nat := fullRecordGapCenterValue + 350466

theorem fullRecordGapTerm06429_eq_value :
    recordGapCenter + 350466 = fullRecordGapValue06429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06429 (fullRecordGapValue06429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06429_not_prime : ¬(recordGapCenter + 350466).Prime := by
  rw [fullRecordGapTerm06429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06429_fast_pow_mod_ne_one

def fullRecordGapValue06430 : Nat := fullRecordGapCenterValue + 350502

theorem fullRecordGapTerm06430_eq_value :
    recordGapCenter + 350502 = fullRecordGapValue06430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06430 (fullRecordGapValue06430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06430_not_prime : ¬(recordGapCenter + 350502).Prime := by
  rw [fullRecordGapTerm06430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06430_fast_pow_mod_ne_one

def fullRecordGapValue06431 : Nat := fullRecordGapCenterValue + 350562

theorem fullRecordGapTerm06431_eq_value :
    recordGapCenter + 350562 = fullRecordGapValue06431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06431 (fullRecordGapValue06431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06431_not_prime : ¬(recordGapCenter + 350562).Prime := by
  rw [fullRecordGapTerm06431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06431_fast_pow_mod_ne_one

def fullRecordGapValue06432 : Nat := fullRecordGapCenterValue + 350582

theorem fullRecordGapTerm06432_eq_value :
    recordGapCenter + 350582 = fullRecordGapValue06432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06432 (fullRecordGapValue06432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06432_not_prime : ¬(recordGapCenter + 350582).Prime := by
  rw [fullRecordGapTerm06432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06432_fast_pow_mod_ne_one

def fullRecordGapValue06433 : Nat := fullRecordGapCenterValue + 350666

theorem fullRecordGapTerm06433_eq_value :
    recordGapCenter + 350666 = fullRecordGapValue06433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06433 (fullRecordGapValue06433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06433_not_prime : ¬(recordGapCenter + 350666).Prime := by
  rw [fullRecordGapTerm06433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06433_fast_pow_mod_ne_one

def fullRecordGapValue06434 : Nat := fullRecordGapCenterValue + 350862

theorem fullRecordGapTerm06434_eq_value :
    recordGapCenter + 350862 = fullRecordGapValue06434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06434 (fullRecordGapValue06434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06434_not_prime : ¬(recordGapCenter + 350862).Prime := by
  rw [fullRecordGapTerm06434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06434_fast_pow_mod_ne_one

def fullRecordGapValue06435 : Nat := fullRecordGapCenterValue + 350876

theorem fullRecordGapTerm06435_eq_value :
    recordGapCenter + 350876 = fullRecordGapValue06435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06435 (fullRecordGapValue06435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06435_not_prime : ¬(recordGapCenter + 350876).Prime := by
  rw [fullRecordGapTerm06435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06435_fast_pow_mod_ne_one

def fullRecordGapValue06436 : Nat := fullRecordGapCenterValue + 350936

theorem fullRecordGapTerm06436_eq_value :
    recordGapCenter + 350936 = fullRecordGapValue06436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06436 (fullRecordGapValue06436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06436_not_prime : ¬(recordGapCenter + 350936).Prime := by
  rw [fullRecordGapTerm06436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06436_fast_pow_mod_ne_one

def fullRecordGapValue06437 : Nat := fullRecordGapCenterValue + 351066

theorem fullRecordGapTerm06437_eq_value :
    recordGapCenter + 351066 = fullRecordGapValue06437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06437 (fullRecordGapValue06437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06437_not_prime : ¬(recordGapCenter + 351066).Prime := by
  rw [fullRecordGapTerm06437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06437_fast_pow_mod_ne_one

def fullRecordGapValue06438 : Nat := fullRecordGapCenterValue + 351146

theorem fullRecordGapTerm06438_eq_value :
    recordGapCenter + 351146 = fullRecordGapValue06438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06438 (fullRecordGapValue06438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06438_not_prime : ¬(recordGapCenter + 351146).Prime := by
  rw [fullRecordGapTerm06438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06438_fast_pow_mod_ne_one

def fullRecordGapValue06439 : Nat := fullRecordGapCenterValue + 351188

theorem fullRecordGapTerm06439_eq_value :
    recordGapCenter + 351188 = fullRecordGapValue06439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06439 (fullRecordGapValue06439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06439_not_prime : ¬(recordGapCenter + 351188).Prime := by
  rw [fullRecordGapTerm06439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06439_fast_pow_mod_ne_one

def fullRecordGapValue06440 : Nat := fullRecordGapCenterValue + 351222

theorem fullRecordGapTerm06440_eq_value :
    recordGapCenter + 351222 = fullRecordGapValue06440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06440 (fullRecordGapValue06440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06440_not_prime : ¬(recordGapCenter + 351222).Prime := by
  rw [fullRecordGapTerm06440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06440_fast_pow_mod_ne_one

def fullRecordGapValue06441 : Nat := fullRecordGapCenterValue + 351326

theorem fullRecordGapTerm06441_eq_value :
    recordGapCenter + 351326 = fullRecordGapValue06441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06441 (fullRecordGapValue06441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06441_not_prime : ¬(recordGapCenter + 351326).Prime := by
  rw [fullRecordGapTerm06441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06441_fast_pow_mod_ne_one

def fullRecordGapValue06442 : Nat := fullRecordGapCenterValue + 351332

theorem fullRecordGapTerm06442_eq_value :
    recordGapCenter + 351332 = fullRecordGapValue06442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06442 (fullRecordGapValue06442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06442_not_prime : ¬(recordGapCenter + 351332).Prime := by
  rw [fullRecordGapTerm06442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06442_fast_pow_mod_ne_one

def fullRecordGapValue06443 : Nat := fullRecordGapCenterValue + 351398

theorem fullRecordGapTerm06443_eq_value :
    recordGapCenter + 351398 = fullRecordGapValue06443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06443 (fullRecordGapValue06443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06443_not_prime : ¬(recordGapCenter + 351398).Prime := by
  rw [fullRecordGapTerm06443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06443_fast_pow_mod_ne_one

def fullRecordGapValue06444 : Nat := fullRecordGapCenterValue + 351506

theorem fullRecordGapTerm06444_eq_value :
    recordGapCenter + 351506 = fullRecordGapValue06444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06444 (fullRecordGapValue06444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06444_not_prime : ¬(recordGapCenter + 351506).Prime := by
  rw [fullRecordGapTerm06444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06444_fast_pow_mod_ne_one

def fullRecordGapValue06445 : Nat := fullRecordGapCenterValue + 351782

theorem fullRecordGapTerm06445_eq_value :
    recordGapCenter + 351782 = fullRecordGapValue06445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06445 (fullRecordGapValue06445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06445_not_prime : ¬(recordGapCenter + 351782).Prime := by
  rw [fullRecordGapTerm06445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06445_fast_pow_mod_ne_one

def fullRecordGapValue06446 : Nat := fullRecordGapCenterValue + 351836

theorem fullRecordGapTerm06446_eq_value :
    recordGapCenter + 351836 = fullRecordGapValue06446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06446 (fullRecordGapValue06446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06446_not_prime : ¬(recordGapCenter + 351836).Prime := by
  rw [fullRecordGapTerm06446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06446_fast_pow_mod_ne_one

def fullRecordGapValue06447 : Nat := fullRecordGapCenterValue + 351942

theorem fullRecordGapTerm06447_eq_value :
    recordGapCenter + 351942 = fullRecordGapValue06447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06447 (fullRecordGapValue06447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06447_not_prime : ¬(recordGapCenter + 351942).Prime := by
  rw [fullRecordGapTerm06447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06447_fast_pow_mod_ne_one

def fullRecordGapValue06448 : Nat := fullRecordGapCenterValue + 352046

theorem fullRecordGapTerm06448_eq_value :
    recordGapCenter + 352046 = fullRecordGapValue06448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06448 (fullRecordGapValue06448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06448_not_prime : ¬(recordGapCenter + 352046).Prime := by
  rw [fullRecordGapTerm06448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06448_fast_pow_mod_ne_one

def fullRecordGapValue06449 : Nat := fullRecordGapCenterValue + 352076

theorem fullRecordGapTerm06449_eq_value :
    recordGapCenter + 352076 = fullRecordGapValue06449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06449 (fullRecordGapValue06449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06449_not_prime : ¬(recordGapCenter + 352076).Prime := by
  rw [fullRecordGapTerm06449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06449_fast_pow_mod_ne_one

def fullRecordGapValue06450 : Nat := fullRecordGapCenterValue + 352082

theorem fullRecordGapTerm06450_eq_value :
    recordGapCenter + 352082 = fullRecordGapValue06450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06450 (fullRecordGapValue06450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06450_not_prime : ¬(recordGapCenter + 352082).Prime := by
  rw [fullRecordGapTerm06450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06450_fast_pow_mod_ne_one

def fullRecordGapValue06451 : Nat := fullRecordGapCenterValue + 352122

theorem fullRecordGapTerm06451_eq_value :
    recordGapCenter + 352122 = fullRecordGapValue06451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06451 (fullRecordGapValue06451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06451_not_prime : ¬(recordGapCenter + 352122).Prime := by
  rw [fullRecordGapTerm06451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06451_fast_pow_mod_ne_one

def fullRecordGapValue06452 : Nat := fullRecordGapCenterValue + 352158

theorem fullRecordGapTerm06452_eq_value :
    recordGapCenter + 352158 = fullRecordGapValue06452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06452 (fullRecordGapValue06452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06452_not_prime : ¬(recordGapCenter + 352158).Prime := by
  rw [fullRecordGapTerm06452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06452_fast_pow_mod_ne_one

def fullRecordGapValue06453 : Nat := fullRecordGapCenterValue + 352266

theorem fullRecordGapTerm06453_eq_value :
    recordGapCenter + 352266 = fullRecordGapValue06453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06453 (fullRecordGapValue06453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06453_not_prime : ¬(recordGapCenter + 352266).Prime := by
  rw [fullRecordGapTerm06453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06453_fast_pow_mod_ne_one

def fullRecordGapValue06454 : Nat := fullRecordGapCenterValue + 352322

theorem fullRecordGapTerm06454_eq_value :
    recordGapCenter + 352322 = fullRecordGapValue06454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06454 (fullRecordGapValue06454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06454_not_prime : ¬(recordGapCenter + 352322).Prime := by
  rw [fullRecordGapTerm06454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06454_fast_pow_mod_ne_one

def fullRecordGapValue06455 : Nat := fullRecordGapCenterValue + 352382

theorem fullRecordGapTerm06455_eq_value :
    recordGapCenter + 352382 = fullRecordGapValue06455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06455 (fullRecordGapValue06455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06455_not_prime : ¬(recordGapCenter + 352382).Prime := by
  rw [fullRecordGapTerm06455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06455_fast_pow_mod_ne_one

def fullRecordGapValue06456 : Nat := fullRecordGapCenterValue + 352398

theorem fullRecordGapTerm06456_eq_value :
    recordGapCenter + 352398 = fullRecordGapValue06456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06456 (fullRecordGapValue06456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06456_not_prime : ¬(recordGapCenter + 352398).Prime := by
  rw [fullRecordGapTerm06456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06456_fast_pow_mod_ne_one

def fullRecordGapValue06457 : Nat := fullRecordGapCenterValue + 352472

theorem fullRecordGapTerm06457_eq_value :
    recordGapCenter + 352472 = fullRecordGapValue06457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06457 (fullRecordGapValue06457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06457_not_prime : ¬(recordGapCenter + 352472).Prime := by
  rw [fullRecordGapTerm06457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06457_fast_pow_mod_ne_one

def fullRecordGapValue06458 : Nat := fullRecordGapCenterValue + 352542

theorem fullRecordGapTerm06458_eq_value :
    recordGapCenter + 352542 = fullRecordGapValue06458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06458 (fullRecordGapValue06458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06458_not_prime : ¬(recordGapCenter + 352542).Prime := by
  rw [fullRecordGapTerm06458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06458_fast_pow_mod_ne_one

def fullRecordGapValue06459 : Nat := fullRecordGapCenterValue + 352626

theorem fullRecordGapTerm06459_eq_value :
    recordGapCenter + 352626 = fullRecordGapValue06459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06459 (fullRecordGapValue06459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06459_not_prime : ¬(recordGapCenter + 352626).Prime := by
  rw [fullRecordGapTerm06459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06459_fast_pow_mod_ne_one

def fullRecordGapValue06460 : Nat := fullRecordGapCenterValue + 352800

theorem fullRecordGapTerm06460_eq_value :
    recordGapCenter + 352800 = fullRecordGapValue06460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06460 (fullRecordGapValue06460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06460_not_prime : ¬(recordGapCenter + 352800).Prime := by
  rw [fullRecordGapTerm06460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06460_fast_pow_mod_ne_one

def fullRecordGapValue06461 : Nat := fullRecordGapCenterValue + 352808

theorem fullRecordGapTerm06461_eq_value :
    recordGapCenter + 352808 = fullRecordGapValue06461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06461 (fullRecordGapValue06461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06461_not_prime : ¬(recordGapCenter + 352808).Prime := by
  rw [fullRecordGapTerm06461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06461_fast_pow_mod_ne_one

def fullRecordGapValue06462 : Nat := fullRecordGapCenterValue + 352892

theorem fullRecordGapTerm06462_eq_value :
    recordGapCenter + 352892 = fullRecordGapValue06462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06462 (fullRecordGapValue06462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06462_not_prime : ¬(recordGapCenter + 352892).Prime := by
  rw [fullRecordGapTerm06462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06462_fast_pow_mod_ne_one

def fullRecordGapValue06463 : Nat := fullRecordGapCenterValue + 352952

theorem fullRecordGapTerm06463_eq_value :
    recordGapCenter + 352952 = fullRecordGapValue06463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06463 (fullRecordGapValue06463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06463_not_prime : ¬(recordGapCenter + 352952).Prime := by
  rw [fullRecordGapTerm06463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06463_fast_pow_mod_ne_one

def fullRecordGapValue06464 : Nat := fullRecordGapCenterValue + 353018

theorem fullRecordGapTerm06464_eq_value :
    recordGapCenter + 353018 = fullRecordGapValue06464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06464 (fullRecordGapValue06464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06464_not_prime : ¬(recordGapCenter + 353018).Prime := by
  rw [fullRecordGapTerm06464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06464_fast_pow_mod_ne_one

def fullRecordGapValue06465 : Nat := fullRecordGapCenterValue + 353042

theorem fullRecordGapTerm06465_eq_value :
    recordGapCenter + 353042 = fullRecordGapValue06465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06465 (fullRecordGapValue06465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06465_not_prime : ¬(recordGapCenter + 353042).Prime := by
  rw [fullRecordGapTerm06465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06465_fast_pow_mod_ne_one

def fullRecordGapValue06466 : Nat := fullRecordGapCenterValue + 353048

theorem fullRecordGapTerm06466_eq_value :
    recordGapCenter + 353048 = fullRecordGapValue06466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06466 (fullRecordGapValue06466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06466_not_prime : ¬(recordGapCenter + 353048).Prime := by
  rw [fullRecordGapTerm06466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06466_fast_pow_mod_ne_one

def fullRecordGapValue06467 : Nat := fullRecordGapCenterValue + 353222

theorem fullRecordGapTerm06467_eq_value :
    recordGapCenter + 353222 = fullRecordGapValue06467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06467 (fullRecordGapValue06467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06467_not_prime : ¬(recordGapCenter + 353222).Prime := by
  rw [fullRecordGapTerm06467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06467_fast_pow_mod_ne_one

def fullRecordGapValue06468 : Nat := fullRecordGapCenterValue + 353348

theorem fullRecordGapTerm06468_eq_value :
    recordGapCenter + 353348 = fullRecordGapValue06468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06468 (fullRecordGapValue06468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06468_not_prime : ¬(recordGapCenter + 353348).Prime := by
  rw [fullRecordGapTerm06468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06468_fast_pow_mod_ne_one

def fullRecordGapValue06469 : Nat := fullRecordGapCenterValue + 353406

theorem fullRecordGapTerm06469_eq_value :
    recordGapCenter + 353406 = fullRecordGapValue06469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06469 (fullRecordGapValue06469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06469_not_prime : ¬(recordGapCenter + 353406).Prime := by
  rw [fullRecordGapTerm06469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06469_fast_pow_mod_ne_one

def fullRecordGapValue06470 : Nat := fullRecordGapCenterValue + 353442

theorem fullRecordGapTerm06470_eq_value :
    recordGapCenter + 353442 = fullRecordGapValue06470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06470 (fullRecordGapValue06470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06470_not_prime : ¬(recordGapCenter + 353442).Prime := by
  rw [fullRecordGapTerm06470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06470_fast_pow_mod_ne_one

def fullRecordGapValue06471 : Nat := fullRecordGapCenterValue + 353516

theorem fullRecordGapTerm06471_eq_value :
    recordGapCenter + 353516 = fullRecordGapValue06471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06471 (fullRecordGapValue06471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06471_not_prime : ¬(recordGapCenter + 353516).Prime := by
  rw [fullRecordGapTerm06471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06471_fast_pow_mod_ne_one

def fullRecordGapValue06472 : Nat := fullRecordGapCenterValue + 353658

theorem fullRecordGapTerm06472_eq_value :
    recordGapCenter + 353658 = fullRecordGapValue06472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06472 (fullRecordGapValue06472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06472_not_prime : ¬(recordGapCenter + 353658).Prime := by
  rw [fullRecordGapTerm06472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06472_fast_pow_mod_ne_one

def fullRecordGapValue06473 : Nat := fullRecordGapCenterValue + 353768

theorem fullRecordGapTerm06473_eq_value :
    recordGapCenter + 353768 = fullRecordGapValue06473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06473 (fullRecordGapValue06473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06473_not_prime : ¬(recordGapCenter + 353768).Prime := by
  rw [fullRecordGapTerm06473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06473_fast_pow_mod_ne_one

def fullRecordGapValue06474 : Nat := fullRecordGapCenterValue + 353876

theorem fullRecordGapTerm06474_eq_value :
    recordGapCenter + 353876 = fullRecordGapValue06474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06474 (fullRecordGapValue06474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06474_not_prime : ¬(recordGapCenter + 353876).Prime := by
  rw [fullRecordGapTerm06474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06474_fast_pow_mod_ne_one

def fullRecordGapValue06475 : Nat := fullRecordGapCenterValue + 353946

theorem fullRecordGapTerm06475_eq_value :
    recordGapCenter + 353946 = fullRecordGapValue06475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06475 (fullRecordGapValue06475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06475_not_prime : ¬(recordGapCenter + 353946).Prime := by
  rw [fullRecordGapTerm06475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06475_fast_pow_mod_ne_one

def fullRecordGapValue06476 : Nat := fullRecordGapCenterValue + 353966

theorem fullRecordGapTerm06476_eq_value :
    recordGapCenter + 353966 = fullRecordGapValue06476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06476 (fullRecordGapValue06476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06476_not_prime : ¬(recordGapCenter + 353966).Prime := by
  rw [fullRecordGapTerm06476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06476_fast_pow_mod_ne_one

def fullRecordGapValue06477 : Nat := fullRecordGapCenterValue + 353972

theorem fullRecordGapTerm06477_eq_value :
    recordGapCenter + 353972 = fullRecordGapValue06477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06477 (fullRecordGapValue06477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06477_not_prime : ¬(recordGapCenter + 353972).Prime := by
  rw [fullRecordGapTerm06477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06477_fast_pow_mod_ne_one

def fullRecordGapValue06478 : Nat := fullRecordGapCenterValue + 354092

theorem fullRecordGapTerm06478_eq_value :
    recordGapCenter + 354092 = fullRecordGapValue06478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06478 (fullRecordGapValue06478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06478_not_prime : ¬(recordGapCenter + 354092).Prime := by
  rw [fullRecordGapTerm06478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06478_fast_pow_mod_ne_one

def fullRecordGapValue06479 : Nat := fullRecordGapCenterValue + 354126

theorem fullRecordGapTerm06479_eq_value :
    recordGapCenter + 354126 = fullRecordGapValue06479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06479 (fullRecordGapValue06479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06479_not_prime : ¬(recordGapCenter + 354126).Prime := by
  rw [fullRecordGapTerm06479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06479_fast_pow_mod_ne_one

def fullRecordGapValue06480 : Nat := fullRecordGapCenterValue + 354182

theorem fullRecordGapTerm06480_eq_value :
    recordGapCenter + 354182 = fullRecordGapValue06480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06480 (fullRecordGapValue06480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06480_not_prime : ¬(recordGapCenter + 354182).Prime := by
  rw [fullRecordGapTerm06480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06480_fast_pow_mod_ne_one

def fullRecordGapValue06481 : Nat := fullRecordGapCenterValue + 354422

theorem fullRecordGapTerm06481_eq_value :
    recordGapCenter + 354422 = fullRecordGapValue06481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06481 (fullRecordGapValue06481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06481_not_prime : ¬(recordGapCenter + 354422).Prime := by
  rw [fullRecordGapTerm06481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06481_fast_pow_mod_ne_one

def fullRecordGapValue06482 : Nat := fullRecordGapCenterValue + 354446

theorem fullRecordGapTerm06482_eq_value :
    recordGapCenter + 354446 = fullRecordGapValue06482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06482 (fullRecordGapValue06482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06482_not_prime : ¬(recordGapCenter + 354446).Prime := by
  rw [fullRecordGapTerm06482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06482_fast_pow_mod_ne_one

def fullRecordGapValue06483 : Nat := fullRecordGapCenterValue + 354572

theorem fullRecordGapTerm06483_eq_value :
    recordGapCenter + 354572 = fullRecordGapValue06483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06483 (fullRecordGapValue06483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06483_not_prime : ¬(recordGapCenter + 354572).Prime := by
  rw [fullRecordGapTerm06483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06483_fast_pow_mod_ne_one

def fullRecordGapValue06484 : Nat := fullRecordGapCenterValue + 354758

theorem fullRecordGapTerm06484_eq_value :
    recordGapCenter + 354758 = fullRecordGapValue06484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06484 (fullRecordGapValue06484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06484_not_prime : ¬(recordGapCenter + 354758).Prime := by
  rw [fullRecordGapTerm06484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06484_fast_pow_mod_ne_one

def fullRecordGapValue06485 : Nat := fullRecordGapCenterValue + 354816

theorem fullRecordGapTerm06485_eq_value :
    recordGapCenter + 354816 = fullRecordGapValue06485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06485 (fullRecordGapValue06485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06485_not_prime : ¬(recordGapCenter + 354816).Prime := by
  rw [fullRecordGapTerm06485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06485_fast_pow_mod_ne_one

def fullRecordGapValue06486 : Nat := fullRecordGapCenterValue + 354842

theorem fullRecordGapTerm06486_eq_value :
    recordGapCenter + 354842 = fullRecordGapValue06486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06486 (fullRecordGapValue06486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06486_not_prime : ¬(recordGapCenter + 354842).Prime := by
  rw [fullRecordGapTerm06486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06486_fast_pow_mod_ne_one

def fullRecordGapValue06487 : Nat := fullRecordGapCenterValue + 354846

theorem fullRecordGapTerm06487_eq_value :
    recordGapCenter + 354846 = fullRecordGapValue06487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06487 (fullRecordGapValue06487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06487_not_prime : ¬(recordGapCenter + 354846).Prime := by
  rw [fullRecordGapTerm06487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06487_fast_pow_mod_ne_one

def fullRecordGapValue06488 : Nat := fullRecordGapCenterValue + 355002

theorem fullRecordGapTerm06488_eq_value :
    recordGapCenter + 355002 = fullRecordGapValue06488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06488 (fullRecordGapValue06488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06488_not_prime : ¬(recordGapCenter + 355002).Prime := by
  rw [fullRecordGapTerm06488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06488_fast_pow_mod_ne_one

def fullRecordGapValue06489 : Nat := fullRecordGapCenterValue + 355022

theorem fullRecordGapTerm06489_eq_value :
    recordGapCenter + 355022 = fullRecordGapValue06489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06489 (fullRecordGapValue06489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06489_not_prime : ¬(recordGapCenter + 355022).Prime := by
  rw [fullRecordGapTerm06489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06489_fast_pow_mod_ne_one

def fullRecordGapValue06490 : Nat := fullRecordGapCenterValue + 355182

theorem fullRecordGapTerm06490_eq_value :
    recordGapCenter + 355182 = fullRecordGapValue06490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06490 (fullRecordGapValue06490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06490_not_prime : ¬(recordGapCenter + 355182).Prime := by
  rw [fullRecordGapTerm06490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06490_fast_pow_mod_ne_one

def fullRecordGapValue06491 : Nat := fullRecordGapCenterValue + 355478

theorem fullRecordGapTerm06491_eq_value :
    recordGapCenter + 355478 = fullRecordGapValue06491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06491 (fullRecordGapValue06491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06491_not_prime : ¬(recordGapCenter + 355478).Prime := by
  rw [fullRecordGapTerm06491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06491_fast_pow_mod_ne_one

def fullRecordGapValue06492 : Nat := fullRecordGapCenterValue + 355526

theorem fullRecordGapTerm06492_eq_value :
    recordGapCenter + 355526 = fullRecordGapValue06492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06492 (fullRecordGapValue06492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06492_not_prime : ¬(recordGapCenter + 355526).Prime := by
  rw [fullRecordGapTerm06492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06492_fast_pow_mod_ne_one

def fullRecordGapValue06493 : Nat := fullRecordGapCenterValue + 355622

theorem fullRecordGapTerm06493_eq_value :
    recordGapCenter + 355622 = fullRecordGapValue06493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06493 (fullRecordGapValue06493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06493_not_prime : ¬(recordGapCenter + 355622).Prime := by
  rw [fullRecordGapTerm06493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06493_fast_pow_mod_ne_one

def fullRecordGapValue06494 : Nat := fullRecordGapCenterValue + 355638

theorem fullRecordGapTerm06494_eq_value :
    recordGapCenter + 355638 = fullRecordGapValue06494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06494 (fullRecordGapValue06494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06494_not_prime : ¬(recordGapCenter + 355638).Prime := by
  rw [fullRecordGapTerm06494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06494_fast_pow_mod_ne_one

def fullRecordGapValue06495 : Nat := fullRecordGapCenterValue + 355686

theorem fullRecordGapTerm06495_eq_value :
    recordGapCenter + 355686 = fullRecordGapValue06495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06495 (fullRecordGapValue06495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06495_not_prime : ¬(recordGapCenter + 355686).Prime := by
  rw [fullRecordGapTerm06495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06495_fast_pow_mod_ne_one

def fullRecordGapValue06496 : Nat := fullRecordGapCenterValue + 355766

theorem fullRecordGapTerm06496_eq_value :
    recordGapCenter + 355766 = fullRecordGapValue06496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06496 (fullRecordGapValue06496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06496_not_prime : ¬(recordGapCenter + 355766).Prime := by
  rw [fullRecordGapTerm06496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06496_fast_pow_mod_ne_one

def fullRecordGapValue06497 : Nat := fullRecordGapCenterValue + 355826

theorem fullRecordGapTerm06497_eq_value :
    recordGapCenter + 355826 = fullRecordGapValue06497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06497 (fullRecordGapValue06497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06497_not_prime : ¬(recordGapCenter + 355826).Prime := by
  rw [fullRecordGapTerm06497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06497_fast_pow_mod_ne_one

def fullRecordGapValue06498 : Nat := fullRecordGapCenterValue + 355988

theorem fullRecordGapTerm06498_eq_value :
    recordGapCenter + 355988 = fullRecordGapValue06498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06498 (fullRecordGapValue06498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06498_not_prime : ¬(recordGapCenter + 355988).Prime := by
  rw [fullRecordGapTerm06498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06498_fast_pow_mod_ne_one

def fullRecordGapValue06499 : Nat := fullRecordGapCenterValue + 356036

theorem fullRecordGapTerm06499_eq_value :
    recordGapCenter + 356036 = fullRecordGapValue06499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06499 (fullRecordGapValue06499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06499_not_prime : ¬(recordGapCenter + 356036).Prime := by
  rw [fullRecordGapTerm06499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06499_fast_pow_mod_ne_one

def fullRecordGapValue06500 : Nat := fullRecordGapCenterValue + 356042

theorem fullRecordGapTerm06500_eq_value :
    recordGapCenter + 356042 = fullRecordGapValue06500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06500 (fullRecordGapValue06500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06500_not_prime : ¬(recordGapCenter + 356042).Prime := by
  rw [fullRecordGapTerm06500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06500_fast_pow_mod_ne_one

def fullRecordGapValue06501 : Nat := fullRecordGapCenterValue + 356186

theorem fullRecordGapTerm06501_eq_value :
    recordGapCenter + 356186 = fullRecordGapValue06501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06501 (fullRecordGapValue06501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06501_not_prime : ¬(recordGapCenter + 356186).Prime := by
  rw [fullRecordGapTerm06501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06501_fast_pow_mod_ne_one

def fullRecordGapValue06502 : Nat := fullRecordGapCenterValue + 356228

theorem fullRecordGapTerm06502_eq_value :
    recordGapCenter + 356228 = fullRecordGapValue06502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06502 (fullRecordGapValue06502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06502_not_prime : ¬(recordGapCenter + 356228).Prime := by
  rw [fullRecordGapTerm06502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06502_fast_pow_mod_ne_one

def fullRecordGapValue06503 : Nat := fullRecordGapCenterValue + 356276

theorem fullRecordGapTerm06503_eq_value :
    recordGapCenter + 356276 = fullRecordGapValue06503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06503 (fullRecordGapValue06503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06503_not_prime : ¬(recordGapCenter + 356276).Prime := by
  rw [fullRecordGapTerm06503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06503_fast_pow_mod_ne_one

def fullRecordGapValue06504 : Nat := fullRecordGapCenterValue + 356322

theorem fullRecordGapTerm06504_eq_value :
    recordGapCenter + 356322 = fullRecordGapValue06504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06504 (fullRecordGapValue06504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06504_not_prime : ¬(recordGapCenter + 356322).Prime := by
  rw [fullRecordGapTerm06504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06504_fast_pow_mod_ne_one

def fullRecordGapValue06505 : Nat := fullRecordGapCenterValue + 356358

theorem fullRecordGapTerm06505_eq_value :
    recordGapCenter + 356358 = fullRecordGapValue06505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06505 (fullRecordGapValue06505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06505_not_prime : ¬(recordGapCenter + 356358).Prime := by
  rw [fullRecordGapTerm06505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06505_fast_pow_mod_ne_one

def fullRecordGapValue06506 : Nat := fullRecordGapCenterValue + 356492

theorem fullRecordGapTerm06506_eq_value :
    recordGapCenter + 356492 = fullRecordGapValue06506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06506 (fullRecordGapValue06506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06506_not_prime : ¬(recordGapCenter + 356492).Prime := by
  rw [fullRecordGapTerm06506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06506_fast_pow_mod_ne_one

def fullRecordGapValue06507 : Nat := fullRecordGapCenterValue + 356498

theorem fullRecordGapTerm06507_eq_value :
    recordGapCenter + 356498 = fullRecordGapValue06507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06507 (fullRecordGapValue06507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06507_not_prime : ¬(recordGapCenter + 356498).Prime := by
  rw [fullRecordGapTerm06507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06507_fast_pow_mod_ne_one

def fullRecordGapValue06508 : Nat := fullRecordGapCenterValue + 356666

theorem fullRecordGapTerm06508_eq_value :
    recordGapCenter + 356666 = fullRecordGapValue06508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06508 (fullRecordGapValue06508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06508_not_prime : ¬(recordGapCenter + 356666).Prime := by
  rw [fullRecordGapTerm06508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06508_fast_pow_mod_ne_one

def fullRecordGapValue06509 : Nat := fullRecordGapCenterValue + 356786

theorem fullRecordGapTerm06509_eq_value :
    recordGapCenter + 356786 = fullRecordGapValue06509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06509 (fullRecordGapValue06509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06509_not_prime : ¬(recordGapCenter + 356786).Prime := by
  rw [fullRecordGapTerm06509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06509_fast_pow_mod_ne_one

def fullRecordGapValue06510 : Nat := fullRecordGapCenterValue + 356802

theorem fullRecordGapTerm06510_eq_value :
    recordGapCenter + 356802 = fullRecordGapValue06510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06510 (fullRecordGapValue06510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06510_not_prime : ¬(recordGapCenter + 356802).Prime := by
  rw [fullRecordGapTerm06510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06510_fast_pow_mod_ne_one

def fullRecordGapValue06511 : Nat := fullRecordGapCenterValue + 356882

theorem fullRecordGapTerm06511_eq_value :
    recordGapCenter + 356882 = fullRecordGapValue06511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06511 (fullRecordGapValue06511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06511_not_prime : ¬(recordGapCenter + 356882).Prime := by
  rw [fullRecordGapTerm06511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06511_fast_pow_mod_ne_one

def fullRecordGapValue06512 : Nat := fullRecordGapCenterValue + 356948

theorem fullRecordGapTerm06512_eq_value :
    recordGapCenter + 356948 = fullRecordGapValue06512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06512 (fullRecordGapValue06512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06512_not_prime : ¬(recordGapCenter + 356948).Prime := by
  rw [fullRecordGapTerm06512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06512_fast_pow_mod_ne_one

def fullRecordGapValue06513 : Nat := fullRecordGapCenterValue + 356982

theorem fullRecordGapTerm06513_eq_value :
    recordGapCenter + 356982 = fullRecordGapValue06513 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06513_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06513 (fullRecordGapValue06513 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06513_not_prime : ¬(recordGapCenter + 356982).Prime := by
  rw [fullRecordGapTerm06513_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06513, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06513_fast_pow_mod_ne_one

def fullRecordGapValue06514 : Nat := fullRecordGapCenterValue + 357002

theorem fullRecordGapTerm06514_eq_value :
    recordGapCenter + 357002 = fullRecordGapValue06514 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06514_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06514 (fullRecordGapValue06514 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06514_not_prime : ¬(recordGapCenter + 357002).Prime := by
  rw [fullRecordGapTerm06514_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06514, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06514_fast_pow_mod_ne_one

def fullRecordGapValue06515 : Nat := fullRecordGapCenterValue + 357026

theorem fullRecordGapTerm06515_eq_value :
    recordGapCenter + 357026 = fullRecordGapValue06515 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06515_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06515 (fullRecordGapValue06515 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06515_not_prime : ¬(recordGapCenter + 357026).Prime := by
  rw [fullRecordGapTerm06515_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06515, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06515_fast_pow_mod_ne_one

def fullRecordGapValue06516 : Nat := fullRecordGapCenterValue + 357092

theorem fullRecordGapTerm06516_eq_value :
    recordGapCenter + 357092 = fullRecordGapValue06516 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06516_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06516 (fullRecordGapValue06516 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06516_not_prime : ¬(recordGapCenter + 357092).Prime := by
  rw [fullRecordGapTerm06516_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06516, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06516_fast_pow_mod_ne_one

def fullRecordGapValue06517 : Nat := fullRecordGapCenterValue + 357218

theorem fullRecordGapTerm06517_eq_value :
    recordGapCenter + 357218 = fullRecordGapValue06517 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06517_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06517 (fullRecordGapValue06517 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06517_not_prime : ¬(recordGapCenter + 357218).Prime := by
  rw [fullRecordGapTerm06517_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06517, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06517_fast_pow_mod_ne_one

def fullRecordGapValue06518 : Nat := fullRecordGapCenterValue + 357242

theorem fullRecordGapTerm06518_eq_value :
    recordGapCenter + 357242 = fullRecordGapValue06518 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06518_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06518 (fullRecordGapValue06518 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06518_not_prime : ¬(recordGapCenter + 357242).Prime := by
  rw [fullRecordGapTerm06518_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06518, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06518_fast_pow_mod_ne_one

def fullRecordGapValue06519 : Nat := fullRecordGapCenterValue + 357402

theorem fullRecordGapTerm06519_eq_value :
    recordGapCenter + 357402 = fullRecordGapValue06519 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06519_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06519 (fullRecordGapValue06519 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06519_not_prime : ¬(recordGapCenter + 357402).Prime := by
  rw [fullRecordGapTerm06519_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06519, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06519_fast_pow_mod_ne_one

def fullRecordGapValue06520 : Nat := fullRecordGapCenterValue + 357548

theorem fullRecordGapTerm06520_eq_value :
    recordGapCenter + 357548 = fullRecordGapValue06520 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06520_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06520 (fullRecordGapValue06520 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06520_not_prime : ¬(recordGapCenter + 357548).Prime := by
  rw [fullRecordGapTerm06520_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06520, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06520_fast_pow_mod_ne_one

def fullRecordGapValue06521 : Nat := fullRecordGapCenterValue + 357596

theorem fullRecordGapTerm06521_eq_value :
    recordGapCenter + 357596 = fullRecordGapValue06521 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06521_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06521 (fullRecordGapValue06521 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06521_not_prime : ¬(recordGapCenter + 357596).Prime := by
  rw [fullRecordGapTerm06521_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06521, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06521_fast_pow_mod_ne_one

def fullRecordGapValue06522 : Nat := fullRecordGapCenterValue + 357662

theorem fullRecordGapTerm06522_eq_value :
    recordGapCenter + 357662 = fullRecordGapValue06522 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06522_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06522 (fullRecordGapValue06522 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06522_not_prime : ¬(recordGapCenter + 357662).Prime := by
  rw [fullRecordGapTerm06522_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06522, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06522_fast_pow_mod_ne_one

def fullRecordGapValue06523 : Nat := fullRecordGapCenterValue + 357668

theorem fullRecordGapTerm06523_eq_value :
    recordGapCenter + 357668 = fullRecordGapValue06523 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06523_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06523 (fullRecordGapValue06523 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06523_not_prime : ¬(recordGapCenter + 357668).Prime := by
  rw [fullRecordGapTerm06523_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06523, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06523_fast_pow_mod_ne_one

def fullRecordGapValue06524 : Nat := fullRecordGapCenterValue + 357726

theorem fullRecordGapTerm06524_eq_value :
    recordGapCenter + 357726 = fullRecordGapValue06524 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06524_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06524 (fullRecordGapValue06524 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06524_not_prime : ¬(recordGapCenter + 357726).Prime := by
  rw [fullRecordGapTerm06524_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06524, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06524_fast_pow_mod_ne_one

def fullRecordGapValue06525 : Nat := fullRecordGapCenterValue + 357746

theorem fullRecordGapTerm06525_eq_value :
    recordGapCenter + 357746 = fullRecordGapValue06525 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06525_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06525 (fullRecordGapValue06525 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06525_not_prime : ¬(recordGapCenter + 357746).Prime := by
  rw [fullRecordGapTerm06525_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06525, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06525_fast_pow_mod_ne_one

def fullRecordGapValue06526 : Nat := fullRecordGapCenterValue + 357806

theorem fullRecordGapTerm06526_eq_value :
    recordGapCenter + 357806 = fullRecordGapValue06526 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06526_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06526 (fullRecordGapValue06526 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06526_not_prime : ¬(recordGapCenter + 357806).Prime := by
  rw [fullRecordGapTerm06526_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06526, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06526_fast_pow_mod_ne_one

def fullRecordGapValue06527 : Nat := fullRecordGapCenterValue + 357908

theorem fullRecordGapTerm06527_eq_value :
    recordGapCenter + 357908 = fullRecordGapValue06527 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06527_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06527 (fullRecordGapValue06527 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06527_not_prime : ¬(recordGapCenter + 357908).Prime := by
  rw [fullRecordGapTerm06527_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06527, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06527_fast_pow_mod_ne_one

def fullRecordGapValue06528 : Nat := fullRecordGapCenterValue + 357978

theorem fullRecordGapTerm06528_eq_value :
    recordGapCenter + 357978 = fullRecordGapValue06528 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06528_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06528 (fullRecordGapValue06528 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06528_not_prime : ¬(recordGapCenter + 357978).Prime := by
  rw [fullRecordGapTerm06528_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06528, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06528_fast_pow_mod_ne_one

def fullRecordGapValue06529 : Nat := fullRecordGapCenterValue + 358076

theorem fullRecordGapTerm06529_eq_value :
    recordGapCenter + 358076 = fullRecordGapValue06529 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06529_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06529 (fullRecordGapValue06529 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06529_not_prime : ¬(recordGapCenter + 358076).Prime := by
  rw [fullRecordGapTerm06529_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06529, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06529_fast_pow_mod_ne_one

def fullRecordGapValue06530 : Nat := fullRecordGapCenterValue + 358082

theorem fullRecordGapTerm06530_eq_value :
    recordGapCenter + 358082 = fullRecordGapValue06530 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06530_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06530 (fullRecordGapValue06530 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06530_not_prime : ¬(recordGapCenter + 358082).Prime := by
  rw [fullRecordGapTerm06530_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06530, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06530_fast_pow_mod_ne_one

def fullRecordGapValue06531 : Nat := fullRecordGapCenterValue + 358158

theorem fullRecordGapTerm06531_eq_value :
    recordGapCenter + 358158 = fullRecordGapValue06531 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06531_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06531 (fullRecordGapValue06531 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06531_not_prime : ¬(recordGapCenter + 358158).Prime := by
  rw [fullRecordGapTerm06531_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06531, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06531_fast_pow_mod_ne_one

def fullRecordGapValue06532 : Nat := fullRecordGapCenterValue + 358166

theorem fullRecordGapTerm06532_eq_value :
    recordGapCenter + 358166 = fullRecordGapValue06532 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06532_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06532 (fullRecordGapValue06532 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06532_not_prime : ¬(recordGapCenter + 358166).Prime := by
  rw [fullRecordGapTerm06532_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06532, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06532_fast_pow_mod_ne_one

def fullRecordGapValue06533 : Nat := fullRecordGapCenterValue + 358286

theorem fullRecordGapTerm06533_eq_value :
    recordGapCenter + 358286 = fullRecordGapValue06533 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06533_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06533 (fullRecordGapValue06533 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06533_not_prime : ¬(recordGapCenter + 358286).Prime := by
  rw [fullRecordGapTerm06533_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06533, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06533_fast_pow_mod_ne_one

def fullRecordGapValue06534 : Nat := fullRecordGapCenterValue + 358338

theorem fullRecordGapTerm06534_eq_value :
    recordGapCenter + 358338 = fullRecordGapValue06534 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06534_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06534 (fullRecordGapValue06534 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06534_not_prime : ¬(recordGapCenter + 358338).Prime := by
  rw [fullRecordGapTerm06534_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06534, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06534_fast_pow_mod_ne_one

def fullRecordGapValue06535 : Nat := fullRecordGapCenterValue + 358400

theorem fullRecordGapTerm06535_eq_value :
    recordGapCenter + 358400 = fullRecordGapValue06535 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06535_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06535 (fullRecordGapValue06535 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06535_not_prime : ¬(recordGapCenter + 358400).Prime := by
  rw [fullRecordGapTerm06535_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06535, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06535_fast_pow_mod_ne_one

def fullRecordGapValue06536 : Nat := fullRecordGapCenterValue + 358412

theorem fullRecordGapTerm06536_eq_value :
    recordGapCenter + 358412 = fullRecordGapValue06536 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06536_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06536 (fullRecordGapValue06536 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06536_not_prime : ¬(recordGapCenter + 358412).Prime := by
  rw [fullRecordGapTerm06536_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06536, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06536_fast_pow_mod_ne_one

def fullRecordGapValue06537 : Nat := fullRecordGapCenterValue + 358458

theorem fullRecordGapTerm06537_eq_value :
    recordGapCenter + 358458 = fullRecordGapValue06537 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06537_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06537 (fullRecordGapValue06537 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06537_not_prime : ¬(recordGapCenter + 358458).Prime := by
  rw [fullRecordGapTerm06537_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06537, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06537_fast_pow_mod_ne_one

def fullRecordGapValue06538 : Nat := fullRecordGapCenterValue + 358538

theorem fullRecordGapTerm06538_eq_value :
    recordGapCenter + 358538 = fullRecordGapValue06538 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06538_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06538 (fullRecordGapValue06538 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06538_not_prime : ¬(recordGapCenter + 358538).Prime := by
  rw [fullRecordGapTerm06538_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06538, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06538_fast_pow_mod_ne_one

def fullRecordGapValue06539 : Nat := fullRecordGapCenterValue + 358562

theorem fullRecordGapTerm06539_eq_value :
    recordGapCenter + 358562 = fullRecordGapValue06539 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06539_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06539 (fullRecordGapValue06539 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06539_not_prime : ¬(recordGapCenter + 358562).Prime := by
  rw [fullRecordGapTerm06539_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06539, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06539_fast_pow_mod_ne_one

def fullRecordGapValue06540 : Nat := fullRecordGapCenterValue + 358676

theorem fullRecordGapTerm06540_eq_value :
    recordGapCenter + 358676 = fullRecordGapValue06540 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06540_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06540 (fullRecordGapValue06540 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06540_not_prime : ¬(recordGapCenter + 358676).Prime := by
  rw [fullRecordGapTerm06540_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06540, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06540_fast_pow_mod_ne_one

def fullRecordGapValue06541 : Nat := fullRecordGapCenterValue + 358782

theorem fullRecordGapTerm06541_eq_value :
    recordGapCenter + 358782 = fullRecordGapValue06541 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06541_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06541 (fullRecordGapValue06541 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06541_not_prime : ¬(recordGapCenter + 358782).Prime := by
  rw [fullRecordGapTerm06541_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06541, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06541_fast_pow_mod_ne_one

def fullRecordGapValue06542 : Nat := fullRecordGapCenterValue + 358922

theorem fullRecordGapTerm06542_eq_value :
    recordGapCenter + 358922 = fullRecordGapValue06542 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06542_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06542 (fullRecordGapValue06542 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06542_not_prime : ¬(recordGapCenter + 358922).Prime := by
  rw [fullRecordGapTerm06542_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06542, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06542_fast_pow_mod_ne_one

def fullRecordGapValue06543 : Nat := fullRecordGapCenterValue + 359066

theorem fullRecordGapTerm06543_eq_value :
    recordGapCenter + 359066 = fullRecordGapValue06543 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06543_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06543 (fullRecordGapValue06543 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06543_not_prime : ¬(recordGapCenter + 359066).Prime := by
  rw [fullRecordGapTerm06543_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06543, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06543_fast_pow_mod_ne_one

def fullRecordGapValue06544 : Nat := fullRecordGapCenterValue + 359096

theorem fullRecordGapTerm06544_eq_value :
    recordGapCenter + 359096 = fullRecordGapValue06544 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06544_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06544 (fullRecordGapValue06544 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06544_not_prime : ¬(recordGapCenter + 359096).Prime := by
  rw [fullRecordGapTerm06544_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06544, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06544_fast_pow_mod_ne_one

def fullRecordGapValue06545 : Nat := fullRecordGapCenterValue + 359186

theorem fullRecordGapTerm06545_eq_value :
    recordGapCenter + 359186 = fullRecordGapValue06545 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06545_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06545 (fullRecordGapValue06545 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06545_not_prime : ¬(recordGapCenter + 359186).Prime := by
  rw [fullRecordGapTerm06545_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06545, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06545_fast_pow_mod_ne_one

def fullRecordGapValue06546 : Nat := fullRecordGapCenterValue + 359276

theorem fullRecordGapTerm06546_eq_value :
    recordGapCenter + 359276 = fullRecordGapValue06546 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06546_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06546 (fullRecordGapValue06546 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06546_not_prime : ¬(recordGapCenter + 359276).Prime := by
  rw [fullRecordGapTerm06546_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06546, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06546_fast_pow_mod_ne_one

def fullRecordGapValue06547 : Nat := fullRecordGapCenterValue + 359318

theorem fullRecordGapTerm06547_eq_value :
    recordGapCenter + 359318 = fullRecordGapValue06547 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06547_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06547 (fullRecordGapValue06547 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06547_not_prime : ¬(recordGapCenter + 359318).Prime := by
  rw [fullRecordGapTerm06547_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06547, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06547_fast_pow_mod_ne_one

def fullRecordGapValue06548 : Nat := fullRecordGapCenterValue + 359342

theorem fullRecordGapTerm06548_eq_value :
    recordGapCenter + 359342 = fullRecordGapValue06548 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06548_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06548 (fullRecordGapValue06548 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06548_not_prime : ¬(recordGapCenter + 359342).Prime := by
  rw [fullRecordGapTerm06548_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06548, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06548_fast_pow_mod_ne_one

def fullRecordGapValue06549 : Nat := fullRecordGapCenterValue + 359588

theorem fullRecordGapTerm06549_eq_value :
    recordGapCenter + 359588 = fullRecordGapValue06549 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06549_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06549 (fullRecordGapValue06549 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06549_not_prime : ¬(recordGapCenter + 359588).Prime := by
  rw [fullRecordGapTerm06549_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06549, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06549_fast_pow_mod_ne_one

def fullRecordGapValue06550 : Nat := fullRecordGapCenterValue + 359672

theorem fullRecordGapTerm06550_eq_value :
    recordGapCenter + 359672 = fullRecordGapValue06550 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06550_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06550 (fullRecordGapValue06550 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06550_not_prime : ¬(recordGapCenter + 359672).Prime := by
  rw [fullRecordGapTerm06550_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06550, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06550_fast_pow_mod_ne_one

def fullRecordGapValue06551 : Nat := fullRecordGapCenterValue + 359846

theorem fullRecordGapTerm06551_eq_value :
    recordGapCenter + 359846 = fullRecordGapValue06551 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06551_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06551 (fullRecordGapValue06551 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06551_not_prime : ¬(recordGapCenter + 359846).Prime := by
  rw [fullRecordGapTerm06551_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06551, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06551_fast_pow_mod_ne_one

def fullRecordGapValue06552 : Nat := fullRecordGapCenterValue + 359886

theorem fullRecordGapTerm06552_eq_value :
    recordGapCenter + 359886 = fullRecordGapValue06552 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06552_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06552 (fullRecordGapValue06552 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06552_not_prime : ¬(recordGapCenter + 359886).Prime := by
  rw [fullRecordGapTerm06552_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06552, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06552_fast_pow_mod_ne_one

def fullRecordGapValue06553 : Nat := fullRecordGapCenterValue + 359978

theorem fullRecordGapTerm06553_eq_value :
    recordGapCenter + 359978 = fullRecordGapValue06553 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06553_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06553 (fullRecordGapValue06553 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06553_not_prime : ¬(recordGapCenter + 359978).Prime := by
  rw [fullRecordGapTerm06553_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06553, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06553_fast_pow_mod_ne_one

def fullRecordGapValue06554 : Nat := fullRecordGapCenterValue + 360056

theorem fullRecordGapTerm06554_eq_value :
    recordGapCenter + 360056 = fullRecordGapValue06554 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06554_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06554 (fullRecordGapValue06554 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06554_not_prime : ¬(recordGapCenter + 360056).Prime := by
  rw [fullRecordGapTerm06554_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06554, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06554_fast_pow_mod_ne_one

def fullRecordGapValue06555 : Nat := fullRecordGapCenterValue + 360078

theorem fullRecordGapTerm06555_eq_value :
    recordGapCenter + 360078 = fullRecordGapValue06555 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06555_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06555 (fullRecordGapValue06555 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06555_not_prime : ¬(recordGapCenter + 360078).Prime := by
  rw [fullRecordGapTerm06555_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06555, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06555_fast_pow_mod_ne_one

def fullRecordGapValue06556 : Nat := fullRecordGapCenterValue + 360236

theorem fullRecordGapTerm06556_eq_value :
    recordGapCenter + 360236 = fullRecordGapValue06556 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06556_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06556 (fullRecordGapValue06556 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06556_not_prime : ¬(recordGapCenter + 360236).Prime := by
  rw [fullRecordGapTerm06556_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06556, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06556_fast_pow_mod_ne_one

def fullRecordGapValue06557 : Nat := fullRecordGapCenterValue + 360362

theorem fullRecordGapTerm06557_eq_value :
    recordGapCenter + 360362 = fullRecordGapValue06557 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06557_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06557 (fullRecordGapValue06557 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06557_not_prime : ¬(recordGapCenter + 360362).Prime := by
  rw [fullRecordGapTerm06557_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06557, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06557_fast_pow_mod_ne_one

def fullRecordGapValue06558 : Nat := fullRecordGapCenterValue + 360428

theorem fullRecordGapTerm06558_eq_value :
    recordGapCenter + 360428 = fullRecordGapValue06558 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06558_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06558 (fullRecordGapValue06558 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06558_not_prime : ¬(recordGapCenter + 360428).Prime := by
  rw [fullRecordGapTerm06558_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06558, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06558_fast_pow_mod_ne_one

def fullRecordGapValue06559 : Nat := fullRecordGapCenterValue + 360546

theorem fullRecordGapTerm06559_eq_value :
    recordGapCenter + 360546 = fullRecordGapValue06559 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06559_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06559 (fullRecordGapValue06559 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06559_not_prime : ¬(recordGapCenter + 360546).Prime := by
  rw [fullRecordGapTerm06559_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06559, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06559_fast_pow_mod_ne_one

def fullRecordGapValue06560 : Nat := fullRecordGapCenterValue + 360596

theorem fullRecordGapTerm06560_eq_value :
    recordGapCenter + 360596 = fullRecordGapValue06560 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06560_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06560 (fullRecordGapValue06560 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06560_not_prime : ¬(recordGapCenter + 360596).Prime := by
  rw [fullRecordGapTerm06560_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06560, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06560_fast_pow_mod_ne_one

def fullRecordGapValue06561 : Nat := fullRecordGapCenterValue + 360722

theorem fullRecordGapTerm06561_eq_value :
    recordGapCenter + 360722 = fullRecordGapValue06561 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06561_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06561 (fullRecordGapValue06561 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06561_not_prime : ¬(recordGapCenter + 360722).Prime := by
  rw [fullRecordGapTerm06561_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06561, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06561_fast_pow_mod_ne_one

def fullRecordGapValue06562 : Nat := fullRecordGapCenterValue + 360762

theorem fullRecordGapTerm06562_eq_value :
    recordGapCenter + 360762 = fullRecordGapValue06562 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06562_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06562 (fullRecordGapValue06562 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06562_not_prime : ¬(recordGapCenter + 360762).Prime := by
  rw [fullRecordGapTerm06562_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06562, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06562_fast_pow_mod_ne_one

def fullRecordGapValue06563 : Nat := fullRecordGapCenterValue + 360782

theorem fullRecordGapTerm06563_eq_value :
    recordGapCenter + 360782 = fullRecordGapValue06563 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06563_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06563 (fullRecordGapValue06563 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06563_not_prime : ¬(recordGapCenter + 360782).Prime := by
  rw [fullRecordGapTerm06563_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06563, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06563_fast_pow_mod_ne_one

def fullRecordGapValue06564 : Nat := fullRecordGapCenterValue + 360788

theorem fullRecordGapTerm06564_eq_value :
    recordGapCenter + 360788 = fullRecordGapValue06564 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06564_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06564 (fullRecordGapValue06564 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06564_not_prime : ¬(recordGapCenter + 360788).Prime := by
  rw [fullRecordGapTerm06564_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06564, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06564_fast_pow_mod_ne_one

def fullRecordGapValue06565 : Nat := fullRecordGapCenterValue + 360812

theorem fullRecordGapTerm06565_eq_value :
    recordGapCenter + 360812 = fullRecordGapValue06565 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06565_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06565 (fullRecordGapValue06565 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06565_not_prime : ¬(recordGapCenter + 360812).Prime := by
  rw [fullRecordGapTerm06565_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06565, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06565_fast_pow_mod_ne_one

def fullRecordGapValue06566 : Nat := fullRecordGapCenterValue + 360908

theorem fullRecordGapTerm06566_eq_value :
    recordGapCenter + 360908 = fullRecordGapValue06566 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06566_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06566 (fullRecordGapValue06566 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06566_not_prime : ¬(recordGapCenter + 360908).Prime := by
  rw [fullRecordGapTerm06566_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06566, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06566_fast_pow_mod_ne_one

def fullRecordGapValue06567 : Nat := fullRecordGapCenterValue + 361002

theorem fullRecordGapTerm06567_eq_value :
    recordGapCenter + 361002 = fullRecordGapValue06567 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06567_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06567 (fullRecordGapValue06567 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06567_not_prime : ¬(recordGapCenter + 361002).Prime := by
  rw [fullRecordGapTerm06567_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06567, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06567_fast_pow_mod_ne_one

def fullRecordGapValue06568 : Nat := fullRecordGapCenterValue + 361502

theorem fullRecordGapTerm06568_eq_value :
    recordGapCenter + 361502 = fullRecordGapValue06568 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06568_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06568 (fullRecordGapValue06568 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06568_not_prime : ¬(recordGapCenter + 361502).Prime := by
  rw [fullRecordGapTerm06568_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06568, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06568_fast_pow_mod_ne_one

def fullRecordGapValue06569 : Nat := fullRecordGapCenterValue + 361506

theorem fullRecordGapTerm06569_eq_value :
    recordGapCenter + 361506 = fullRecordGapValue06569 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06569_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06569 (fullRecordGapValue06569 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06569_not_prime : ¬(recordGapCenter + 361506).Prime := by
  rw [fullRecordGapTerm06569_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06569, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06569_fast_pow_mod_ne_one

def fullRecordGapValue06570 : Nat := fullRecordGapCenterValue + 361586

theorem fullRecordGapTerm06570_eq_value :
    recordGapCenter + 361586 = fullRecordGapValue06570 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06570_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06570 (fullRecordGapValue06570 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06570_not_prime : ¬(recordGapCenter + 361586).Prime := by
  rw [fullRecordGapTerm06570_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06570, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06570_fast_pow_mod_ne_one

def fullRecordGapValue06571 : Nat := fullRecordGapCenterValue + 361628

theorem fullRecordGapTerm06571_eq_value :
    recordGapCenter + 361628 = fullRecordGapValue06571 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06571_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06571 (fullRecordGapValue06571 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06571_not_prime : ¬(recordGapCenter + 361628).Prime := by
  rw [fullRecordGapTerm06571_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06571, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06571_fast_pow_mod_ne_one

def fullRecordGapValue06572 : Nat := fullRecordGapCenterValue + 361898

theorem fullRecordGapTerm06572_eq_value :
    recordGapCenter + 361898 = fullRecordGapValue06572 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06572_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06572 (fullRecordGapValue06572 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06572_not_prime : ¬(recordGapCenter + 361898).Prime := by
  rw [fullRecordGapTerm06572_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06572, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06572_fast_pow_mod_ne_one

def fullRecordGapValue06573 : Nat := fullRecordGapCenterValue + 361902

theorem fullRecordGapTerm06573_eq_value :
    recordGapCenter + 361902 = fullRecordGapValue06573 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06573_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06573 (fullRecordGapValue06573 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06573_not_prime : ¬(recordGapCenter + 361902).Prime := by
  rw [fullRecordGapTerm06573_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06573, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06573_fast_pow_mod_ne_one

def fullRecordGapValue06574 : Nat := fullRecordGapCenterValue + 361986

theorem fullRecordGapTerm06574_eq_value :
    recordGapCenter + 361986 = fullRecordGapValue06574 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06574_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06574 (fullRecordGapValue06574 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06574_not_prime : ¬(recordGapCenter + 361986).Prime := by
  rw [fullRecordGapTerm06574_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06574, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06574_fast_pow_mod_ne_one

def fullRecordGapValue06575 : Nat := fullRecordGapCenterValue + 362078

theorem fullRecordGapTerm06575_eq_value :
    recordGapCenter + 362078 = fullRecordGapValue06575 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06575_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06575 (fullRecordGapValue06575 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06575_not_prime : ¬(recordGapCenter + 362078).Prime := by
  rw [fullRecordGapTerm06575_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06575, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06575_fast_pow_mod_ne_one

def fullRecordGapValue06576 : Nat := fullRecordGapCenterValue + 362238

theorem fullRecordGapTerm06576_eq_value :
    recordGapCenter + 362238 = fullRecordGapValue06576 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06576_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06576 (fullRecordGapValue06576 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06576_not_prime : ¬(recordGapCenter + 362238).Prime := by
  rw [fullRecordGapTerm06576_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06576, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06576_fast_pow_mod_ne_one

def fullRecordGapValue06577 : Nat := fullRecordGapCenterValue + 362282

theorem fullRecordGapTerm06577_eq_value :
    recordGapCenter + 362282 = fullRecordGapValue06577 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06577_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06577 (fullRecordGapValue06577 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06577_not_prime : ¬(recordGapCenter + 362282).Prime := by
  rw [fullRecordGapTerm06577_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06577, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06577_fast_pow_mod_ne_one

def fullRecordGapValue06578 : Nat := fullRecordGapCenterValue + 362486

theorem fullRecordGapTerm06578_eq_value :
    recordGapCenter + 362486 = fullRecordGapValue06578 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06578_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06578 (fullRecordGapValue06578 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06578_not_prime : ¬(recordGapCenter + 362486).Prime := by
  rw [fullRecordGapTerm06578_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06578, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06578_fast_pow_mod_ne_one

def fullRecordGapValue06579 : Nat := fullRecordGapCenterValue + 362546

theorem fullRecordGapTerm06579_eq_value :
    recordGapCenter + 362546 = fullRecordGapValue06579 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06579_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06579 (fullRecordGapValue06579 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06579_not_prime : ¬(recordGapCenter + 362546).Prime := by
  rw [fullRecordGapTerm06579_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06579, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06579_fast_pow_mod_ne_one

def fullRecordGapValue06580 : Nat := fullRecordGapCenterValue + 362552

theorem fullRecordGapTerm06580_eq_value :
    recordGapCenter + 362552 = fullRecordGapValue06580 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06580_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06580 (fullRecordGapValue06580 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06580_not_prime : ¬(recordGapCenter + 362552).Prime := by
  rw [fullRecordGapTerm06580_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06580, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06580_fast_pow_mod_ne_one

def fullRecordGapValue06581 : Nat := fullRecordGapCenterValue + 362588

theorem fullRecordGapTerm06581_eq_value :
    recordGapCenter + 362588 = fullRecordGapValue06581 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06581_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06581 (fullRecordGapValue06581 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06581_not_prime : ¬(recordGapCenter + 362588).Prime := by
  rw [fullRecordGapTerm06581_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06581, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06581_fast_pow_mod_ne_one

def fullRecordGapValue06582 : Nat := fullRecordGapCenterValue + 362636

theorem fullRecordGapTerm06582_eq_value :
    recordGapCenter + 362636 = fullRecordGapValue06582 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06582_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06582 (fullRecordGapValue06582 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06582_not_prime : ¬(recordGapCenter + 362636).Prime := by
  rw [fullRecordGapTerm06582_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06582, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06582_fast_pow_mod_ne_one

def fullRecordGapValue06583 : Nat := fullRecordGapCenterValue + 362658

theorem fullRecordGapTerm06583_eq_value :
    recordGapCenter + 362658 = fullRecordGapValue06583 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06583_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06583 (fullRecordGapValue06583 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06583_not_prime : ¬(recordGapCenter + 362658).Prime := by
  rw [fullRecordGapTerm06583_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06583, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06583_fast_pow_mod_ne_one

def fullRecordGapValue06584 : Nat := fullRecordGapCenterValue + 362708

theorem fullRecordGapTerm06584_eq_value :
    recordGapCenter + 362708 = fullRecordGapValue06584 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06584_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06584 (fullRecordGapValue06584 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06584_not_prime : ¬(recordGapCenter + 362708).Prime := by
  rw [fullRecordGapTerm06584_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06584, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06584_fast_pow_mod_ne_one

def fullRecordGapValue06585 : Nat := fullRecordGapCenterValue + 362958

theorem fullRecordGapTerm06585_eq_value :
    recordGapCenter + 362958 = fullRecordGapValue06585 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06585_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06585 (fullRecordGapValue06585 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06585_not_prime : ¬(recordGapCenter + 362958).Prime := by
  rw [fullRecordGapTerm06585_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06585, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06585_fast_pow_mod_ne_one

def fullRecordGapValue06586 : Nat := fullRecordGapCenterValue + 363000

theorem fullRecordGapTerm06586_eq_value :
    recordGapCenter + 363000 = fullRecordGapValue06586 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06586_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06586 (fullRecordGapValue06586 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06586_not_prime : ¬(recordGapCenter + 363000).Prime := by
  rw [fullRecordGapTerm06586_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06586, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06586_fast_pow_mod_ne_one

def fullRecordGapValue06587 : Nat := fullRecordGapCenterValue + 363002

theorem fullRecordGapTerm06587_eq_value :
    recordGapCenter + 363002 = fullRecordGapValue06587 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06587_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06587 (fullRecordGapValue06587 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06587_not_prime : ¬(recordGapCenter + 363002).Prime := by
  rw [fullRecordGapTerm06587_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06587, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06587_fast_pow_mod_ne_one

def fullRecordGapValue06588 : Nat := fullRecordGapCenterValue + 363098

theorem fullRecordGapTerm06588_eq_value :
    recordGapCenter + 363098 = fullRecordGapValue06588 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06588_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06588 (fullRecordGapValue06588 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06588_not_prime : ¬(recordGapCenter + 363098).Prime := by
  rw [fullRecordGapTerm06588_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06588, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06588_fast_pow_mod_ne_one

def fullRecordGapValue06589 : Nat := fullRecordGapCenterValue + 363126

theorem fullRecordGapTerm06589_eq_value :
    recordGapCenter + 363126 = fullRecordGapValue06589 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06589_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06589 (fullRecordGapValue06589 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06589_not_prime : ¬(recordGapCenter + 363126).Prime := by
  rw [fullRecordGapTerm06589_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06589, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06589_fast_pow_mod_ne_one

def fullRecordGapValue06590 : Nat := fullRecordGapCenterValue + 363338

theorem fullRecordGapTerm06590_eq_value :
    recordGapCenter + 363338 = fullRecordGapValue06590 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06590_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06590 (fullRecordGapValue06590 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06590_not_prime : ¬(recordGapCenter + 363338).Prime := by
  rw [fullRecordGapTerm06590_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06590, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06590_fast_pow_mod_ne_one

def fullRecordGapValue06591 : Nat := fullRecordGapCenterValue + 363452

theorem fullRecordGapTerm06591_eq_value :
    recordGapCenter + 363452 = fullRecordGapValue06591 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06591_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06591 (fullRecordGapValue06591 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06591_not_prime : ¬(recordGapCenter + 363452).Prime := by
  rw [fullRecordGapTerm06591_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06591, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06591_fast_pow_mod_ne_one

def fullRecordGapValue06592 : Nat := fullRecordGapCenterValue + 363512

theorem fullRecordGapTerm06592_eq_value :
    recordGapCenter + 363512 = fullRecordGapValue06592 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06592_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06592 (fullRecordGapValue06592 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06592_not_prime : ¬(recordGapCenter + 363512).Prime := by
  rw [fullRecordGapTerm06592_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06592, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06592_fast_pow_mod_ne_one

def fullRecordGapValue06593 : Nat := fullRecordGapCenterValue + 363578

theorem fullRecordGapTerm06593_eq_value :
    recordGapCenter + 363578 = fullRecordGapValue06593 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06593_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06593 (fullRecordGapValue06593 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06593_not_prime : ¬(recordGapCenter + 363578).Prime := by
  rw [fullRecordGapTerm06593_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06593, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06593_fast_pow_mod_ne_one

def fullRecordGapValue06594 : Nat := fullRecordGapCenterValue + 363606

theorem fullRecordGapTerm06594_eq_value :
    recordGapCenter + 363606 = fullRecordGapValue06594 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06594_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06594 (fullRecordGapValue06594 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06594_not_prime : ¬(recordGapCenter + 363606).Prime := by
  rw [fullRecordGapTerm06594_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06594, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06594_fast_pow_mod_ne_one

def fullRecordGapValue06595 : Nat := fullRecordGapCenterValue + 363702

theorem fullRecordGapTerm06595_eq_value :
    recordGapCenter + 363702 = fullRecordGapValue06595 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06595_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06595 (fullRecordGapValue06595 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06595_not_prime : ¬(recordGapCenter + 363702).Prime := by
  rw [fullRecordGapTerm06595_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06595, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06595_fast_pow_mod_ne_one

def fullRecordGapValue06596 : Nat := fullRecordGapCenterValue + 363738

theorem fullRecordGapTerm06596_eq_value :
    recordGapCenter + 363738 = fullRecordGapValue06596 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06596_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06596 (fullRecordGapValue06596 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06596_not_prime : ¬(recordGapCenter + 363738).Prime := by
  rw [fullRecordGapTerm06596_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06596, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06596_fast_pow_mod_ne_one

def fullRecordGapValue06597 : Nat := fullRecordGapCenterValue + 363746

theorem fullRecordGapTerm06597_eq_value :
    recordGapCenter + 363746 = fullRecordGapValue06597 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06597_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06597 (fullRecordGapValue06597 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06597_not_prime : ¬(recordGapCenter + 363746).Prime := by
  rw [fullRecordGapTerm06597_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06597, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06597_fast_pow_mod_ne_one

def fullRecordGapValue06598 : Nat := fullRecordGapCenterValue + 363806

theorem fullRecordGapTerm06598_eq_value :
    recordGapCenter + 363806 = fullRecordGapValue06598 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06598_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06598 (fullRecordGapValue06598 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06598_not_prime : ¬(recordGapCenter + 363806).Prime := by
  rw [fullRecordGapTerm06598_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06598, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06598_fast_pow_mod_ne_one

def fullRecordGapValue06599 : Nat := fullRecordGapCenterValue + 363882

theorem fullRecordGapTerm06599_eq_value :
    recordGapCenter + 363882 = fullRecordGapValue06599 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06599_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06599 (fullRecordGapValue06599 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06599_not_prime : ¬(recordGapCenter + 363882).Prime := by
  rw [fullRecordGapTerm06599_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06599, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06599_fast_pow_mod_ne_one

def fullRecordGapValue06600 : Nat := fullRecordGapCenterValue + 363956

theorem fullRecordGapTerm06600_eq_value :
    recordGapCenter + 363956 = fullRecordGapValue06600 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06600_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06600 (fullRecordGapValue06600 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06600_not_prime : ¬(recordGapCenter + 363956).Prime := by
  rw [fullRecordGapTerm06600_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06600, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06600_fast_pow_mod_ne_one

def fullRecordGapValue06601 : Nat := fullRecordGapCenterValue + 364022

theorem fullRecordGapTerm06601_eq_value :
    recordGapCenter + 364022 = fullRecordGapValue06601 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06601_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06601 (fullRecordGapValue06601 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06601_not_prime : ¬(recordGapCenter + 364022).Prime := by
  rw [fullRecordGapTerm06601_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06601, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06601_fast_pow_mod_ne_one

def fullRecordGapValue06602 : Nat := fullRecordGapCenterValue + 364082

theorem fullRecordGapTerm06602_eq_value :
    recordGapCenter + 364082 = fullRecordGapValue06602 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06602_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06602 (fullRecordGapValue06602 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06602_not_prime : ¬(recordGapCenter + 364082).Prime := by
  rw [fullRecordGapTerm06602_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06602, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06602_fast_pow_mod_ne_one

def fullRecordGapValue06603 : Nat := fullRecordGapCenterValue + 364218

theorem fullRecordGapTerm06603_eq_value :
    recordGapCenter + 364218 = fullRecordGapValue06603 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06603_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06603 (fullRecordGapValue06603 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06603_not_prime : ¬(recordGapCenter + 364218).Prime := by
  rw [fullRecordGapTerm06603_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06603, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06603_fast_pow_mod_ne_one

def fullRecordGapValue06604 : Nat := fullRecordGapCenterValue + 364262

theorem fullRecordGapTerm06604_eq_value :
    recordGapCenter + 364262 = fullRecordGapValue06604 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06604_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06604 (fullRecordGapValue06604 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06604_not_prime : ¬(recordGapCenter + 364262).Prime := by
  rw [fullRecordGapTerm06604_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06604, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06604_fast_pow_mod_ne_one

def fullRecordGapValue06605 : Nat := fullRecordGapCenterValue + 364358

theorem fullRecordGapTerm06605_eq_value :
    recordGapCenter + 364358 = fullRecordGapValue06605 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06605_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06605 (fullRecordGapValue06605 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06605_not_prime : ¬(recordGapCenter + 364358).Prime := by
  rw [fullRecordGapTerm06605_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06605, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06605_fast_pow_mod_ne_one

def fullRecordGapValue06606 : Nat := fullRecordGapCenterValue + 364478

theorem fullRecordGapTerm06606_eq_value :
    recordGapCenter + 364478 = fullRecordGapValue06606 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06606_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06606 (fullRecordGapValue06606 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06606_not_prime : ¬(recordGapCenter + 364478).Prime := by
  rw [fullRecordGapTerm06606_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06606, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06606_fast_pow_mod_ne_one

def fullRecordGapValue06607 : Nat := fullRecordGapCenterValue + 364500

theorem fullRecordGapTerm06607_eq_value :
    recordGapCenter + 364500 = fullRecordGapValue06607 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06607_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06607 (fullRecordGapValue06607 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06607_not_prime : ¬(recordGapCenter + 364500).Prime := by
  rw [fullRecordGapTerm06607_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06607, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06607_fast_pow_mod_ne_one

def fullRecordGapValue06608 : Nat := fullRecordGapCenterValue + 364556

theorem fullRecordGapTerm06608_eq_value :
    recordGapCenter + 364556 = fullRecordGapValue06608 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06608_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06608 (fullRecordGapValue06608 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06608_not_prime : ¬(recordGapCenter + 364556).Prime := by
  rw [fullRecordGapTerm06608_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06608, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06608_fast_pow_mod_ne_one

def fullRecordGapValue06609 : Nat := fullRecordGapCenterValue + 364578

theorem fullRecordGapTerm06609_eq_value :
    recordGapCenter + 364578 = fullRecordGapValue06609 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06609_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06609 (fullRecordGapValue06609 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06609_not_prime : ¬(recordGapCenter + 364578).Prime := by
  rw [fullRecordGapTerm06609_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06609, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06609_fast_pow_mod_ne_one

def fullRecordGapValue06610 : Nat := fullRecordGapCenterValue + 364652

theorem fullRecordGapTerm06610_eq_value :
    recordGapCenter + 364652 = fullRecordGapValue06610 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06610_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06610 (fullRecordGapValue06610 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06610_not_prime : ¬(recordGapCenter + 364652).Prime := by
  rw [fullRecordGapTerm06610_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06610, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06610_fast_pow_mod_ne_one

def fullRecordGapValue06611 : Nat := fullRecordGapCenterValue + 364758

theorem fullRecordGapTerm06611_eq_value :
    recordGapCenter + 364758 = fullRecordGapValue06611 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06611_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06611 (fullRecordGapValue06611 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06611_not_prime : ¬(recordGapCenter + 364758).Prime := by
  rw [fullRecordGapTerm06611_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06611, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06611_fast_pow_mod_ne_one

def fullRecordGapValue06612 : Nat := fullRecordGapCenterValue + 364772

theorem fullRecordGapTerm06612_eq_value :
    recordGapCenter + 364772 = fullRecordGapValue06612 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06612_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06612 (fullRecordGapValue06612 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06612_not_prime : ¬(recordGapCenter + 364772).Prime := by
  rw [fullRecordGapTerm06612_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06612, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06612_fast_pow_mod_ne_one

def fullRecordGapValue06613 : Nat := fullRecordGapCenterValue + 364946

theorem fullRecordGapTerm06613_eq_value :
    recordGapCenter + 364946 = fullRecordGapValue06613 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06613_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06613 (fullRecordGapValue06613 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06613_not_prime : ¬(recordGapCenter + 364946).Prime := by
  rw [fullRecordGapTerm06613_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06613, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06613_fast_pow_mod_ne_one

def fullRecordGapValue06614 : Nat := fullRecordGapCenterValue + 365018

theorem fullRecordGapTerm06614_eq_value :
    recordGapCenter + 365018 = fullRecordGapValue06614 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06614_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06614 (fullRecordGapValue06614 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06614_not_prime : ¬(recordGapCenter + 365018).Prime := by
  rw [fullRecordGapTerm06614_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06614, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06614_fast_pow_mod_ne_one

def fullRecordGapValue06615 : Nat := fullRecordGapCenterValue + 365198

theorem fullRecordGapTerm06615_eq_value :
    recordGapCenter + 365198 = fullRecordGapValue06615 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06615_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06615 (fullRecordGapValue06615 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06615_not_prime : ¬(recordGapCenter + 365198).Prime := by
  rw [fullRecordGapTerm06615_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06615, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06615_fast_pow_mod_ne_one

def fullRecordGapValue06616 : Nat := fullRecordGapCenterValue + 365282

theorem fullRecordGapTerm06616_eq_value :
    recordGapCenter + 365282 = fullRecordGapValue06616 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06616_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06616 (fullRecordGapValue06616 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06616_not_prime : ¬(recordGapCenter + 365282).Prime := by
  rw [fullRecordGapTerm06616_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06616, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06616_fast_pow_mod_ne_one

def fullRecordGapValue06617 : Nat := fullRecordGapCenterValue + 365426

theorem fullRecordGapTerm06617_eq_value :
    recordGapCenter + 365426 = fullRecordGapValue06617 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06617_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06617 (fullRecordGapValue06617 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06617_not_prime : ¬(recordGapCenter + 365426).Prime := by
  rw [fullRecordGapTerm06617_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06617, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06617_fast_pow_mod_ne_one

def fullRecordGapValue06618 : Nat := fullRecordGapCenterValue + 365478

theorem fullRecordGapTerm06618_eq_value :
    recordGapCenter + 365478 = fullRecordGapValue06618 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06618_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06618 (fullRecordGapValue06618 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06618_not_prime : ¬(recordGapCenter + 365478).Prime := by
  rw [fullRecordGapTerm06618_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06618, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06618_fast_pow_mod_ne_one

def fullRecordGapValue06619 : Nat := fullRecordGapCenterValue + 365492

theorem fullRecordGapTerm06619_eq_value :
    recordGapCenter + 365492 = fullRecordGapValue06619 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06619_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06619 (fullRecordGapValue06619 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06619_not_prime : ¬(recordGapCenter + 365492).Prime := by
  rw [fullRecordGapTerm06619_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06619, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06619_fast_pow_mod_ne_one

def fullRecordGapValue06620 : Nat := fullRecordGapCenterValue + 365558

theorem fullRecordGapTerm06620_eq_value :
    recordGapCenter + 365558 = fullRecordGapValue06620 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06620_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06620 (fullRecordGapValue06620 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06620_not_prime : ¬(recordGapCenter + 365558).Prime := by
  rw [fullRecordGapTerm06620_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06620, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06620_fast_pow_mod_ne_one

def fullRecordGapValue06621 : Nat := fullRecordGapCenterValue + 365576

theorem fullRecordGapTerm06621_eq_value :
    recordGapCenter + 365576 = fullRecordGapValue06621 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06621_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06621 (fullRecordGapValue06621 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06621_not_prime : ¬(recordGapCenter + 365576).Prime := by
  rw [fullRecordGapTerm06621_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06621, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06621_fast_pow_mod_ne_one

def fullRecordGapValue06622 : Nat := fullRecordGapCenterValue + 365622

theorem fullRecordGapTerm06622_eq_value :
    recordGapCenter + 365622 = fullRecordGapValue06622 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06622_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06622 (fullRecordGapValue06622 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06622_not_prime : ¬(recordGapCenter + 365622).Prime := by
  rw [fullRecordGapTerm06622_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06622, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06622_fast_pow_mod_ne_one

def fullRecordGapValue06623 : Nat := fullRecordGapCenterValue + 365642

theorem fullRecordGapTerm06623_eq_value :
    recordGapCenter + 365642 = fullRecordGapValue06623 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06623_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06623 (fullRecordGapValue06623 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06623_not_prime : ¬(recordGapCenter + 365642).Prime := by
  rw [fullRecordGapTerm06623_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06623, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06623_fast_pow_mod_ne_one

def fullRecordGapValue06624 : Nat := fullRecordGapCenterValue + 365678

theorem fullRecordGapTerm06624_eq_value :
    recordGapCenter + 365678 = fullRecordGapValue06624 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06624_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06624 (fullRecordGapValue06624 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06624_not_prime : ¬(recordGapCenter + 365678).Prime := by
  rw [fullRecordGapTerm06624_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06624, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06624_fast_pow_mod_ne_one

def fullRecordGapValue06625 : Nat := fullRecordGapCenterValue + 365828

theorem fullRecordGapTerm06625_eq_value :
    recordGapCenter + 365828 = fullRecordGapValue06625 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06625_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06625 (fullRecordGapValue06625 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06625_not_prime : ¬(recordGapCenter + 365828).Prime := by
  rw [fullRecordGapTerm06625_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06625, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06625_fast_pow_mod_ne_one

def fullRecordGapValue06626 : Nat := fullRecordGapCenterValue + 365858

theorem fullRecordGapTerm06626_eq_value :
    recordGapCenter + 365858 = fullRecordGapValue06626 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06626_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06626 (fullRecordGapValue06626 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06626_not_prime : ¬(recordGapCenter + 365858).Prime := by
  rw [fullRecordGapTerm06626_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06626, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06626_fast_pow_mod_ne_one

def fullRecordGapValue06627 : Nat := fullRecordGapCenterValue + 365996

theorem fullRecordGapTerm06627_eq_value :
    recordGapCenter + 365996 = fullRecordGapValue06627 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06627_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06627 (fullRecordGapValue06627 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06627_not_prime : ¬(recordGapCenter + 365996).Prime := by
  rw [fullRecordGapTerm06627_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06627, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06627_fast_pow_mod_ne_one

def fullRecordGapValue06628 : Nat := fullRecordGapCenterValue + 366006

theorem fullRecordGapTerm06628_eq_value :
    recordGapCenter + 366006 = fullRecordGapValue06628 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06628_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06628 (fullRecordGapValue06628 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06628_not_prime : ¬(recordGapCenter + 366006).Prime := by
  rw [fullRecordGapTerm06628_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06628, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06628_fast_pow_mod_ne_one

def fullRecordGapValue06629 : Nat := fullRecordGapCenterValue + 366182

theorem fullRecordGapTerm06629_eq_value :
    recordGapCenter + 366182 = fullRecordGapValue06629 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06629_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06629 (fullRecordGapValue06629 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06629_not_prime : ¬(recordGapCenter + 366182).Prime := by
  rw [fullRecordGapTerm06629_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06629, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06629_fast_pow_mod_ne_one

def fullRecordGapValue06630 : Nat := fullRecordGapCenterValue + 366258

theorem fullRecordGapTerm06630_eq_value :
    recordGapCenter + 366258 = fullRecordGapValue06630 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06630_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06630 (fullRecordGapValue06630 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06630_not_prime : ¬(recordGapCenter + 366258).Prime := by
  rw [fullRecordGapTerm06630_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06630, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06630_fast_pow_mod_ne_one

def fullRecordGapValue06631 : Nat := fullRecordGapCenterValue + 366332

theorem fullRecordGapTerm06631_eq_value :
    recordGapCenter + 366332 = fullRecordGapValue06631 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06631_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06631 (fullRecordGapValue06631 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06631_not_prime : ¬(recordGapCenter + 366332).Prime := by
  rw [fullRecordGapTerm06631_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06631, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06631_fast_pow_mod_ne_one

def fullRecordGapValue06632 : Nat := fullRecordGapCenterValue + 366342

theorem fullRecordGapTerm06632_eq_value :
    recordGapCenter + 366342 = fullRecordGapValue06632 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06632_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06632 (fullRecordGapValue06632 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06632_not_prime : ¬(recordGapCenter + 366342).Prime := by
  rw [fullRecordGapTerm06632_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06632, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06632_fast_pow_mod_ne_one

def fullRecordGapValue06633 : Nat := fullRecordGapCenterValue + 366518

theorem fullRecordGapTerm06633_eq_value :
    recordGapCenter + 366518 = fullRecordGapValue06633 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06633_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06633 (fullRecordGapValue06633 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06633_not_prime : ¬(recordGapCenter + 366518).Prime := by
  rw [fullRecordGapTerm06633_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06633, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06633_fast_pow_mod_ne_one

def fullRecordGapValue06634 : Nat := fullRecordGapCenterValue + 366566

theorem fullRecordGapTerm06634_eq_value :
    recordGapCenter + 366566 = fullRecordGapValue06634 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06634_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06634 (fullRecordGapValue06634 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06634_not_prime : ¬(recordGapCenter + 366566).Prime := by
  rw [fullRecordGapTerm06634_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06634, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06634_fast_pow_mod_ne_one

def fullRecordGapValue06635 : Nat := fullRecordGapCenterValue + 366578

theorem fullRecordGapTerm06635_eq_value :
    recordGapCenter + 366578 = fullRecordGapValue06635 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06635_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06635 (fullRecordGapValue06635 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06635_not_prime : ¬(recordGapCenter + 366578).Prime := by
  rw [fullRecordGapTerm06635_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06635, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06635_fast_pow_mod_ne_one

def fullRecordGapValue06636 : Nat := fullRecordGapCenterValue + 366602

theorem fullRecordGapTerm06636_eq_value :
    recordGapCenter + 366602 = fullRecordGapValue06636 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06636_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06636 (fullRecordGapValue06636 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06636_not_prime : ¬(recordGapCenter + 366602).Prime := by
  rw [fullRecordGapTerm06636_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06636, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06636_fast_pow_mod_ne_one

def fullRecordGapValue06637 : Nat := fullRecordGapCenterValue + 366686

theorem fullRecordGapTerm06637_eq_value :
    recordGapCenter + 366686 = fullRecordGapValue06637 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06637_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06637 (fullRecordGapValue06637 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06637_not_prime : ¬(recordGapCenter + 366686).Prime := by
  rw [fullRecordGapTerm06637_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06637, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06637_fast_pow_mod_ne_one

def fullRecordGapValue06638 : Nat := fullRecordGapCenterValue + 366746

theorem fullRecordGapTerm06638_eq_value :
    recordGapCenter + 366746 = fullRecordGapValue06638 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06638_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06638 (fullRecordGapValue06638 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06638_not_prime : ¬(recordGapCenter + 366746).Prime := by
  rw [fullRecordGapTerm06638_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06638, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06638_fast_pow_mod_ne_one

def fullRecordGapValue06639 : Nat := fullRecordGapCenterValue + 366812

theorem fullRecordGapTerm06639_eq_value :
    recordGapCenter + 366812 = fullRecordGapValue06639 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06639_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06639 (fullRecordGapValue06639 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06639_not_prime : ¬(recordGapCenter + 366812).Prime := by
  rw [fullRecordGapTerm06639_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06639, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06639_fast_pow_mod_ne_one

def fullRecordGapValue06640 : Nat := fullRecordGapCenterValue + 366902

theorem fullRecordGapTerm06640_eq_value :
    recordGapCenter + 366902 = fullRecordGapValue06640 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06640_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06640 (fullRecordGapValue06640 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06640_not_prime : ¬(recordGapCenter + 366902).Prime := by
  rw [fullRecordGapTerm06640_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06640, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06640_fast_pow_mod_ne_one

def fullRecordGapValue06641 : Nat := fullRecordGapCenterValue + 366998

theorem fullRecordGapTerm06641_eq_value :
    recordGapCenter + 366998 = fullRecordGapValue06641 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06641_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06641 (fullRecordGapValue06641 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06641_not_prime : ¬(recordGapCenter + 366998).Prime := by
  rw [fullRecordGapTerm06641_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06641, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06641_fast_pow_mod_ne_one

def fullRecordGapValue06642 : Nat := fullRecordGapCenterValue + 367266

theorem fullRecordGapTerm06642_eq_value :
    recordGapCenter + 367266 = fullRecordGapValue06642 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06642_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06642 (fullRecordGapValue06642 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06642_not_prime : ¬(recordGapCenter + 367266).Prime := by
  rw [fullRecordGapTerm06642_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06642, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06642_fast_pow_mod_ne_one

def fullRecordGapValue06643 : Nat := fullRecordGapCenterValue + 367322

theorem fullRecordGapTerm06643_eq_value :
    recordGapCenter + 367322 = fullRecordGapValue06643 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06643_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06643 (fullRecordGapValue06643 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06643_not_prime : ¬(recordGapCenter + 367322).Prime := by
  rw [fullRecordGapTerm06643_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06643, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06643_fast_pow_mod_ne_one

def fullRecordGapValue06644 : Nat := fullRecordGapCenterValue + 367416

theorem fullRecordGapTerm06644_eq_value :
    recordGapCenter + 367416 = fullRecordGapValue06644 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06644_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06644 (fullRecordGapValue06644 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06644_not_prime : ¬(recordGapCenter + 367416).Prime := by
  rw [fullRecordGapTerm06644_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06644, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06644_fast_pow_mod_ne_one

def fullRecordGapValue06645 : Nat := fullRecordGapCenterValue + 367518

theorem fullRecordGapTerm06645_eq_value :
    recordGapCenter + 367518 = fullRecordGapValue06645 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06645_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06645 (fullRecordGapValue06645 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06645_not_prime : ¬(recordGapCenter + 367518).Prime := by
  rw [fullRecordGapTerm06645_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06645, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06645_fast_pow_mod_ne_one

def fullRecordGapValue06646 : Nat := fullRecordGapCenterValue + 367782

theorem fullRecordGapTerm06646_eq_value :
    recordGapCenter + 367782 = fullRecordGapValue06646 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06646_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06646 (fullRecordGapValue06646 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06646_not_prime : ¬(recordGapCenter + 367782).Prime := by
  rw [fullRecordGapTerm06646_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06646, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06646_fast_pow_mod_ne_one

def fullRecordGapValue06647 : Nat := fullRecordGapCenterValue + 367838

theorem fullRecordGapTerm06647_eq_value :
    recordGapCenter + 367838 = fullRecordGapValue06647 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06647_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06647 (fullRecordGapValue06647 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06647_not_prime : ¬(recordGapCenter + 367838).Prime := by
  rw [fullRecordGapTerm06647_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06647, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06647_fast_pow_mod_ne_one

def fullRecordGapValue06648 : Nat := fullRecordGapCenterValue + 367986

theorem fullRecordGapTerm06648_eq_value :
    recordGapCenter + 367986 = fullRecordGapValue06648 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06648_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06648 (fullRecordGapValue06648 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06648_not_prime : ¬(recordGapCenter + 367986).Prime := by
  rw [fullRecordGapTerm06648_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06648, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06648_fast_pow_mod_ne_one

def fullRecordGapValue06649 : Nat := fullRecordGapCenterValue + 368006

theorem fullRecordGapTerm06649_eq_value :
    recordGapCenter + 368006 = fullRecordGapValue06649 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06649_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06649 (fullRecordGapValue06649 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06649_not_prime : ¬(recordGapCenter + 368006).Prime := by
  rw [fullRecordGapTerm06649_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06649, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06649_fast_pow_mod_ne_one

def fullRecordGapValue06650 : Nat := fullRecordGapCenterValue + 368036

theorem fullRecordGapTerm06650_eq_value :
    recordGapCenter + 368036 = fullRecordGapValue06650 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06650_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06650 (fullRecordGapValue06650 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06650_not_prime : ¬(recordGapCenter + 368036).Prime := by
  rw [fullRecordGapTerm06650_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06650, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06650_fast_pow_mod_ne_one

def fullRecordGapValue06651 : Nat := fullRecordGapCenterValue + 368162

theorem fullRecordGapTerm06651_eq_value :
    recordGapCenter + 368162 = fullRecordGapValue06651 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06651_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06651 (fullRecordGapValue06651 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06651_not_prime : ¬(recordGapCenter + 368162).Prime := by
  rw [fullRecordGapTerm06651_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06651, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06651_fast_pow_mod_ne_one

def fullRecordGapValue06652 : Nat := fullRecordGapCenterValue + 368168

theorem fullRecordGapTerm06652_eq_value :
    recordGapCenter + 368168 = fullRecordGapValue06652 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06652_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06652 (fullRecordGapValue06652 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06652_not_prime : ¬(recordGapCenter + 368168).Prime := by
  rw [fullRecordGapTerm06652_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06652, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06652_fast_pow_mod_ne_one

def fullRecordGapValue06653 : Nat := fullRecordGapCenterValue + 368216

theorem fullRecordGapTerm06653_eq_value :
    recordGapCenter + 368216 = fullRecordGapValue06653 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06653_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06653 (fullRecordGapValue06653 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06653_not_prime : ¬(recordGapCenter + 368216).Prime := by
  rw [fullRecordGapTerm06653_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06653, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06653_fast_pow_mod_ne_one

def fullRecordGapValue06654 : Nat := fullRecordGapCenterValue + 368418

theorem fullRecordGapTerm06654_eq_value :
    recordGapCenter + 368418 = fullRecordGapValue06654 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06654_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06654 (fullRecordGapValue06654 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06654_not_prime : ¬(recordGapCenter + 368418).Prime := by
  rw [fullRecordGapTerm06654_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06654, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06654_fast_pow_mod_ne_one

def fullRecordGapValue06655 : Nat := fullRecordGapCenterValue + 368546

theorem fullRecordGapTerm06655_eq_value :
    recordGapCenter + 368546 = fullRecordGapValue06655 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06655_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06655 (fullRecordGapValue06655 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06655_not_prime : ¬(recordGapCenter + 368546).Prime := by
  rw [fullRecordGapTerm06655_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06655, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06655_fast_pow_mod_ne_one

def fullRecordGapValue06656 : Nat := fullRecordGapCenterValue + 368558

theorem fullRecordGapTerm06656_eq_value :
    recordGapCenter + 368558 = fullRecordGapValue06656 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06656_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06656 (fullRecordGapValue06656 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06656_not_prime : ¬(recordGapCenter + 368558).Prime := by
  rw [fullRecordGapTerm06656_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06656, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06656_fast_pow_mod_ne_one

end PrimeFactorUnimodality
