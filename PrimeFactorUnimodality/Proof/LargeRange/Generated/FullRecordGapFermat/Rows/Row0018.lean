import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue04353 : Nat := fullRecordGapCenterValue + 134822

theorem fullRecordGapTerm04353_eq_value :
    recordGapCenter + 134822 = fullRecordGapValue04353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04353 (fullRecordGapValue04353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04353_not_prime : ¬(recordGapCenter + 134822).Prime := by
  rw [fullRecordGapTerm04353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04353_fast_pow_mod_ne_one

def fullRecordGapValue04354 : Nat := fullRecordGapCenterValue + 134906

theorem fullRecordGapTerm04354_eq_value :
    recordGapCenter + 134906 = fullRecordGapValue04354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04354 (fullRecordGapValue04354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04354_not_prime : ¬(recordGapCenter + 134906).Prime := by
  rw [fullRecordGapTerm04354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04354_fast_pow_mod_ne_one

def fullRecordGapValue04355 : Nat := fullRecordGapCenterValue + 135000

theorem fullRecordGapTerm04355_eq_value :
    recordGapCenter + 135000 = fullRecordGapValue04355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04355 (fullRecordGapValue04355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04355_not_prime : ¬(recordGapCenter + 135000).Prime := by
  rw [fullRecordGapTerm04355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04355_fast_pow_mod_ne_one

def fullRecordGapValue04356 : Nat := fullRecordGapCenterValue + 135158

theorem fullRecordGapTerm04356_eq_value :
    recordGapCenter + 135158 = fullRecordGapValue04356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04356 (fullRecordGapValue04356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04356_not_prime : ¬(recordGapCenter + 135158).Prime := by
  rw [fullRecordGapTerm04356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04356_fast_pow_mod_ne_one

def fullRecordGapValue04357 : Nat := fullRecordGapCenterValue + 135398

theorem fullRecordGapTerm04357_eq_value :
    recordGapCenter + 135398 = fullRecordGapValue04357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04357 (fullRecordGapValue04357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04357_not_prime : ¬(recordGapCenter + 135398).Prime := by
  rw [fullRecordGapTerm04357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04357_fast_pow_mod_ne_one

def fullRecordGapValue04358 : Nat := fullRecordGapCenterValue + 135446

theorem fullRecordGapTerm04358_eq_value :
    recordGapCenter + 135446 = fullRecordGapValue04358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04358 (fullRecordGapValue04358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04358_not_prime : ¬(recordGapCenter + 135446).Prime := by
  rw [fullRecordGapTerm04358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04358_fast_pow_mod_ne_one

def fullRecordGapValue04359 : Nat := fullRecordGapCenterValue + 135602

theorem fullRecordGapTerm04359_eq_value :
    recordGapCenter + 135602 = fullRecordGapValue04359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04359 (fullRecordGapValue04359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04359_not_prime : ¬(recordGapCenter + 135602).Prime := by
  rw [fullRecordGapTerm04359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04359_fast_pow_mod_ne_one

def fullRecordGapValue04360 : Nat := fullRecordGapCenterValue + 135828

theorem fullRecordGapTerm04360_eq_value :
    recordGapCenter + 135828 = fullRecordGapValue04360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04360 (fullRecordGapValue04360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04360_not_prime : ¬(recordGapCenter + 135828).Prime := by
  rw [fullRecordGapTerm04360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04360_fast_pow_mod_ne_one

def fullRecordGapValue04361 : Nat := fullRecordGapCenterValue + 135986

theorem fullRecordGapTerm04361_eq_value :
    recordGapCenter + 135986 = fullRecordGapValue04361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04361 (fullRecordGapValue04361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04361_not_prime : ¬(recordGapCenter + 135986).Prime := by
  rw [fullRecordGapTerm04361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04361_fast_pow_mod_ne_one

def fullRecordGapValue04362 : Nat := fullRecordGapCenterValue + 136080

theorem fullRecordGapTerm04362_eq_value :
    recordGapCenter + 136080 = fullRecordGapValue04362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04362 (fullRecordGapValue04362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04362_not_prime : ¬(recordGapCenter + 136080).Prime := by
  rw [fullRecordGapTerm04362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04362_fast_pow_mod_ne_one

def fullRecordGapValue04363 : Nat := fullRecordGapCenterValue + 136082

theorem fullRecordGapTerm04363_eq_value :
    recordGapCenter + 136082 = fullRecordGapValue04363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04363 (fullRecordGapValue04363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04363_not_prime : ¬(recordGapCenter + 136082).Prime := by
  rw [fullRecordGapTerm04363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04363_fast_pow_mod_ne_one

def fullRecordGapValue04364 : Nat := fullRecordGapCenterValue + 136118

theorem fullRecordGapTerm04364_eq_value :
    recordGapCenter + 136118 = fullRecordGapValue04364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04364 (fullRecordGapValue04364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04364_not_prime : ¬(recordGapCenter + 136118).Prime := by
  rw [fullRecordGapTerm04364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04364_fast_pow_mod_ne_one

def fullRecordGapValue04365 : Nat := fullRecordGapCenterValue + 136622

theorem fullRecordGapTerm04365_eq_value :
    recordGapCenter + 136622 = fullRecordGapValue04365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04365 (fullRecordGapValue04365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04365_not_prime : ¬(recordGapCenter + 136622).Prime := by
  rw [fullRecordGapTerm04365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04365_fast_pow_mod_ne_one

def fullRecordGapValue04366 : Nat := fullRecordGapCenterValue + 136778

theorem fullRecordGapTerm04366_eq_value :
    recordGapCenter + 136778 = fullRecordGapValue04366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04366 (fullRecordGapValue04366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04366_not_prime : ¬(recordGapCenter + 136778).Prime := by
  rw [fullRecordGapTerm04366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04366_fast_pow_mod_ne_one

def fullRecordGapValue04367 : Nat := fullRecordGapCenterValue + 136886

theorem fullRecordGapTerm04367_eq_value :
    recordGapCenter + 136886 = fullRecordGapValue04367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04367 (fullRecordGapValue04367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04367_not_prime : ¬(recordGapCenter + 136886).Prime := by
  rw [fullRecordGapTerm04367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04367_fast_pow_mod_ne_one

def fullRecordGapValue04368 : Nat := fullRecordGapCenterValue + 137366

theorem fullRecordGapTerm04368_eq_value :
    recordGapCenter + 137366 = fullRecordGapValue04368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04368 (fullRecordGapValue04368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04368_not_prime : ¬(recordGapCenter + 137366).Prime := by
  rw [fullRecordGapTerm04368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04368_fast_pow_mod_ne_one

def fullRecordGapValue04369 : Nat := fullRecordGapCenterValue + 137426

theorem fullRecordGapTerm04369_eq_value :
    recordGapCenter + 137426 = fullRecordGapValue04369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04369 (fullRecordGapValue04369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04369_not_prime : ¬(recordGapCenter + 137426).Prime := by
  rw [fullRecordGapTerm04369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04369_fast_pow_mod_ne_one

def fullRecordGapValue04370 : Nat := fullRecordGapCenterValue + 137498

theorem fullRecordGapTerm04370_eq_value :
    recordGapCenter + 137498 = fullRecordGapValue04370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04370 (fullRecordGapValue04370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04370_not_prime : ¬(recordGapCenter + 137498).Prime := by
  rw [fullRecordGapTerm04370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04370_fast_pow_mod_ne_one

def fullRecordGapValue04371 : Nat := fullRecordGapCenterValue + 137582

theorem fullRecordGapTerm04371_eq_value :
    recordGapCenter + 137582 = fullRecordGapValue04371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04371 (fullRecordGapValue04371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04371_not_prime : ¬(recordGapCenter + 137582).Prime := by
  rw [fullRecordGapTerm04371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04371_fast_pow_mod_ne_one

def fullRecordGapValue04372 : Nat := fullRecordGapCenterValue + 137798

theorem fullRecordGapTerm04372_eq_value :
    recordGapCenter + 137798 = fullRecordGapValue04372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04372 (fullRecordGapValue04372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04372_not_prime : ¬(recordGapCenter + 137798).Prime := by
  rw [fullRecordGapTerm04372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04372_fast_pow_mod_ne_one

def fullRecordGapValue04373 : Nat := fullRecordGapCenterValue + 138122

theorem fullRecordGapTerm04373_eq_value :
    recordGapCenter + 138122 = fullRecordGapValue04373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04373 (fullRecordGapValue04373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04373_not_prime : ¬(recordGapCenter + 138122).Prime := by
  rw [fullRecordGapTerm04373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04373_fast_pow_mod_ne_one

def fullRecordGapValue04374 : Nat := fullRecordGapCenterValue + 138146

theorem fullRecordGapTerm04374_eq_value :
    recordGapCenter + 138146 = fullRecordGapValue04374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04374 (fullRecordGapValue04374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04374_not_prime : ¬(recordGapCenter + 138146).Prime := by
  rw [fullRecordGapTerm04374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04374_fast_pow_mod_ne_one

def fullRecordGapValue04375 : Nat := fullRecordGapCenterValue + 138240

theorem fullRecordGapTerm04375_eq_value :
    recordGapCenter + 138240 = fullRecordGapValue04375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04375 (fullRecordGapValue04375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04375_not_prime : ¬(recordGapCenter + 138240).Prime := by
  rw [fullRecordGapTerm04375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04375_fast_pow_mod_ne_one

def fullRecordGapValue04376 : Nat := fullRecordGapCenterValue + 138302

theorem fullRecordGapTerm04376_eq_value :
    recordGapCenter + 138302 = fullRecordGapValue04376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04376 (fullRecordGapValue04376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04376_not_prime : ¬(recordGapCenter + 138302).Prime := by
  rw [fullRecordGapTerm04376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04376_fast_pow_mod_ne_one

def fullRecordGapValue04377 : Nat := fullRecordGapCenterValue + 138386

theorem fullRecordGapTerm04377_eq_value :
    recordGapCenter + 138386 = fullRecordGapValue04377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04377 (fullRecordGapValue04377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04377_not_prime : ¬(recordGapCenter + 138386).Prime := by
  rw [fullRecordGapTerm04377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04377_fast_pow_mod_ne_one

def fullRecordGapValue04378 : Nat := fullRecordGapCenterValue + 138518

theorem fullRecordGapTerm04378_eq_value :
    recordGapCenter + 138518 = fullRecordGapValue04378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04378 (fullRecordGapValue04378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04378_not_prime : ¬(recordGapCenter + 138518).Prime := by
  rw [fullRecordGapTerm04378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04378_fast_pow_mod_ne_one

def fullRecordGapValue04379 : Nat := fullRecordGapCenterValue + 138600

theorem fullRecordGapTerm04379_eq_value :
    recordGapCenter + 138600 = fullRecordGapValue04379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04379 (fullRecordGapValue04379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04379_not_prime : ¬(recordGapCenter + 138600).Prime := by
  rw [fullRecordGapTerm04379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04379_fast_pow_mod_ne_one

def fullRecordGapValue04380 : Nat := fullRecordGapCenterValue + 138806

theorem fullRecordGapTerm04380_eq_value :
    recordGapCenter + 138806 = fullRecordGapValue04380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04380 (fullRecordGapValue04380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04380_not_prime : ¬(recordGapCenter + 138806).Prime := by
  rw [fullRecordGapTerm04380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04380_fast_pow_mod_ne_one

def fullRecordGapValue04381 : Nat := fullRecordGapCenterValue + 138986

theorem fullRecordGapTerm04381_eq_value :
    recordGapCenter + 138986 = fullRecordGapValue04381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04381 (fullRecordGapValue04381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04381_not_prime : ¬(recordGapCenter + 138986).Prime := by
  rw [fullRecordGapTerm04381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04381_fast_pow_mod_ne_one

def fullRecordGapValue04382 : Nat := fullRecordGapCenterValue + 139382

theorem fullRecordGapTerm04382_eq_value :
    recordGapCenter + 139382 = fullRecordGapValue04382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04382 (fullRecordGapValue04382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04382_not_prime : ¬(recordGapCenter + 139382).Prime := by
  rw [fullRecordGapTerm04382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04382_fast_pow_mod_ne_one

def fullRecordGapValue04383 : Nat := fullRecordGapCenterValue + 139478

theorem fullRecordGapTerm04383_eq_value :
    recordGapCenter + 139478 = fullRecordGapValue04383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04383 (fullRecordGapValue04383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04383_not_prime : ¬(recordGapCenter + 139478).Prime := by
  rw [fullRecordGapTerm04383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04383_fast_pow_mod_ne_one

def fullRecordGapValue04384 : Nat := fullRecordGapCenterValue + 139526

theorem fullRecordGapTerm04384_eq_value :
    recordGapCenter + 139526 = fullRecordGapValue04384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04384 (fullRecordGapValue04384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04384_not_prime : ¬(recordGapCenter + 139526).Prime := by
  rw [fullRecordGapTerm04384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04384_fast_pow_mod_ne_one

def fullRecordGapValue04385 : Nat := fullRecordGapCenterValue + 139658

theorem fullRecordGapTerm04385_eq_value :
    recordGapCenter + 139658 = fullRecordGapValue04385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04385 (fullRecordGapValue04385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04385_not_prime : ¬(recordGapCenter + 139658).Prime := by
  rw [fullRecordGapTerm04385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04385_fast_pow_mod_ne_one

def fullRecordGapValue04386 : Nat := fullRecordGapCenterValue + 139862

theorem fullRecordGapTerm04386_eq_value :
    recordGapCenter + 139862 = fullRecordGapValue04386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04386 (fullRecordGapValue04386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04386_not_prime : ¬(recordGapCenter + 139862).Prime := by
  rw [fullRecordGapTerm04386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04386_fast_pow_mod_ne_one

def fullRecordGapValue04387 : Nat := fullRecordGapCenterValue + 140018

theorem fullRecordGapTerm04387_eq_value :
    recordGapCenter + 140018 = fullRecordGapValue04387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04387 (fullRecordGapValue04387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04387_not_prime : ¬(recordGapCenter + 140018).Prime := by
  rw [fullRecordGapTerm04387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04387_fast_pow_mod_ne_one

def fullRecordGapValue04388 : Nat := fullRecordGapCenterValue + 140078

theorem fullRecordGapTerm04388_eq_value :
    recordGapCenter + 140078 = fullRecordGapValue04388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04388 (fullRecordGapValue04388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04388_not_prime : ¬(recordGapCenter + 140078).Prime := by
  rw [fullRecordGapTerm04388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04388_fast_pow_mod_ne_one

def fullRecordGapValue04389 : Nat := fullRecordGapCenterValue + 140102

theorem fullRecordGapTerm04389_eq_value :
    recordGapCenter + 140102 = fullRecordGapValue04389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04389 (fullRecordGapValue04389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04389_not_prime : ¬(recordGapCenter + 140102).Prime := by
  rw [fullRecordGapTerm04389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04389_fast_pow_mod_ne_one

def fullRecordGapValue04390 : Nat := fullRecordGapCenterValue + 140198

theorem fullRecordGapTerm04390_eq_value :
    recordGapCenter + 140198 = fullRecordGapValue04390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04390 (fullRecordGapValue04390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04390_not_prime : ¬(recordGapCenter + 140198).Prime := by
  rw [fullRecordGapTerm04390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04390_fast_pow_mod_ne_one

def fullRecordGapValue04391 : Nat := fullRecordGapCenterValue + 140222

theorem fullRecordGapTerm04391_eq_value :
    recordGapCenter + 140222 = fullRecordGapValue04391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04391 (fullRecordGapValue04391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04391_not_prime : ¬(recordGapCenter + 140222).Prime := by
  rw [fullRecordGapTerm04391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04391_fast_pow_mod_ne_one

def fullRecordGapValue04392 : Nat := fullRecordGapCenterValue + 140282

theorem fullRecordGapTerm04392_eq_value :
    recordGapCenter + 140282 = fullRecordGapValue04392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04392 (fullRecordGapValue04392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04392_not_prime : ¬(recordGapCenter + 140282).Prime := by
  rw [fullRecordGapTerm04392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04392_fast_pow_mod_ne_one

def fullRecordGapValue04393 : Nat := fullRecordGapCenterValue + 140702

theorem fullRecordGapTerm04393_eq_value :
    recordGapCenter + 140702 = fullRecordGapValue04393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04393 (fullRecordGapValue04393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04393_not_prime : ¬(recordGapCenter + 140702).Prime := by
  rw [fullRecordGapTerm04393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04393_fast_pow_mod_ne_one

def fullRecordGapValue04394 : Nat := fullRecordGapCenterValue + 140918

theorem fullRecordGapTerm04394_eq_value :
    recordGapCenter + 140918 = fullRecordGapValue04394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04394 (fullRecordGapValue04394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04394_not_prime : ¬(recordGapCenter + 140918).Prime := by
  rw [fullRecordGapTerm04394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04394_fast_pow_mod_ne_one

def fullRecordGapValue04395 : Nat := fullRecordGapCenterValue + 141278

theorem fullRecordGapTerm04395_eq_value :
    recordGapCenter + 141278 = fullRecordGapValue04395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04395 (fullRecordGapValue04395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04395_not_prime : ¬(recordGapCenter + 141278).Prime := by
  rw [fullRecordGapTerm04395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04395_fast_pow_mod_ne_one

def fullRecordGapValue04396 : Nat := fullRecordGapCenterValue + 141458

theorem fullRecordGapTerm04396_eq_value :
    recordGapCenter + 141458 = fullRecordGapValue04396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04396 (fullRecordGapValue04396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04396_not_prime : ¬(recordGapCenter + 141458).Prime := by
  rw [fullRecordGapTerm04396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04396_fast_pow_mod_ne_one

def fullRecordGapValue04397 : Nat := fullRecordGapCenterValue + 141758

theorem fullRecordGapTerm04397_eq_value :
    recordGapCenter + 141758 = fullRecordGapValue04397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04397 (fullRecordGapValue04397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04397_not_prime : ¬(recordGapCenter + 141758).Prime := by
  rw [fullRecordGapTerm04397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04397_fast_pow_mod_ne_one

def fullRecordGapValue04398 : Nat := fullRecordGapCenterValue + 141842

theorem fullRecordGapTerm04398_eq_value :
    recordGapCenter + 141842 = fullRecordGapValue04398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04398 (fullRecordGapValue04398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04398_not_prime : ¬(recordGapCenter + 141842).Prime := by
  rw [fullRecordGapTerm04398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04398_fast_pow_mod_ne_one

def fullRecordGapValue04399 : Nat := fullRecordGapCenterValue + 141998

theorem fullRecordGapTerm04399_eq_value :
    recordGapCenter + 141998 = fullRecordGapValue04399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04399 (fullRecordGapValue04399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04399_not_prime : ¬(recordGapCenter + 141998).Prime := by
  rw [fullRecordGapTerm04399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04399_fast_pow_mod_ne_one

def fullRecordGapValue04400 : Nat := fullRecordGapCenterValue + 142178

theorem fullRecordGapTerm04400_eq_value :
    recordGapCenter + 142178 = fullRecordGapValue04400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04400 (fullRecordGapValue04400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04400_not_prime : ¬(recordGapCenter + 142178).Prime := by
  rw [fullRecordGapTerm04400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04400_fast_pow_mod_ne_one

def fullRecordGapValue04401 : Nat := fullRecordGapCenterValue + 142296

theorem fullRecordGapTerm04401_eq_value :
    recordGapCenter + 142296 = fullRecordGapValue04401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04401 (fullRecordGapValue04401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04401_not_prime : ¬(recordGapCenter + 142296).Prime := by
  rw [fullRecordGapTerm04401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04401_fast_pow_mod_ne_one

def fullRecordGapValue04402 : Nat := fullRecordGapCenterValue + 142322

theorem fullRecordGapTerm04402_eq_value :
    recordGapCenter + 142322 = fullRecordGapValue04402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04402 (fullRecordGapValue04402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04402_not_prime : ¬(recordGapCenter + 142322).Prime := by
  rw [fullRecordGapTerm04402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04402_fast_pow_mod_ne_one

def fullRecordGapValue04403 : Nat := fullRecordGapCenterValue + 142418

theorem fullRecordGapTerm04403_eq_value :
    recordGapCenter + 142418 = fullRecordGapValue04403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04403 (fullRecordGapValue04403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04403_not_prime : ¬(recordGapCenter + 142418).Prime := by
  rw [fullRecordGapTerm04403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04403_fast_pow_mod_ne_one

def fullRecordGapValue04404 : Nat := fullRecordGapCenterValue + 142560

theorem fullRecordGapTerm04404_eq_value :
    recordGapCenter + 142560 = fullRecordGapValue04404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04404 (fullRecordGapValue04404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04404_not_prime : ¬(recordGapCenter + 142560).Prime := by
  rw [fullRecordGapTerm04404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04404_fast_pow_mod_ne_one

def fullRecordGapValue04405 : Nat := fullRecordGapCenterValue + 142838

theorem fullRecordGapTerm04405_eq_value :
    recordGapCenter + 142838 = fullRecordGapValue04405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04405 (fullRecordGapValue04405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04405_not_prime : ¬(recordGapCenter + 142838).Prime := by
  rw [fullRecordGapTerm04405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04405_fast_pow_mod_ne_one

def fullRecordGapValue04406 : Nat := fullRecordGapCenterValue + 142958

theorem fullRecordGapTerm04406_eq_value :
    recordGapCenter + 142958 = fullRecordGapValue04406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04406 (fullRecordGapValue04406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04406_not_prime : ¬(recordGapCenter + 142958).Prime := by
  rw [fullRecordGapTerm04406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04406_fast_pow_mod_ne_one

def fullRecordGapValue04407 : Nat := fullRecordGapCenterValue + 143342

theorem fullRecordGapTerm04407_eq_value :
    recordGapCenter + 143342 = fullRecordGapValue04407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04407 (fullRecordGapValue04407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04407_not_prime : ¬(recordGapCenter + 143342).Prime := by
  rw [fullRecordGapTerm04407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04407_fast_pow_mod_ne_one

def fullRecordGapValue04408 : Nat := fullRecordGapCenterValue + 143360

theorem fullRecordGapTerm04408_eq_value :
    recordGapCenter + 143360 = fullRecordGapValue04408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04408 (fullRecordGapValue04408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04408_not_prime : ¬(recordGapCenter + 143360).Prime := by
  rw [fullRecordGapTerm04408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04408_fast_pow_mod_ne_one

def fullRecordGapValue04409 : Nat := fullRecordGapCenterValue + 143748

theorem fullRecordGapTerm04409_eq_value :
    recordGapCenter + 143748 = fullRecordGapValue04409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04409 (fullRecordGapValue04409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04409_not_prime : ¬(recordGapCenter + 143748).Prime := by
  rw [fullRecordGapTerm04409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04409_fast_pow_mod_ne_one

def fullRecordGapValue04410 : Nat := fullRecordGapCenterValue + 144000

theorem fullRecordGapTerm04410_eq_value :
    recordGapCenter + 144000 = fullRecordGapValue04410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04410 (fullRecordGapValue04410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04410_not_prime : ¬(recordGapCenter + 144000).Prime := by
  rw [fullRecordGapTerm04410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04410_fast_pow_mod_ne_one

def fullRecordGapValue04411 : Nat := fullRecordGapCenterValue + 144062

theorem fullRecordGapTerm04411_eq_value :
    recordGapCenter + 144062 = fullRecordGapValue04411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04411 (fullRecordGapValue04411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04411_not_prime : ¬(recordGapCenter + 144062).Prime := by
  rw [fullRecordGapTerm04411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04411_fast_pow_mod_ne_one

def fullRecordGapValue04412 : Nat := fullRecordGapCenterValue + 144182

theorem fullRecordGapTerm04412_eq_value :
    recordGapCenter + 144182 = fullRecordGapValue04412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04412 (fullRecordGapValue04412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04412_not_prime : ¬(recordGapCenter + 144182).Prime := by
  rw [fullRecordGapTerm04412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04412_fast_pow_mod_ne_one

def fullRecordGapValue04413 : Nat := fullRecordGapCenterValue + 144218

theorem fullRecordGapTerm04413_eq_value :
    recordGapCenter + 144218 = fullRecordGapValue04413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04413 (fullRecordGapValue04413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04413_not_prime : ¬(recordGapCenter + 144218).Prime := by
  rw [fullRecordGapTerm04413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04413_fast_pow_mod_ne_one

def fullRecordGapValue04414 : Nat := fullRecordGapCenterValue + 144446

theorem fullRecordGapTerm04414_eq_value :
    recordGapCenter + 144446 = fullRecordGapValue04414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04414 (fullRecordGapValue04414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04414_not_prime : ¬(recordGapCenter + 144446).Prime := by
  rw [fullRecordGapTerm04414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04414_fast_pow_mod_ne_one

def fullRecordGapValue04415 : Nat := fullRecordGapCenterValue + 144506

theorem fullRecordGapTerm04415_eq_value :
    recordGapCenter + 144506 = fullRecordGapValue04415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04415 (fullRecordGapValue04415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04415_not_prime : ¬(recordGapCenter + 144506).Prime := by
  rw [fullRecordGapTerm04415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04415_fast_pow_mod_ne_one

def fullRecordGapValue04416 : Nat := fullRecordGapCenterValue + 144842

theorem fullRecordGapTerm04416_eq_value :
    recordGapCenter + 144842 = fullRecordGapValue04416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04416 (fullRecordGapValue04416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04416_not_prime : ¬(recordGapCenter + 144842).Prime := by
  rw [fullRecordGapTerm04416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04416_fast_pow_mod_ne_one

def fullRecordGapValue04417 : Nat := fullRecordGapCenterValue + 144986

theorem fullRecordGapTerm04417_eq_value :
    recordGapCenter + 144986 = fullRecordGapValue04417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04417 (fullRecordGapValue04417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04417_not_prime : ¬(recordGapCenter + 144986).Prime := by
  rw [fullRecordGapTerm04417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04417_fast_pow_mod_ne_one

def fullRecordGapValue04418 : Nat := fullRecordGapCenterValue + 145118

theorem fullRecordGapTerm04418_eq_value :
    recordGapCenter + 145118 = fullRecordGapValue04418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04418 (fullRecordGapValue04418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04418_not_prime : ¬(recordGapCenter + 145118).Prime := by
  rw [fullRecordGapTerm04418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04418_fast_pow_mod_ne_one

def fullRecordGapValue04419 : Nat := fullRecordGapCenterValue + 145346

theorem fullRecordGapTerm04419_eq_value :
    recordGapCenter + 145346 = fullRecordGapValue04419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04419 (fullRecordGapValue04419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04419_not_prime : ¬(recordGapCenter + 145346).Prime := by
  rw [fullRecordGapTerm04419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04419_fast_pow_mod_ne_one

def fullRecordGapValue04420 : Nat := fullRecordGapCenterValue + 145358

theorem fullRecordGapTerm04420_eq_value :
    recordGapCenter + 145358 = fullRecordGapValue04420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04420 (fullRecordGapValue04420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04420_not_prime : ¬(recordGapCenter + 145358).Prime := by
  rw [fullRecordGapTerm04420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04420_fast_pow_mod_ne_one

def fullRecordGapValue04421 : Nat := fullRecordGapCenterValue + 145478

theorem fullRecordGapTerm04421_eq_value :
    recordGapCenter + 145478 = fullRecordGapValue04421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04421 (fullRecordGapValue04421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04421_not_prime : ¬(recordGapCenter + 145478).Prime := by
  rw [fullRecordGapTerm04421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04421_fast_pow_mod_ne_one

def fullRecordGapValue04422 : Nat := fullRecordGapCenterValue + 145530

theorem fullRecordGapTerm04422_eq_value :
    recordGapCenter + 145530 = fullRecordGapValue04422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04422 (fullRecordGapValue04422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04422_not_prime : ¬(recordGapCenter + 145530).Prime := by
  rw [fullRecordGapTerm04422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04422_fast_pow_mod_ne_one

def fullRecordGapValue04423 : Nat := fullRecordGapCenterValue + 145646

theorem fullRecordGapTerm04423_eq_value :
    recordGapCenter + 145646 = fullRecordGapValue04423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04423 (fullRecordGapValue04423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04423_not_prime : ¬(recordGapCenter + 145646).Prime := by
  rw [fullRecordGapTerm04423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04423_fast_pow_mod_ne_one

def fullRecordGapValue04424 : Nat := fullRecordGapCenterValue + 145800

theorem fullRecordGapTerm04424_eq_value :
    recordGapCenter + 145800 = fullRecordGapValue04424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04424 (fullRecordGapValue04424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04424_not_prime : ¬(recordGapCenter + 145800).Prime := by
  rw [fullRecordGapTerm04424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04424_fast_pow_mod_ne_one

def fullRecordGapValue04425 : Nat := fullRecordGapCenterValue + 145946

theorem fullRecordGapTerm04425_eq_value :
    recordGapCenter + 145946 = fullRecordGapValue04425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04425 (fullRecordGapValue04425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04425_not_prime : ¬(recordGapCenter + 145946).Prime := by
  rw [fullRecordGapTerm04425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04425_fast_pow_mod_ne_one

def fullRecordGapValue04426 : Nat := fullRecordGapCenterValue + 146282

theorem fullRecordGapTerm04426_eq_value :
    recordGapCenter + 146282 = fullRecordGapValue04426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04426 (fullRecordGapValue04426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04426_not_prime : ¬(recordGapCenter + 146282).Prime := by
  rw [fullRecordGapTerm04426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04426_fast_pow_mod_ne_one

def fullRecordGapValue04427 : Nat := fullRecordGapCenterValue + 146738

theorem fullRecordGapTerm04427_eq_value :
    recordGapCenter + 146738 = fullRecordGapValue04427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04427 (fullRecordGapValue04427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04427_not_prime : ¬(recordGapCenter + 146738).Prime := by
  rw [fullRecordGapTerm04427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04427_fast_pow_mod_ne_one

def fullRecordGapValue04428 : Nat := fullRecordGapCenterValue + 146906

theorem fullRecordGapTerm04428_eq_value :
    recordGapCenter + 146906 = fullRecordGapValue04428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04428 (fullRecordGapValue04428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04428_not_prime : ¬(recordGapCenter + 146906).Prime := by
  rw [fullRecordGapTerm04428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04428_fast_pow_mod_ne_one

def fullRecordGapValue04429 : Nat := fullRecordGapCenterValue + 146966

theorem fullRecordGapTerm04429_eq_value :
    recordGapCenter + 146966 = fullRecordGapValue04429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04429 (fullRecordGapValue04429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04429_not_prime : ¬(recordGapCenter + 146966).Prime := by
  rw [fullRecordGapTerm04429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04429_fast_pow_mod_ne_one

def fullRecordGapValue04430 : Nat := fullRecordGapCenterValue + 147386

theorem fullRecordGapTerm04430_eq_value :
    recordGapCenter + 147386 = fullRecordGapValue04430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04430 (fullRecordGapValue04430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04430_not_prime : ¬(recordGapCenter + 147386).Prime := by
  rw [fullRecordGapTerm04430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04430_fast_pow_mod_ne_one

def fullRecordGapValue04431 : Nat := fullRecordGapCenterValue + 147456

theorem fullRecordGapTerm04431_eq_value :
    recordGapCenter + 147456 = fullRecordGapValue04431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04431 (fullRecordGapValue04431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04431_not_prime : ¬(recordGapCenter + 147456).Prime := by
  rw [fullRecordGapTerm04431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04431_fast_pow_mod_ne_one

def fullRecordGapValue04432 : Nat := fullRecordGapCenterValue + 147698

theorem fullRecordGapTerm04432_eq_value :
    recordGapCenter + 147698 = fullRecordGapValue04432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04432 (fullRecordGapValue04432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04432_not_prime : ¬(recordGapCenter + 147698).Prime := by
  rw [fullRecordGapTerm04432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04432_fast_pow_mod_ne_one

def fullRecordGapValue04433 : Nat := fullRecordGapCenterValue + 147878

theorem fullRecordGapTerm04433_eq_value :
    recordGapCenter + 147878 = fullRecordGapValue04433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04433 (fullRecordGapValue04433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04433_not_prime : ¬(recordGapCenter + 147878).Prime := by
  rw [fullRecordGapTerm04433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04433_fast_pow_mod_ne_one

def fullRecordGapValue04434 : Nat := fullRecordGapCenterValue + 148142

theorem fullRecordGapTerm04434_eq_value :
    recordGapCenter + 148142 = fullRecordGapValue04434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04434 (fullRecordGapValue04434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04434_not_prime : ¬(recordGapCenter + 148142).Prime := by
  rw [fullRecordGapTerm04434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04434_fast_pow_mod_ne_one

def fullRecordGapValue04435 : Nat := fullRecordGapCenterValue + 148202

theorem fullRecordGapTerm04435_eq_value :
    recordGapCenter + 148202 = fullRecordGapValue04435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04435 (fullRecordGapValue04435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04435_not_prime : ¬(recordGapCenter + 148202).Prime := by
  rw [fullRecordGapTerm04435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04435_fast_pow_mod_ne_one

def fullRecordGapValue04436 : Nat := fullRecordGapCenterValue + 148262

theorem fullRecordGapTerm04436_eq_value :
    recordGapCenter + 148262 = fullRecordGapValue04436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04436 (fullRecordGapValue04436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04436_not_prime : ¬(recordGapCenter + 148262).Prime := by
  rw [fullRecordGapTerm04436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04436_fast_pow_mod_ne_one

def fullRecordGapValue04437 : Nat := fullRecordGapCenterValue + 148286

theorem fullRecordGapTerm04437_eq_value :
    recordGapCenter + 148286 = fullRecordGapValue04437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04437 (fullRecordGapValue04437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04437_not_prime : ¬(recordGapCenter + 148286).Prime := by
  rw [fullRecordGapTerm04437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04437_fast_pow_mod_ne_one

def fullRecordGapValue04438 : Nat := fullRecordGapCenterValue + 148766

theorem fullRecordGapTerm04438_eq_value :
    recordGapCenter + 148766 = fullRecordGapValue04438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04438 (fullRecordGapValue04438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04438_not_prime : ¬(recordGapCenter + 148766).Prime := by
  rw [fullRecordGapTerm04438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04438_fast_pow_mod_ne_one

def fullRecordGapValue04439 : Nat := fullRecordGapCenterValue + 149072

theorem fullRecordGapTerm04439_eq_value :
    recordGapCenter + 149072 = fullRecordGapValue04439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04439 (fullRecordGapValue04439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04439_not_prime : ¬(recordGapCenter + 149072).Prime := by
  rw [fullRecordGapTerm04439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04439_fast_pow_mod_ne_one

def fullRecordGapValue04440 : Nat := fullRecordGapCenterValue + 149306

theorem fullRecordGapTerm04440_eq_value :
    recordGapCenter + 149306 = fullRecordGapValue04440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04440 (fullRecordGapValue04440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04440_not_prime : ¬(recordGapCenter + 149306).Prime := by
  rw [fullRecordGapTerm04440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04440_fast_pow_mod_ne_one

def fullRecordGapValue04441 : Nat := fullRecordGapCenterValue + 149426

theorem fullRecordGapTerm04441_eq_value :
    recordGapCenter + 149426 = fullRecordGapValue04441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04441 (fullRecordGapValue04441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04441_not_prime : ¬(recordGapCenter + 149426).Prime := by
  rw [fullRecordGapTerm04441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04441_fast_pow_mod_ne_one

def fullRecordGapValue04442 : Nat := fullRecordGapCenterValue + 149438

theorem fullRecordGapTerm04442_eq_value :
    recordGapCenter + 149438 = fullRecordGapValue04442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04442 (fullRecordGapValue04442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04442_not_prime : ¬(recordGapCenter + 149438).Prime := by
  rw [fullRecordGapTerm04442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04442_fast_pow_mod_ne_one

def fullRecordGapValue04443 : Nat := fullRecordGapCenterValue + 149462

theorem fullRecordGapTerm04443_eq_value :
    recordGapCenter + 149462 = fullRecordGapValue04443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04443 (fullRecordGapValue04443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04443_not_prime : ¬(recordGapCenter + 149462).Prime := by
  rw [fullRecordGapTerm04443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04443_fast_pow_mod_ne_one

def fullRecordGapValue04444 : Nat := fullRecordGapCenterValue + 149642

theorem fullRecordGapTerm04444_eq_value :
    recordGapCenter + 149642 = fullRecordGapValue04444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04444 (fullRecordGapValue04444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04444_not_prime : ¬(recordGapCenter + 149642).Prime := by
  rw [fullRecordGapTerm04444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04444_fast_pow_mod_ne_one

def fullRecordGapValue04445 : Nat := fullRecordGapCenterValue + 149846

theorem fullRecordGapTerm04445_eq_value :
    recordGapCenter + 149846 = fullRecordGapValue04445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04445 (fullRecordGapValue04445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04445_not_prime : ¬(recordGapCenter + 149846).Prime := by
  rw [fullRecordGapTerm04445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04445_fast_pow_mod_ne_one

def fullRecordGapValue04446 : Nat := fullRecordGapCenterValue + 150000

theorem fullRecordGapTerm04446_eq_value :
    recordGapCenter + 150000 = fullRecordGapValue04446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04446 (fullRecordGapValue04446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04446_not_prime : ¬(recordGapCenter + 150000).Prime := by
  rw [fullRecordGapTerm04446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04446_fast_pow_mod_ne_one

def fullRecordGapValue04447 : Nat := fullRecordGapCenterValue + 150158

theorem fullRecordGapTerm04447_eq_value :
    recordGapCenter + 150158 = fullRecordGapValue04447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04447 (fullRecordGapValue04447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04447_not_prime : ¬(recordGapCenter + 150158).Prime := by
  rw [fullRecordGapTerm04447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04447_fast_pow_mod_ne_one

def fullRecordGapValue04448 : Nat := fullRecordGapCenterValue + 150266

theorem fullRecordGapTerm04448_eq_value :
    recordGapCenter + 150266 = fullRecordGapValue04448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04448 (fullRecordGapValue04448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04448_not_prime : ¬(recordGapCenter + 150266).Prime := by
  rw [fullRecordGapTerm04448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04448_fast_pow_mod_ne_one

def fullRecordGapValue04449 : Nat := fullRecordGapCenterValue + 150446

theorem fullRecordGapTerm04449_eq_value :
    recordGapCenter + 150446 = fullRecordGapValue04449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04449 (fullRecordGapValue04449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04449_not_prime : ¬(recordGapCenter + 150446).Prime := by
  rw [fullRecordGapTerm04449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04449_fast_pow_mod_ne_one

def fullRecordGapValue04450 : Nat := fullRecordGapCenterValue + 150578

theorem fullRecordGapTerm04450_eq_value :
    recordGapCenter + 150578 = fullRecordGapValue04450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04450 (fullRecordGapValue04450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04450_not_prime : ¬(recordGapCenter + 150578).Prime := by
  rw [fullRecordGapTerm04450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04450_fast_pow_mod_ne_one

def fullRecordGapValue04451 : Nat := fullRecordGapCenterValue + 150920

theorem fullRecordGapTerm04451_eq_value :
    recordGapCenter + 150920 = fullRecordGapValue04451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04451 (fullRecordGapValue04451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04451_not_prime : ¬(recordGapCenter + 150920).Prime := by
  rw [fullRecordGapTerm04451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04451_fast_pow_mod_ne_one

def fullRecordGapValue04452 : Nat := fullRecordGapCenterValue + 151142

theorem fullRecordGapTerm04452_eq_value :
    recordGapCenter + 151142 = fullRecordGapValue04452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04452 (fullRecordGapValue04452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04452_not_prime : ¬(recordGapCenter + 151142).Prime := by
  rw [fullRecordGapTerm04452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04452_fast_pow_mod_ne_one

def fullRecordGapValue04453 : Nat := fullRecordGapCenterValue + 151200

theorem fullRecordGapTerm04453_eq_value :
    recordGapCenter + 151200 = fullRecordGapValue04453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04453 (fullRecordGapValue04453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04453_not_prime : ¬(recordGapCenter + 151200).Prime := by
  rw [fullRecordGapTerm04453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04453_fast_pow_mod_ne_one

def fullRecordGapValue04454 : Nat := fullRecordGapCenterValue + 151250

theorem fullRecordGapTerm04454_eq_value :
    recordGapCenter + 151250 = fullRecordGapValue04454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04454 (fullRecordGapValue04454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04454_not_prime : ¬(recordGapCenter + 151250).Prime := by
  rw [fullRecordGapTerm04454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04454_fast_pow_mod_ne_one

def fullRecordGapValue04455 : Nat := fullRecordGapCenterValue + 151358

theorem fullRecordGapTerm04455_eq_value :
    recordGapCenter + 151358 = fullRecordGapValue04455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04455 (fullRecordGapValue04455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04455_not_prime : ¬(recordGapCenter + 151358).Prime := by
  rw [fullRecordGapTerm04455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04455_fast_pow_mod_ne_one

def fullRecordGapValue04456 : Nat := fullRecordGapCenterValue + 151586

theorem fullRecordGapTerm04456_eq_value :
    recordGapCenter + 151586 = fullRecordGapValue04456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04456 (fullRecordGapValue04456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04456_not_prime : ¬(recordGapCenter + 151586).Prime := by
  rw [fullRecordGapTerm04456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04456_fast_pow_mod_ne_one

def fullRecordGapValue04457 : Nat := fullRecordGapCenterValue + 151706

theorem fullRecordGapTerm04457_eq_value :
    recordGapCenter + 151706 = fullRecordGapValue04457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04457 (fullRecordGapValue04457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04457_not_prime : ¬(recordGapCenter + 151706).Prime := by
  rw [fullRecordGapTerm04457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04457_fast_pow_mod_ne_one

def fullRecordGapValue04458 : Nat := fullRecordGapCenterValue + 151826

theorem fullRecordGapTerm04458_eq_value :
    recordGapCenter + 151826 = fullRecordGapValue04458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04458 (fullRecordGapValue04458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04458_not_prime : ¬(recordGapCenter + 151826).Prime := by
  rw [fullRecordGapTerm04458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04458_fast_pow_mod_ne_one

def fullRecordGapValue04459 : Nat := fullRecordGapCenterValue + 152078

theorem fullRecordGapTerm04459_eq_value :
    recordGapCenter + 152078 = fullRecordGapValue04459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04459 (fullRecordGapValue04459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04459_not_prime : ¬(recordGapCenter + 152078).Prime := by
  rw [fullRecordGapTerm04459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04459_fast_pow_mod_ne_one

def fullRecordGapValue04460 : Nat := fullRecordGapCenterValue + 152162

theorem fullRecordGapTerm04460_eq_value :
    recordGapCenter + 152162 = fullRecordGapValue04460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04460 (fullRecordGapValue04460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04460_not_prime : ¬(recordGapCenter + 152162).Prime := by
  rw [fullRecordGapTerm04460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04460_fast_pow_mod_ne_one

def fullRecordGapValue04461 : Nat := fullRecordGapCenterValue + 152426

theorem fullRecordGapTerm04461_eq_value :
    recordGapCenter + 152426 = fullRecordGapValue04461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04461 (fullRecordGapValue04461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04461_not_prime : ¬(recordGapCenter + 152426).Prime := by
  rw [fullRecordGapTerm04461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04461_fast_pow_mod_ne_one

def fullRecordGapValue04462 : Nat := fullRecordGapCenterValue + 152462

theorem fullRecordGapTerm04462_eq_value :
    recordGapCenter + 152462 = fullRecordGapValue04462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04462 (fullRecordGapValue04462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04462_not_prime : ¬(recordGapCenter + 152462).Prime := by
  rw [fullRecordGapTerm04462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04462_fast_pow_mod_ne_one

def fullRecordGapValue04463 : Nat := fullRecordGapCenterValue + 152486

theorem fullRecordGapTerm04463_eq_value :
    recordGapCenter + 152486 = fullRecordGapValue04463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04463 (fullRecordGapValue04463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04463_not_prime : ¬(recordGapCenter + 152486).Prime := by
  rw [fullRecordGapTerm04463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04463_fast_pow_mod_ne_one

def fullRecordGapValue04464 : Nat := fullRecordGapCenterValue + 152738

theorem fullRecordGapTerm04464_eq_value :
    recordGapCenter + 152738 = fullRecordGapValue04464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04464 (fullRecordGapValue04464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04464_not_prime : ¬(recordGapCenter + 152738).Prime := by
  rw [fullRecordGapTerm04464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04464_fast_pow_mod_ne_one

def fullRecordGapValue04465 : Nat := fullRecordGapCenterValue + 153090

theorem fullRecordGapTerm04465_eq_value :
    recordGapCenter + 153090 = fullRecordGapValue04465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04465 (fullRecordGapValue04465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04465_not_prime : ¬(recordGapCenter + 153090).Prime := by
  rw [fullRecordGapTerm04465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04465_fast_pow_mod_ne_one

def fullRecordGapValue04466 : Nat := fullRecordGapCenterValue + 153158

theorem fullRecordGapTerm04466_eq_value :
    recordGapCenter + 153158 = fullRecordGapValue04466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04466 (fullRecordGapValue04466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04466_not_prime : ¬(recordGapCenter + 153158).Prime := by
  rw [fullRecordGapTerm04466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04466_fast_pow_mod_ne_one

def fullRecordGapValue04467 : Nat := fullRecordGapCenterValue + 153602

theorem fullRecordGapTerm04467_eq_value :
    recordGapCenter + 153602 = fullRecordGapValue04467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04467 (fullRecordGapValue04467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04467_not_prime : ¬(recordGapCenter + 153602).Prime := by
  rw [fullRecordGapTerm04467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04467_fast_pow_mod_ne_one

def fullRecordGapValue04468 : Nat := fullRecordGapCenterValue + 153638

theorem fullRecordGapTerm04468_eq_value :
    recordGapCenter + 153638 = fullRecordGapValue04468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04468 (fullRecordGapValue04468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04468_not_prime : ¬(recordGapCenter + 153638).Prime := by
  rw [fullRecordGapTerm04468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04468_fast_pow_mod_ne_one

def fullRecordGapValue04469 : Nat := fullRecordGapCenterValue + 153662

theorem fullRecordGapTerm04469_eq_value :
    recordGapCenter + 153662 = fullRecordGapValue04469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04469 (fullRecordGapValue04469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04469_not_prime : ¬(recordGapCenter + 153662).Prime := by
  rw [fullRecordGapTerm04469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04469_fast_pow_mod_ne_one

def fullRecordGapValue04470 : Nat := fullRecordGapCenterValue + 153746

theorem fullRecordGapTerm04470_eq_value :
    recordGapCenter + 153746 = fullRecordGapValue04470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04470 (fullRecordGapValue04470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04470_not_prime : ¬(recordGapCenter + 153746).Prime := by
  rw [fullRecordGapTerm04470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04470_fast_pow_mod_ne_one

def fullRecordGapValue04471 : Nat := fullRecordGapCenterValue + 154058

theorem fullRecordGapTerm04471_eq_value :
    recordGapCenter + 154058 = fullRecordGapValue04471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04471 (fullRecordGapValue04471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04471_not_prime : ¬(recordGapCenter + 154058).Prime := by
  rw [fullRecordGapTerm04471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04471_fast_pow_mod_ne_one

def fullRecordGapValue04472 : Nat := fullRecordGapCenterValue + 154082

theorem fullRecordGapTerm04472_eq_value :
    recordGapCenter + 154082 = fullRecordGapValue04472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04472 (fullRecordGapValue04472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04472_not_prime : ¬(recordGapCenter + 154082).Prime := by
  rw [fullRecordGapTerm04472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04472_fast_pow_mod_ne_one

def fullRecordGapValue04473 : Nat := fullRecordGapCenterValue + 155138

theorem fullRecordGapTerm04473_eq_value :
    recordGapCenter + 155138 = fullRecordGapValue04473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04473 (fullRecordGapValue04473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04473_not_prime : ¬(recordGapCenter + 155138).Prime := by
  rw [fullRecordGapTerm04473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04473_fast_pow_mod_ne_one

def fullRecordGapValue04474 : Nat := fullRecordGapCenterValue + 155232

theorem fullRecordGapTerm04474_eq_value :
    recordGapCenter + 155232 = fullRecordGapValue04474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04474 (fullRecordGapValue04474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04474_not_prime : ¬(recordGapCenter + 155232).Prime := by
  rw [fullRecordGapTerm04474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04474_fast_pow_mod_ne_one

def fullRecordGapValue04475 : Nat := fullRecordGapCenterValue + 155486

theorem fullRecordGapTerm04475_eq_value :
    recordGapCenter + 155486 = fullRecordGapValue04475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04475 (fullRecordGapValue04475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04475_not_prime : ¬(recordGapCenter + 155486).Prime := by
  rw [fullRecordGapTerm04475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04475_fast_pow_mod_ne_one

def fullRecordGapValue04476 : Nat := fullRecordGapCenterValue + 155520

theorem fullRecordGapTerm04476_eq_value :
    recordGapCenter + 155520 = fullRecordGapValue04476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04476 (fullRecordGapValue04476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04476_not_prime : ¬(recordGapCenter + 155520).Prime := by
  rw [fullRecordGapTerm04476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04476_fast_pow_mod_ne_one

def fullRecordGapValue04477 : Nat := fullRecordGapCenterValue + 155522

theorem fullRecordGapTerm04477_eq_value :
    recordGapCenter + 155522 = fullRecordGapValue04477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04477 (fullRecordGapValue04477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04477_not_prime : ¬(recordGapCenter + 155522).Prime := by
  rw [fullRecordGapTerm04477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04477_fast_pow_mod_ne_one

def fullRecordGapValue04478 : Nat := fullRecordGapCenterValue + 156062

theorem fullRecordGapTerm04478_eq_value :
    recordGapCenter + 156062 = fullRecordGapValue04478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04478 (fullRecordGapValue04478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04478_not_prime : ¬(recordGapCenter + 156062).Prime := by
  rw [fullRecordGapTerm04478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04478_fast_pow_mod_ne_one

def fullRecordGapValue04479 : Nat := fullRecordGapCenterValue + 156158

theorem fullRecordGapTerm04479_eq_value :
    recordGapCenter + 156158 = fullRecordGapValue04479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04479 (fullRecordGapValue04479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04479_not_prime : ¬(recordGapCenter + 156158).Prime := by
  rw [fullRecordGapTerm04479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04479_fast_pow_mod_ne_one

def fullRecordGapValue04480 : Nat := fullRecordGapCenterValue + 156242

theorem fullRecordGapTerm04480_eq_value :
    recordGapCenter + 156242 = fullRecordGapValue04480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04480 (fullRecordGapValue04480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04480_not_prime : ¬(recordGapCenter + 156242).Prime := by
  rw [fullRecordGapTerm04480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04480_fast_pow_mod_ne_one

def fullRecordGapValue04481 : Nat := fullRecordGapCenterValue + 156326

theorem fullRecordGapTerm04481_eq_value :
    recordGapCenter + 156326 = fullRecordGapValue04481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04481 (fullRecordGapValue04481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04481_not_prime : ¬(recordGapCenter + 156326).Prime := by
  rw [fullRecordGapTerm04481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04481_fast_pow_mod_ne_one

def fullRecordGapValue04482 : Nat := fullRecordGapCenterValue + 156458

theorem fullRecordGapTerm04482_eq_value :
    recordGapCenter + 156458 = fullRecordGapValue04482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04482 (fullRecordGapValue04482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04482_not_prime : ¬(recordGapCenter + 156458).Prime := by
  rw [fullRecordGapTerm04482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04482_fast_pow_mod_ne_one

def fullRecordGapValue04483 : Nat := fullRecordGapCenterValue + 156816

theorem fullRecordGapTerm04483_eq_value :
    recordGapCenter + 156816 = fullRecordGapValue04483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04483 (fullRecordGapValue04483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04483_not_prime : ¬(recordGapCenter + 156816).Prime := by
  rw [fullRecordGapTerm04483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04483_fast_pow_mod_ne_one

def fullRecordGapValue04484 : Nat := fullRecordGapCenterValue + 157382

theorem fullRecordGapTerm04484_eq_value :
    recordGapCenter + 157382 = fullRecordGapValue04484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04484 (fullRecordGapValue04484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04484_not_prime : ¬(recordGapCenter + 157382).Prime := by
  rw [fullRecordGapTerm04484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04484_fast_pow_mod_ne_one

def fullRecordGapValue04485 : Nat := fullRecordGapCenterValue + 157706

theorem fullRecordGapTerm04485_eq_value :
    recordGapCenter + 157706 = fullRecordGapValue04485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04485 (fullRecordGapValue04485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04485_not_prime : ¬(recordGapCenter + 157706).Prime := by
  rw [fullRecordGapTerm04485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04485_fast_pow_mod_ne_one

def fullRecordGapValue04486 : Nat := fullRecordGapCenterValue + 157778

theorem fullRecordGapTerm04486_eq_value :
    recordGapCenter + 157778 = fullRecordGapValue04486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04486 (fullRecordGapValue04486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04486_not_prime : ¬(recordGapCenter + 157778).Prime := by
  rw [fullRecordGapTerm04486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04486_fast_pow_mod_ne_one

def fullRecordGapValue04487 : Nat := fullRecordGapCenterValue + 157958

theorem fullRecordGapTerm04487_eq_value :
    recordGapCenter + 157958 = fullRecordGapValue04487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04487 (fullRecordGapValue04487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04487_not_prime : ¬(recordGapCenter + 157958).Prime := by
  rw [fullRecordGapTerm04487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04487_fast_pow_mod_ne_one

def fullRecordGapValue04488 : Nat := fullRecordGapCenterValue + 158126

theorem fullRecordGapTerm04488_eq_value :
    recordGapCenter + 158126 = fullRecordGapValue04488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04488 (fullRecordGapValue04488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04488_not_prime : ¬(recordGapCenter + 158126).Prime := by
  rw [fullRecordGapTerm04488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04488_fast_pow_mod_ne_one

def fullRecordGapValue04489 : Nat := fullRecordGapCenterValue + 158400

theorem fullRecordGapTerm04489_eq_value :
    recordGapCenter + 158400 = fullRecordGapValue04489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04489 (fullRecordGapValue04489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04489_not_prime : ¬(recordGapCenter + 158400).Prime := by
  rw [fullRecordGapTerm04489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04489_fast_pow_mod_ne_one

def fullRecordGapValue04490 : Nat := fullRecordGapCenterValue + 158466

theorem fullRecordGapTerm04490_eq_value :
    recordGapCenter + 158466 = fullRecordGapValue04490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04490 (fullRecordGapValue04490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04490_not_prime : ¬(recordGapCenter + 158466).Prime := by
  rw [fullRecordGapTerm04490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04490_fast_pow_mod_ne_one

def fullRecordGapValue04491 : Nat := fullRecordGapCenterValue + 158558

theorem fullRecordGapTerm04491_eq_value :
    recordGapCenter + 158558 = fullRecordGapValue04491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04491 (fullRecordGapValue04491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04491_not_prime : ¬(recordGapCenter + 158558).Prime := by
  rw [fullRecordGapTerm04491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04491_fast_pow_mod_ne_one

def fullRecordGapValue04492 : Nat := fullRecordGapCenterValue + 158618

theorem fullRecordGapTerm04492_eq_value :
    recordGapCenter + 158618 = fullRecordGapValue04492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04492 (fullRecordGapValue04492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04492_not_prime : ¬(recordGapCenter + 158618).Prime := by
  rw [fullRecordGapTerm04492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04492_fast_pow_mod_ne_one

def fullRecordGapValue04493 : Nat := fullRecordGapCenterValue + 158786

theorem fullRecordGapTerm04493_eq_value :
    recordGapCenter + 158786 = fullRecordGapValue04493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04493 (fullRecordGapValue04493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04493_not_prime : ¬(recordGapCenter + 158786).Prime := by
  rw [fullRecordGapTerm04493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04493_fast_pow_mod_ne_one

def fullRecordGapValue04494 : Nat := fullRecordGapCenterValue + 158798

theorem fullRecordGapTerm04494_eq_value :
    recordGapCenter + 158798 = fullRecordGapValue04494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04494 (fullRecordGapValue04494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04494_not_prime : ¬(recordGapCenter + 158798).Prime := by
  rw [fullRecordGapTerm04494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04494_fast_pow_mod_ne_one

def fullRecordGapValue04495 : Nat := fullRecordGapCenterValue + 159218

theorem fullRecordGapTerm04495_eq_value :
    recordGapCenter + 159218 = fullRecordGapValue04495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04495 (fullRecordGapValue04495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04495_not_prime : ¬(recordGapCenter + 159218).Prime := by
  rw [fullRecordGapTerm04495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04495_fast_pow_mod_ne_one

def fullRecordGapValue04496 : Nat := fullRecordGapCenterValue + 159266

theorem fullRecordGapTerm04496_eq_value :
    recordGapCenter + 159266 = fullRecordGapValue04496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04496 (fullRecordGapValue04496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04496_not_prime : ¬(recordGapCenter + 159266).Prime := by
  rw [fullRecordGapTerm04496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04496_fast_pow_mod_ne_one

def fullRecordGapValue04497 : Nat := fullRecordGapCenterValue + 159398

theorem fullRecordGapTerm04497_eq_value :
    recordGapCenter + 159398 = fullRecordGapValue04497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04497 (fullRecordGapValue04497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04497_not_prime : ¬(recordGapCenter + 159398).Prime := by
  rw [fullRecordGapTerm04497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04497_fast_pow_mod_ne_one

def fullRecordGapValue04498 : Nat := fullRecordGapCenterValue + 159602

theorem fullRecordGapTerm04498_eq_value :
    recordGapCenter + 159602 = fullRecordGapValue04498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04498 (fullRecordGapValue04498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04498_not_prime : ¬(recordGapCenter + 159602).Prime := by
  rw [fullRecordGapTerm04498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04498_fast_pow_mod_ne_one

def fullRecordGapValue04499 : Nat := fullRecordGapCenterValue + 159626

theorem fullRecordGapTerm04499_eq_value :
    recordGapCenter + 159626 = fullRecordGapValue04499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04499 (fullRecordGapValue04499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04499_not_prime : ¬(recordGapCenter + 159626).Prime := by
  rw [fullRecordGapTerm04499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04499_fast_pow_mod_ne_one

def fullRecordGapValue04500 : Nat := fullRecordGapCenterValue + 159720

theorem fullRecordGapTerm04500_eq_value :
    recordGapCenter + 159720 = fullRecordGapValue04500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04500 (fullRecordGapValue04500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04500_not_prime : ¬(recordGapCenter + 159720).Prime := by
  rw [fullRecordGapTerm04500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04500_fast_pow_mod_ne_one

def fullRecordGapValue04501 : Nat := fullRecordGapCenterValue + 159878

theorem fullRecordGapTerm04501_eq_value :
    recordGapCenter + 159878 = fullRecordGapValue04501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04501 (fullRecordGapValue04501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04501_not_prime : ¬(recordGapCenter + 159878).Prime := by
  rw [fullRecordGapTerm04501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04501_fast_pow_mod_ne_one

def fullRecordGapValue04502 : Nat := fullRecordGapCenterValue + 160142

theorem fullRecordGapTerm04502_eq_value :
    recordGapCenter + 160142 = fullRecordGapValue04502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04502 (fullRecordGapValue04502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04502_not_prime : ¬(recordGapCenter + 160142).Prime := by
  rw [fullRecordGapTerm04502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04502_fast_pow_mod_ne_one

def fullRecordGapValue04503 : Nat := fullRecordGapCenterValue + 160346

theorem fullRecordGapTerm04503_eq_value :
    recordGapCenter + 160346 = fullRecordGapValue04503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04503 (fullRecordGapValue04503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04503_not_prime : ¬(recordGapCenter + 160346).Prime := by
  rw [fullRecordGapTerm04503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04503_fast_pow_mod_ne_one

def fullRecordGapValue04504 : Nat := fullRecordGapCenterValue + 160382

theorem fullRecordGapTerm04504_eq_value :
    recordGapCenter + 160382 = fullRecordGapValue04504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04504 (fullRecordGapValue04504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04504_not_prime : ¬(recordGapCenter + 160382).Prime := by
  rw [fullRecordGapTerm04504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04504_fast_pow_mod_ne_one

def fullRecordGapValue04505 : Nat := fullRecordGapCenterValue + 160526

theorem fullRecordGapTerm04505_eq_value :
    recordGapCenter + 160526 = fullRecordGapValue04505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04505 (fullRecordGapValue04505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04505_not_prime : ¬(recordGapCenter + 160526).Prime := by
  rw [fullRecordGapTerm04505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04505_fast_pow_mod_ne_one

def fullRecordGapValue04506 : Nat := fullRecordGapCenterValue + 160682

theorem fullRecordGapTerm04506_eq_value :
    recordGapCenter + 160682 = fullRecordGapValue04506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04506 (fullRecordGapValue04506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04506_not_prime : ¬(recordGapCenter + 160682).Prime := by
  rw [fullRecordGapTerm04506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04506_fast_pow_mod_ne_one

def fullRecordGapValue04507 : Nat := fullRecordGapCenterValue + 160898

theorem fullRecordGapTerm04507_eq_value :
    recordGapCenter + 160898 = fullRecordGapValue04507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04507 (fullRecordGapValue04507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04507_not_prime : ¬(recordGapCenter + 160898).Prime := by
  rw [fullRecordGapTerm04507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04507_fast_pow_mod_ne_one

def fullRecordGapValue04508 : Nat := fullRecordGapCenterValue + 161618

theorem fullRecordGapTerm04508_eq_value :
    recordGapCenter + 161618 = fullRecordGapValue04508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04508 (fullRecordGapValue04508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04508_not_prime : ¬(recordGapCenter + 161618).Prime := by
  rw [fullRecordGapTerm04508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04508_fast_pow_mod_ne_one

def fullRecordGapValue04509 : Nat := fullRecordGapCenterValue + 161822

theorem fullRecordGapTerm04509_eq_value :
    recordGapCenter + 161822 = fullRecordGapValue04509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04509 (fullRecordGapValue04509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04509_not_prime : ¬(recordGapCenter + 161822).Prime := by
  rw [fullRecordGapTerm04509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04509_fast_pow_mod_ne_one

def fullRecordGapValue04510 : Nat := fullRecordGapCenterValue + 161858

theorem fullRecordGapTerm04510_eq_value :
    recordGapCenter + 161858 = fullRecordGapValue04510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04510 (fullRecordGapValue04510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04510_not_prime : ¬(recordGapCenter + 161858).Prime := by
  rw [fullRecordGapTerm04510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04510_fast_pow_mod_ne_one

def fullRecordGapValue04511 : Nat := fullRecordGapCenterValue + 161906

theorem fullRecordGapTerm04511_eq_value :
    recordGapCenter + 161906 = fullRecordGapValue04511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04511 (fullRecordGapValue04511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04511_not_prime : ¬(recordGapCenter + 161906).Prime := by
  rw [fullRecordGapTerm04511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04511_fast_pow_mod_ne_one

def fullRecordGapValue04512 : Nat := fullRecordGapCenterValue + 162362

theorem fullRecordGapTerm04512_eq_value :
    recordGapCenter + 162362 = fullRecordGapValue04512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04512 (fullRecordGapValue04512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04512_not_prime : ¬(recordGapCenter + 162362).Prime := by
  rw [fullRecordGapTerm04512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04512_fast_pow_mod_ne_one

def fullRecordGapValue04513 : Nat := fullRecordGapCenterValue + 162662

theorem fullRecordGapTerm04513_eq_value :
    recordGapCenter + 162662 = fullRecordGapValue04513 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04513_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04513 (fullRecordGapValue04513 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04513_not_prime : ¬(recordGapCenter + 162662).Prime := by
  rw [fullRecordGapTerm04513_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04513, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04513_fast_pow_mod_ne_one

def fullRecordGapValue04514 : Nat := fullRecordGapCenterValue + 162878

theorem fullRecordGapTerm04514_eq_value :
    recordGapCenter + 162878 = fullRecordGapValue04514 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04514_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04514 (fullRecordGapValue04514 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04514_not_prime : ¬(recordGapCenter + 162878).Prime := by
  rw [fullRecordGapTerm04514_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04514, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04514_fast_pow_mod_ne_one

def fullRecordGapValue04515 : Nat := fullRecordGapCenterValue + 162926

theorem fullRecordGapTerm04515_eq_value :
    recordGapCenter + 162926 = fullRecordGapValue04515 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04515_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04515 (fullRecordGapValue04515 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04515_not_prime : ¬(recordGapCenter + 162926).Prime := by
  rw [fullRecordGapTerm04515_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04515, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04515_fast_pow_mod_ne_one

def fullRecordGapValue04516 : Nat := fullRecordGapCenterValue + 163238

theorem fullRecordGapTerm04516_eq_value :
    recordGapCenter + 163238 = fullRecordGapValue04516 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04516_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04516 (fullRecordGapValue04516 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04516_not_prime : ¬(recordGapCenter + 163238).Prime := by
  rw [fullRecordGapTerm04516_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04516, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04516_fast_pow_mod_ne_one

def fullRecordGapValue04517 : Nat := fullRecordGapCenterValue + 163298

theorem fullRecordGapTerm04517_eq_value :
    recordGapCenter + 163298 = fullRecordGapValue04517 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04517_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04517 (fullRecordGapValue04517 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04517_not_prime : ¬(recordGapCenter + 163298).Prime := by
  rw [fullRecordGapTerm04517_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04517, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04517_fast_pow_mod_ne_one

def fullRecordGapValue04518 : Nat := fullRecordGapCenterValue + 163350

theorem fullRecordGapTerm04518_eq_value :
    recordGapCenter + 163350 = fullRecordGapValue04518 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04518_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04518 (fullRecordGapValue04518 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04518_not_prime : ¬(recordGapCenter + 163350).Prime := by
  rw [fullRecordGapTerm04518_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04518, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04518_fast_pow_mod_ne_one

def fullRecordGapValue04519 : Nat := fullRecordGapCenterValue + 163406

theorem fullRecordGapTerm04519_eq_value :
    recordGapCenter + 163406 = fullRecordGapValue04519 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04519_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04519 (fullRecordGapValue04519 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04519_not_prime : ¬(recordGapCenter + 163406).Prime := by
  rw [fullRecordGapTerm04519_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04519, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04519_fast_pow_mod_ne_one

def fullRecordGapValue04520 : Nat := fullRecordGapCenterValue + 163538

theorem fullRecordGapTerm04520_eq_value :
    recordGapCenter + 163538 = fullRecordGapValue04520 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04520_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04520 (fullRecordGapValue04520 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04520_not_prime : ¬(recordGapCenter + 163538).Prime := by
  rw [fullRecordGapTerm04520_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04520, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04520_fast_pow_mod_ne_one

def fullRecordGapValue04521 : Nat := fullRecordGapCenterValue + 163598

theorem fullRecordGapTerm04521_eq_value :
    recordGapCenter + 163598 = fullRecordGapValue04521 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04521_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04521 (fullRecordGapValue04521 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04521_not_prime : ¬(recordGapCenter + 163598).Prime := by
  rw [fullRecordGapTerm04521_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04521, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04521_fast_pow_mod_ne_one

def fullRecordGapValue04522 : Nat := fullRecordGapCenterValue + 163706

theorem fullRecordGapTerm04522_eq_value :
    recordGapCenter + 163706 = fullRecordGapValue04522 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04522_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04522 (fullRecordGapValue04522 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04522_not_prime : ¬(recordGapCenter + 163706).Prime := by
  rw [fullRecordGapTerm04522_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04522, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04522_fast_pow_mod_ne_one

def fullRecordGapValue04523 : Nat := fullRecordGapCenterValue + 163766

theorem fullRecordGapTerm04523_eq_value :
    recordGapCenter + 163766 = fullRecordGapValue04523 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04523_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04523 (fullRecordGapValue04523 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04523_not_prime : ¬(recordGapCenter + 163766).Prime := by
  rw [fullRecordGapTerm04523_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04523, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04523_fast_pow_mod_ne_one

def fullRecordGapValue04524 : Nat := fullRecordGapCenterValue + 163802

theorem fullRecordGapTerm04524_eq_value :
    recordGapCenter + 163802 = fullRecordGapValue04524 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04524_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04524 (fullRecordGapValue04524 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04524_not_prime : ¬(recordGapCenter + 163802).Prime := by
  rw [fullRecordGapTerm04524_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04524, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04524_fast_pow_mod_ne_one

def fullRecordGapValue04525 : Nat := fullRecordGapCenterValue + 163838

theorem fullRecordGapTerm04525_eq_value :
    recordGapCenter + 163838 = fullRecordGapValue04525 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04525_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04525 (fullRecordGapValue04525 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04525_not_prime : ¬(recordGapCenter + 163838).Prime := by
  rw [fullRecordGapTerm04525_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04525, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04525_fast_pow_mod_ne_one

def fullRecordGapValue04526 : Nat := fullRecordGapCenterValue + 164018

theorem fullRecordGapTerm04526_eq_value :
    recordGapCenter + 164018 = fullRecordGapValue04526 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04526_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04526 (fullRecordGapValue04526 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04526_not_prime : ¬(recordGapCenter + 164018).Prime := by
  rw [fullRecordGapTerm04526_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04526, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04526_fast_pow_mod_ne_one

def fullRecordGapValue04527 : Nat := fullRecordGapCenterValue + 164102

theorem fullRecordGapTerm04527_eq_value :
    recordGapCenter + 164102 = fullRecordGapValue04527 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04527_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04527 (fullRecordGapValue04527 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04527_not_prime : ¬(recordGapCenter + 164102).Prime := by
  rw [fullRecordGapTerm04527_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04527, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04527_fast_pow_mod_ne_one

def fullRecordGapValue04528 : Nat := fullRecordGapCenterValue + 164258

theorem fullRecordGapTerm04528_eq_value :
    recordGapCenter + 164258 = fullRecordGapValue04528 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04528_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04528 (fullRecordGapValue04528 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04528_not_prime : ¬(recordGapCenter + 164258).Prime := by
  rw [fullRecordGapTerm04528_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04528, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04528_fast_pow_mod_ne_one

def fullRecordGapValue04529 : Nat := fullRecordGapCenterValue + 164438

theorem fullRecordGapTerm04529_eq_value :
    recordGapCenter + 164438 = fullRecordGapValue04529 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04529_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04529 (fullRecordGapValue04529 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04529_not_prime : ¬(recordGapCenter + 164438).Prime := by
  rw [fullRecordGapTerm04529_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04529, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04529_fast_pow_mod_ne_one

def fullRecordGapValue04530 : Nat := fullRecordGapCenterValue + 164678

theorem fullRecordGapTerm04530_eq_value :
    recordGapCenter + 164678 = fullRecordGapValue04530 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04530_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04530 (fullRecordGapValue04530 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04530_not_prime : ¬(recordGapCenter + 164678).Prime := by
  rw [fullRecordGapTerm04530_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04530, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04530_fast_pow_mod_ne_one

def fullRecordGapValue04531 : Nat := fullRecordGapCenterValue + 164966

theorem fullRecordGapTerm04531_eq_value :
    recordGapCenter + 164966 = fullRecordGapValue04531 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04531_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04531 (fullRecordGapValue04531 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04531_not_prime : ¬(recordGapCenter + 164966).Prime := by
  rw [fullRecordGapTerm04531_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04531, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04531_fast_pow_mod_ne_one

def fullRecordGapValue04532 : Nat := fullRecordGapCenterValue + 165182

theorem fullRecordGapTerm04532_eq_value :
    recordGapCenter + 165182 = fullRecordGapValue04532 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04532_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04532 (fullRecordGapValue04532 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04532_not_prime : ¬(recordGapCenter + 165182).Prime := by
  rw [fullRecordGapTerm04532_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04532, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04532_fast_pow_mod_ne_one

def fullRecordGapValue04533 : Nat := fullRecordGapCenterValue + 165398

theorem fullRecordGapTerm04533_eq_value :
    recordGapCenter + 165398 = fullRecordGapValue04533 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04533_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04533 (fullRecordGapValue04533 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04533_not_prime : ¬(recordGapCenter + 165398).Prime := by
  rw [fullRecordGapTerm04533_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04533, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04533_fast_pow_mod_ne_one

def fullRecordGapValue04534 : Nat := fullRecordGapCenterValue + 165518

theorem fullRecordGapTerm04534_eq_value :
    recordGapCenter + 165518 = fullRecordGapValue04534 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04534_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04534 (fullRecordGapValue04534 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04534_not_prime : ¬(recordGapCenter + 165518).Prime := by
  rw [fullRecordGapTerm04534_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04534, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04534_fast_pow_mod_ne_one

def fullRecordGapValue04535 : Nat := fullRecordGapCenterValue + 166178

theorem fullRecordGapTerm04535_eq_value :
    recordGapCenter + 166178 = fullRecordGapValue04535 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04535_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04535 (fullRecordGapValue04535 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04535_not_prime : ¬(recordGapCenter + 166178).Prime := by
  rw [fullRecordGapTerm04535_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04535, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04535_fast_pow_mod_ne_one

def fullRecordGapValue04536 : Nat := fullRecordGapCenterValue + 166406

theorem fullRecordGapTerm04536_eq_value :
    recordGapCenter + 166406 = fullRecordGapValue04536 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04536_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04536 (fullRecordGapValue04536 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04536_not_prime : ¬(recordGapCenter + 166406).Prime := by
  rw [fullRecordGapTerm04536_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04536, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04536_fast_pow_mod_ne_one

def fullRecordGapValue04537 : Nat := fullRecordGapCenterValue + 166698

theorem fullRecordGapTerm04537_eq_value :
    recordGapCenter + 166698 = fullRecordGapValue04537 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04537_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04537 (fullRecordGapValue04537 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04537_not_prime : ¬(recordGapCenter + 166698).Prime := by
  rw [fullRecordGapTerm04537_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04537, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04537_fast_pow_mod_ne_one

def fullRecordGapValue04538 : Nat := fullRecordGapCenterValue + 167126

theorem fullRecordGapTerm04538_eq_value :
    recordGapCenter + 167126 = fullRecordGapValue04538 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04538_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04538 (fullRecordGapValue04538 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04538_not_prime : ¬(recordGapCenter + 167126).Prime := by
  rw [fullRecordGapTerm04538_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04538, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04538_fast_pow_mod_ne_one

def fullRecordGapValue04539 : Nat := fullRecordGapCenterValue + 167402

theorem fullRecordGapTerm04539_eq_value :
    recordGapCenter + 167402 = fullRecordGapValue04539 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04539_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04539 (fullRecordGapValue04539 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04539_not_prime : ¬(recordGapCenter + 167402).Prime := by
  rw [fullRecordGapTerm04539_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04539, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04539_fast_pow_mod_ne_one

def fullRecordGapValue04540 : Nat := fullRecordGapCenterValue + 167546

theorem fullRecordGapTerm04540_eq_value :
    recordGapCenter + 167546 = fullRecordGapValue04540 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04540_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04540 (fullRecordGapValue04540 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04540_not_prime : ¬(recordGapCenter + 167546).Prime := by
  rw [fullRecordGapTerm04540_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04540, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04540_fast_pow_mod_ne_one

def fullRecordGapValue04541 : Nat := fullRecordGapCenterValue + 167666

theorem fullRecordGapTerm04541_eq_value :
    recordGapCenter + 167666 = fullRecordGapValue04541 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04541_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04541 (fullRecordGapValue04541 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04541_not_prime : ¬(recordGapCenter + 167666).Prime := by
  rw [fullRecordGapTerm04541_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04541, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04541_fast_pow_mod_ne_one

def fullRecordGapValue04542 : Nat := fullRecordGapCenterValue + 168326

theorem fullRecordGapTerm04542_eq_value :
    recordGapCenter + 168326 = fullRecordGapValue04542 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04542_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04542 (fullRecordGapValue04542 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04542_not_prime : ¬(recordGapCenter + 168326).Prime := by
  rw [fullRecordGapTerm04542_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04542, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04542_fast_pow_mod_ne_one

def fullRecordGapValue04543 : Nat := fullRecordGapCenterValue + 168422

theorem fullRecordGapTerm04543_eq_value :
    recordGapCenter + 168422 = fullRecordGapValue04543 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04543_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04543 (fullRecordGapValue04543 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04543_not_prime : ¬(recordGapCenter + 168422).Prime := by
  rw [fullRecordGapTerm04543_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04543, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04543_fast_pow_mod_ne_one

def fullRecordGapValue04544 : Nat := fullRecordGapCenterValue + 168782

theorem fullRecordGapTerm04544_eq_value :
    recordGapCenter + 168782 = fullRecordGapValue04544 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04544_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04544 (fullRecordGapValue04544 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04544_not_prime : ¬(recordGapCenter + 168782).Prime := by
  rw [fullRecordGapTerm04544_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04544, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04544_fast_pow_mod_ne_one

def fullRecordGapValue04545 : Nat := fullRecordGapCenterValue + 168842

theorem fullRecordGapTerm04545_eq_value :
    recordGapCenter + 168842 = fullRecordGapValue04545 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04545_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04545 (fullRecordGapValue04545 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04545_not_prime : ¬(recordGapCenter + 168842).Prime := by
  rw [fullRecordGapTerm04545_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04545, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04545_fast_pow_mod_ne_one

def fullRecordGapValue04546 : Nat := fullRecordGapCenterValue + 168926

theorem fullRecordGapTerm04546_eq_value :
    recordGapCenter + 168926 = fullRecordGapValue04546 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04546_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04546 (fullRecordGapValue04546 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04546_not_prime : ¬(recordGapCenter + 168926).Prime := by
  rw [fullRecordGapTerm04546_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04546, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04546_fast_pow_mod_ne_one

def fullRecordGapValue04547 : Nat := fullRecordGapCenterValue + 168960

theorem fullRecordGapTerm04547_eq_value :
    recordGapCenter + 168960 = fullRecordGapValue04547 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04547_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04547 (fullRecordGapValue04547 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04547_not_prime : ¬(recordGapCenter + 168960).Prime := by
  rw [fullRecordGapTerm04547_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04547, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04547_fast_pow_mod_ne_one

def fullRecordGapValue04548 : Nat := fullRecordGapCenterValue + 168962

theorem fullRecordGapTerm04548_eq_value :
    recordGapCenter + 168962 = fullRecordGapValue04548 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04548_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04548 (fullRecordGapValue04548 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04548_not_prime : ¬(recordGapCenter + 168962).Prime := by
  rw [fullRecordGapTerm04548_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04548, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04548_fast_pow_mod_ne_one

def fullRecordGapValue04549 : Nat := fullRecordGapCenterValue + 169046

theorem fullRecordGapTerm04549_eq_value :
    recordGapCenter + 169046 = fullRecordGapValue04549 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04549_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04549 (fullRecordGapValue04549 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04549_not_prime : ¬(recordGapCenter + 169046).Prime := by
  rw [fullRecordGapTerm04549_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04549, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04549_fast_pow_mod_ne_one

def fullRecordGapValue04550 : Nat := fullRecordGapCenterValue + 169382

theorem fullRecordGapTerm04550_eq_value :
    recordGapCenter + 169382 = fullRecordGapValue04550 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04550_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04550 (fullRecordGapValue04550 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04550_not_prime : ¬(recordGapCenter + 169382).Prime := by
  rw [fullRecordGapTerm04550_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04550, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04550_fast_pow_mod_ne_one

def fullRecordGapValue04551 : Nat := fullRecordGapCenterValue + 169586

theorem fullRecordGapTerm04551_eq_value :
    recordGapCenter + 169586 = fullRecordGapValue04551 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04551_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04551 (fullRecordGapValue04551 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04551_not_prime : ¬(recordGapCenter + 169586).Prime := by
  rw [fullRecordGapTerm04551_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04551, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04551_fast_pow_mod_ne_one

def fullRecordGapValue04552 : Nat := fullRecordGapCenterValue + 169982

theorem fullRecordGapTerm04552_eq_value :
    recordGapCenter + 169982 = fullRecordGapValue04552 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04552_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04552 (fullRecordGapValue04552 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04552_not_prime : ¬(recordGapCenter + 169982).Prime := by
  rw [fullRecordGapTerm04552_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04552, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04552_fast_pow_mod_ne_one

def fullRecordGapValue04553 : Nat := fullRecordGapCenterValue + 170042

theorem fullRecordGapTerm04553_eq_value :
    recordGapCenter + 170042 = fullRecordGapValue04553 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04553_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04553 (fullRecordGapValue04553 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04553_not_prime : ¬(recordGapCenter + 170042).Prime := by
  rw [fullRecordGapTerm04553_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04553, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04553_fast_pow_mod_ne_one

def fullRecordGapValue04554 : Nat := fullRecordGapCenterValue + 170318

theorem fullRecordGapTerm04554_eq_value :
    recordGapCenter + 170318 = fullRecordGapValue04554 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04554_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04554 (fullRecordGapValue04554 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04554_not_prime : ¬(recordGapCenter + 170318).Prime := by
  rw [fullRecordGapTerm04554_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04554, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04554_fast_pow_mod_ne_one

def fullRecordGapValue04555 : Nat := fullRecordGapCenterValue + 170426

theorem fullRecordGapTerm04555_eq_value :
    recordGapCenter + 170426 = fullRecordGapValue04555 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04555_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04555 (fullRecordGapValue04555 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04555_not_prime : ¬(recordGapCenter + 170426).Prime := by
  rw [fullRecordGapTerm04555_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04555, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04555_fast_pow_mod_ne_one

def fullRecordGapValue04556 : Nat := fullRecordGapCenterValue + 170726

theorem fullRecordGapTerm04556_eq_value :
    recordGapCenter + 170726 = fullRecordGapValue04556 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04556_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04556 (fullRecordGapValue04556 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04556_not_prime : ¬(recordGapCenter + 170726).Prime := by
  rw [fullRecordGapTerm04556_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04556, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04556_fast_pow_mod_ne_one

def fullRecordGapValue04557 : Nat := fullRecordGapCenterValue + 171278

theorem fullRecordGapTerm04557_eq_value :
    recordGapCenter + 171278 = fullRecordGapValue04557 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04557_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04557 (fullRecordGapValue04557 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04557_not_prime : ¬(recordGapCenter + 171278).Prime := by
  rw [fullRecordGapTerm04557_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04557, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04557_fast_pow_mod_ne_one

def fullRecordGapValue04558 : Nat := fullRecordGapCenterValue + 171638

theorem fullRecordGapTerm04558_eq_value :
    recordGapCenter + 171638 = fullRecordGapValue04558 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04558_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04558 (fullRecordGapValue04558 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04558_not_prime : ¬(recordGapCenter + 171638).Prime := by
  rw [fullRecordGapTerm04558_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04558, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04558_fast_pow_mod_ne_one

def fullRecordGapValue04559 : Nat := fullRecordGapCenterValue + 171686

theorem fullRecordGapTerm04559_eq_value :
    recordGapCenter + 171686 = fullRecordGapValue04559 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04559_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04559 (fullRecordGapValue04559 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04559_not_prime : ¬(recordGapCenter + 171686).Prime := by
  rw [fullRecordGapTerm04559_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04559, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04559_fast_pow_mod_ne_one

def fullRecordGapValue04560 : Nat := fullRecordGapCenterValue + 171818

theorem fullRecordGapTerm04560_eq_value :
    recordGapCenter + 171818 = fullRecordGapValue04560 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04560_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04560 (fullRecordGapValue04560 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04560_not_prime : ¬(recordGapCenter + 171818).Prime := by
  rw [fullRecordGapTerm04560_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04560, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04560_fast_pow_mod_ne_one

def fullRecordGapValue04561 : Nat := fullRecordGapCenterValue + 171866

theorem fullRecordGapTerm04561_eq_value :
    recordGapCenter + 171866 = fullRecordGapValue04561 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04561_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04561 (fullRecordGapValue04561 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04561_not_prime : ¬(recordGapCenter + 171866).Prime := by
  rw [fullRecordGapTerm04561_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04561, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04561_fast_pow_mod_ne_one

def fullRecordGapValue04562 : Nat := fullRecordGapCenterValue + 171998

theorem fullRecordGapTerm04562_eq_value :
    recordGapCenter + 171998 = fullRecordGapValue04562 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04562_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04562 (fullRecordGapValue04562 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04562_not_prime : ¬(recordGapCenter + 171998).Prime := by
  rw [fullRecordGapTerm04562_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04562, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04562_fast_pow_mod_ne_one

def fullRecordGapValue04563 : Nat := fullRecordGapCenterValue + 172032

theorem fullRecordGapTerm04563_eq_value :
    recordGapCenter + 172032 = fullRecordGapValue04563 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04563_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04563 (fullRecordGapValue04563 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04563_not_prime : ¬(recordGapCenter + 172032).Prime := by
  rw [fullRecordGapTerm04563_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04563, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04563_fast_pow_mod_ne_one

def fullRecordGapValue04564 : Nat := fullRecordGapCenterValue + 172226

theorem fullRecordGapTerm04564_eq_value :
    recordGapCenter + 172226 = fullRecordGapValue04564 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04564_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04564 (fullRecordGapValue04564 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04564_not_prime : ¬(recordGapCenter + 172226).Prime := by
  rw [fullRecordGapTerm04564_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04564, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04564_fast_pow_mod_ne_one

def fullRecordGapValue04565 : Nat := fullRecordGapCenterValue + 172358

theorem fullRecordGapTerm04565_eq_value :
    recordGapCenter + 172358 = fullRecordGapValue04565 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04565_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04565 (fullRecordGapValue04565 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04565_not_prime : ¬(recordGapCenter + 172358).Prime := by
  rw [fullRecordGapTerm04565_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04565, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04565_fast_pow_mod_ne_one

def fullRecordGapValue04566 : Nat := fullRecordGapCenterValue + 172532

theorem fullRecordGapTerm04566_eq_value :
    recordGapCenter + 172532 = fullRecordGapValue04566 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04566_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04566 (fullRecordGapValue04566 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04566_not_prime : ¬(recordGapCenter + 172532).Prime := by
  rw [fullRecordGapTerm04566_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04566, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04566_fast_pow_mod_ne_one

def fullRecordGapValue04567 : Nat := fullRecordGapCenterValue + 172538

theorem fullRecordGapTerm04567_eq_value :
    recordGapCenter + 172538 = fullRecordGapValue04567 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04567_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04567 (fullRecordGapValue04567 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04567_not_prime : ¬(recordGapCenter + 172538).Prime := by
  rw [fullRecordGapTerm04567_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04567, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04567_fast_pow_mod_ne_one

def fullRecordGapValue04568 : Nat := fullRecordGapCenterValue + 172622

theorem fullRecordGapTerm04568_eq_value :
    recordGapCenter + 172622 = fullRecordGapValue04568 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04568_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04568 (fullRecordGapValue04568 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04568_not_prime : ¬(recordGapCenter + 172622).Prime := by
  rw [fullRecordGapTerm04568_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04568, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04568_fast_pow_mod_ne_one

def fullRecordGapValue04569 : Nat := fullRecordGapCenterValue + 172646

theorem fullRecordGapTerm04569_eq_value :
    recordGapCenter + 172646 = fullRecordGapValue04569 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04569_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04569 (fullRecordGapValue04569 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04569_not_prime : ¬(recordGapCenter + 172646).Prime := by
  rw [fullRecordGapTerm04569_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04569, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04569_fast_pow_mod_ne_one

def fullRecordGapValue04570 : Nat := fullRecordGapCenterValue + 172826

theorem fullRecordGapTerm04570_eq_value :
    recordGapCenter + 172826 = fullRecordGapValue04570 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04570_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04570 (fullRecordGapValue04570 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04570_not_prime : ¬(recordGapCenter + 172826).Prime := by
  rw [fullRecordGapTerm04570_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04570, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04570_fast_pow_mod_ne_one

def fullRecordGapValue04571 : Nat := fullRecordGapCenterValue + 173078

theorem fullRecordGapTerm04571_eq_value :
    recordGapCenter + 173078 = fullRecordGapValue04571 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04571_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04571 (fullRecordGapValue04571 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04571_not_prime : ¬(recordGapCenter + 173078).Prime := by
  rw [fullRecordGapTerm04571_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04571, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04571_fast_pow_mod_ne_one

def fullRecordGapValue04572 : Nat := fullRecordGapCenterValue + 173198

theorem fullRecordGapTerm04572_eq_value :
    recordGapCenter + 173198 = fullRecordGapValue04572 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04572_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04572 (fullRecordGapValue04572 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04572_not_prime : ¬(recordGapCenter + 173198).Prime := by
  rw [fullRecordGapTerm04572_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04572, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04572_fast_pow_mod_ne_one

def fullRecordGapValue04573 : Nat := fullRecordGapCenterValue + 173486

theorem fullRecordGapTerm04573_eq_value :
    recordGapCenter + 173486 = fullRecordGapValue04573 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04573_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04573 (fullRecordGapValue04573 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04573_not_prime : ¬(recordGapCenter + 173486).Prime := by
  rw [fullRecordGapTerm04573_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04573, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04573_fast_pow_mod_ne_one

def fullRecordGapValue04574 : Nat := fullRecordGapCenterValue + 173702

theorem fullRecordGapTerm04574_eq_value :
    recordGapCenter + 173702 = fullRecordGapValue04574 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04574_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04574 (fullRecordGapValue04574 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04574_not_prime : ¬(recordGapCenter + 173702).Prime := by
  rw [fullRecordGapTerm04574_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04574, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04574_fast_pow_mod_ne_one

def fullRecordGapValue04575 : Nat := fullRecordGapCenterValue + 173738

theorem fullRecordGapTerm04575_eq_value :
    recordGapCenter + 173738 = fullRecordGapValue04575 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04575_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04575 (fullRecordGapValue04575 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04575_not_prime : ¬(recordGapCenter + 173738).Prime := by
  rw [fullRecordGapTerm04575_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04575, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04575_fast_pow_mod_ne_one

def fullRecordGapValue04576 : Nat := fullRecordGapCenterValue + 173918

theorem fullRecordGapTerm04576_eq_value :
    recordGapCenter + 173918 = fullRecordGapValue04576 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04576_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04576 (fullRecordGapValue04576 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04576_not_prime : ¬(recordGapCenter + 173918).Prime := by
  rw [fullRecordGapTerm04576_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04576, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04576_fast_pow_mod_ne_one

def fullRecordGapValue04577 : Nat := fullRecordGapCenterValue + 173948

theorem fullRecordGapTerm04577_eq_value :
    recordGapCenter + 173948 = fullRecordGapValue04577 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04577_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04577 (fullRecordGapValue04577 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04577_not_prime : ¬(recordGapCenter + 173948).Prime := by
  rw [fullRecordGapTerm04577_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04577, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04577_fast_pow_mod_ne_one

def fullRecordGapValue04578 : Nat := fullRecordGapCenterValue + 174206

theorem fullRecordGapTerm04578_eq_value :
    recordGapCenter + 174206 = fullRecordGapValue04578 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04578_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04578 (fullRecordGapValue04578 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04578_not_prime : ¬(recordGapCenter + 174206).Prime := by
  rw [fullRecordGapTerm04578_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04578, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04578_fast_pow_mod_ne_one

def fullRecordGapValue04579 : Nat := fullRecordGapCenterValue + 174240

theorem fullRecordGapTerm04579_eq_value :
    recordGapCenter + 174240 = fullRecordGapValue04579 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04579_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04579 (fullRecordGapValue04579 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04579_not_prime : ¬(recordGapCenter + 174240).Prime := by
  rw [fullRecordGapTerm04579_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04579, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04579_fast_pow_mod_ne_one

def fullRecordGapValue04580 : Nat := fullRecordGapCenterValue + 174422

theorem fullRecordGapTerm04580_eq_value :
    recordGapCenter + 174422 = fullRecordGapValue04580 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04580_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04580 (fullRecordGapValue04580 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04580_not_prime : ¬(recordGapCenter + 174422).Prime := by
  rw [fullRecordGapTerm04580_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04580, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04580_fast_pow_mod_ne_one

def fullRecordGapValue04581 : Nat := fullRecordGapCenterValue + 174806

theorem fullRecordGapTerm04581_eq_value :
    recordGapCenter + 174806 = fullRecordGapValue04581 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04581_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04581 (fullRecordGapValue04581 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04581_not_prime : ¬(recordGapCenter + 174806).Prime := by
  rw [fullRecordGapTerm04581_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04581, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04581_fast_pow_mod_ne_one

def fullRecordGapValue04582 : Nat := fullRecordGapCenterValue + 175046

theorem fullRecordGapTerm04582_eq_value :
    recordGapCenter + 175046 = fullRecordGapValue04582 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04582_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04582 (fullRecordGapValue04582 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04582_not_prime : ¬(recordGapCenter + 175046).Prime := by
  rw [fullRecordGapTerm04582_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04582, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04582_fast_pow_mod_ne_one

def fullRecordGapValue04583 : Nat := fullRecordGapCenterValue + 175166

theorem fullRecordGapTerm04583_eq_value :
    recordGapCenter + 175166 = fullRecordGapValue04583 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04583_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04583 (fullRecordGapValue04583 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04583_not_prime : ¬(recordGapCenter + 175166).Prime := by
  rw [fullRecordGapTerm04583_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04583, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04583_fast_pow_mod_ne_one

def fullRecordGapValue04584 : Nat := fullRecordGapCenterValue + 175178

theorem fullRecordGapTerm04584_eq_value :
    recordGapCenter + 175178 = fullRecordGapValue04584 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04584_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04584 (fullRecordGapValue04584 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04584_not_prime : ¬(recordGapCenter + 175178).Prime := by
  rw [fullRecordGapTerm04584_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04584, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04584_fast_pow_mod_ne_one

def fullRecordGapValue04585 : Nat := fullRecordGapCenterValue + 175298

theorem fullRecordGapTerm04585_eq_value :
    recordGapCenter + 175298 = fullRecordGapValue04585 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04585_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04585 (fullRecordGapValue04585 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04585_not_prime : ¬(recordGapCenter + 175298).Prime := by
  rw [fullRecordGapTerm04585_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04585, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04585_fast_pow_mod_ne_one

def fullRecordGapValue04586 : Nat := fullRecordGapCenterValue + 175586

theorem fullRecordGapTerm04586_eq_value :
    recordGapCenter + 175586 = fullRecordGapValue04586 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04586_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04586 (fullRecordGapValue04586 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04586_not_prime : ¬(recordGapCenter + 175586).Prime := by
  rw [fullRecordGapTerm04586_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04586, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04586_fast_pow_mod_ne_one

def fullRecordGapValue04587 : Nat := fullRecordGapCenterValue + 175616

theorem fullRecordGapTerm04587_eq_value :
    recordGapCenter + 175616 = fullRecordGapValue04587 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04587_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04587 (fullRecordGapValue04587 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04587_not_prime : ¬(recordGapCenter + 175616).Prime := by
  rw [fullRecordGapTerm04587_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04587, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04587_fast_pow_mod_ne_one

def fullRecordGapValue04588 : Nat := fullRecordGapCenterValue + 175862

theorem fullRecordGapTerm04588_eq_value :
    recordGapCenter + 175862 = fullRecordGapValue04588 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04588_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04588 (fullRecordGapValue04588 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04588_not_prime : ¬(recordGapCenter + 175862).Prime := by
  rw [fullRecordGapTerm04588_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04588, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04588_fast_pow_mod_ne_one

def fullRecordGapValue04589 : Nat := fullRecordGapCenterValue + 175892

theorem fullRecordGapTerm04589_eq_value :
    recordGapCenter + 175892 = fullRecordGapValue04589 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04589_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04589 (fullRecordGapValue04589 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04589_not_prime : ¬(recordGapCenter + 175892).Prime := by
  rw [fullRecordGapTerm04589_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04589, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04589_fast_pow_mod_ne_one

def fullRecordGapValue04590 : Nat := fullRecordGapCenterValue + 175988

theorem fullRecordGapTerm04590_eq_value :
    recordGapCenter + 175988 = fullRecordGapValue04590 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04590_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04590 (fullRecordGapValue04590 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04590_not_prime : ¬(recordGapCenter + 175988).Prime := by
  rw [fullRecordGapTerm04590_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04590, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04590_fast_pow_mod_ne_one

def fullRecordGapValue04591 : Nat := fullRecordGapCenterValue + 176186

theorem fullRecordGapTerm04591_eq_value :
    recordGapCenter + 176186 = fullRecordGapValue04591 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04591_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04591 (fullRecordGapValue04591 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04591_not_prime : ¬(recordGapCenter + 176186).Prime := by
  rw [fullRecordGapTerm04591_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04591, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04591_fast_pow_mod_ne_one

def fullRecordGapValue04592 : Nat := fullRecordGapCenterValue + 176642

theorem fullRecordGapTerm04592_eq_value :
    recordGapCenter + 176642 = fullRecordGapValue04592 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04592_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04592 (fullRecordGapValue04592 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04592_not_prime : ¬(recordGapCenter + 176642).Prime := by
  rw [fullRecordGapTerm04592_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04592, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04592_fast_pow_mod_ne_one

def fullRecordGapValue04593 : Nat := fullRecordGapCenterValue + 176846

theorem fullRecordGapTerm04593_eq_value :
    recordGapCenter + 176846 = fullRecordGapValue04593 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04593_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04593 (fullRecordGapValue04593 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04593_not_prime : ¬(recordGapCenter + 176846).Prime := by
  rw [fullRecordGapTerm04593_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04593, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04593_fast_pow_mod_ne_one

def fullRecordGapValue04594 : Nat := fullRecordGapCenterValue + 177026

theorem fullRecordGapTerm04594_eq_value :
    recordGapCenter + 177026 = fullRecordGapValue04594 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04594_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04594 (fullRecordGapValue04594 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04594_not_prime : ¬(recordGapCenter + 177026).Prime := by
  rw [fullRecordGapTerm04594_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04594, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04594_fast_pow_mod_ne_one

def fullRecordGapValue04595 : Nat := fullRecordGapCenterValue + 177116

theorem fullRecordGapTerm04595_eq_value :
    recordGapCenter + 177116 = fullRecordGapValue04595 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04595_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04595 (fullRecordGapValue04595 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04595_not_prime : ¬(recordGapCenter + 177116).Prime := by
  rw [fullRecordGapTerm04595_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04595, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04595_fast_pow_mod_ne_one

def fullRecordGapValue04596 : Nat := fullRecordGapCenterValue + 177482

theorem fullRecordGapTerm04596_eq_value :
    recordGapCenter + 177482 = fullRecordGapValue04596 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04596_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04596 (fullRecordGapValue04596 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04596_not_prime : ¬(recordGapCenter + 177482).Prime := by
  rw [fullRecordGapTerm04596_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04596, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04596_fast_pow_mod_ne_one

def fullRecordGapValue04597 : Nat := fullRecordGapCenterValue + 177746

theorem fullRecordGapTerm04597_eq_value :
    recordGapCenter + 177746 = fullRecordGapValue04597 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04597_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04597 (fullRecordGapValue04597 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04597_not_prime : ¬(recordGapCenter + 177746).Prime := by
  rw [fullRecordGapTerm04597_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04597, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04597_fast_pow_mod_ne_one

def fullRecordGapValue04598 : Nat := fullRecordGapCenterValue + 178082

theorem fullRecordGapTerm04598_eq_value :
    recordGapCenter + 178082 = fullRecordGapValue04598 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04598_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04598 (fullRecordGapValue04598 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04598_not_prime : ¬(recordGapCenter + 178082).Prime := by
  rw [fullRecordGapTerm04598_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04598, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04598_fast_pow_mod_ne_one

def fullRecordGapValue04599 : Nat := fullRecordGapCenterValue + 178202

theorem fullRecordGapTerm04599_eq_value :
    recordGapCenter + 178202 = fullRecordGapValue04599 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04599_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04599 (fullRecordGapValue04599 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04599_not_prime : ¬(recordGapCenter + 178202).Prime := by
  rw [fullRecordGapTerm04599_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04599, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04599_fast_pow_mod_ne_one

def fullRecordGapValue04600 : Nat := fullRecordGapCenterValue + 178628

theorem fullRecordGapTerm04600_eq_value :
    recordGapCenter + 178628 = fullRecordGapValue04600 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04600_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04600 (fullRecordGapValue04600 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04600_not_prime : ¬(recordGapCenter + 178628).Prime := by
  rw [fullRecordGapTerm04600_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04600, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04600_fast_pow_mod_ne_one

def fullRecordGapValue04601 : Nat := fullRecordGapCenterValue + 178742

theorem fullRecordGapTerm04601_eq_value :
    recordGapCenter + 178742 = fullRecordGapValue04601 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04601_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04601 (fullRecordGapValue04601 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04601_not_prime : ¬(recordGapCenter + 178742).Prime := by
  rw [fullRecordGapTerm04601_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04601, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04601_fast_pow_mod_ne_one

def fullRecordGapValue04602 : Nat := fullRecordGapCenterValue + 178796

theorem fullRecordGapTerm04602_eq_value :
    recordGapCenter + 178796 = fullRecordGapValue04602 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04602_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04602 (fullRecordGapValue04602 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04602_not_prime : ¬(recordGapCenter + 178796).Prime := by
  rw [fullRecordGapTerm04602_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04602, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04602_fast_pow_mod_ne_one

def fullRecordGapValue04603 : Nat := fullRecordGapCenterValue + 178826

theorem fullRecordGapTerm04603_eq_value :
    recordGapCenter + 178826 = fullRecordGapValue04603 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04603_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04603 (fullRecordGapValue04603 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04603_not_prime : ¬(recordGapCenter + 178826).Prime := by
  rw [fullRecordGapTerm04603_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04603, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04603_fast_pow_mod_ne_one

def fullRecordGapValue04604 : Nat := fullRecordGapCenterValue + 179042

theorem fullRecordGapTerm04604_eq_value :
    recordGapCenter + 179042 = fullRecordGapValue04604 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04604_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04604 (fullRecordGapValue04604 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04604_not_prime : ¬(recordGapCenter + 179042).Prime := by
  rw [fullRecordGapTerm04604_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04604, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04604_fast_pow_mod_ne_one

def fullRecordGapValue04605 : Nat := fullRecordGapCenterValue + 179198

theorem fullRecordGapTerm04605_eq_value :
    recordGapCenter + 179198 = fullRecordGapValue04605 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04605_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04605 (fullRecordGapValue04605 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04605_not_prime : ¬(recordGapCenter + 179198).Prime := by
  rw [fullRecordGapTerm04605_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04605, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04605_fast_pow_mod_ne_one

def fullRecordGapValue04606 : Nat := fullRecordGapCenterValue + 179306

theorem fullRecordGapTerm04606_eq_value :
    recordGapCenter + 179306 = fullRecordGapValue04606 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04606_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04606 (fullRecordGapValue04606 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04606_not_prime : ¬(recordGapCenter + 179306).Prime := by
  rw [fullRecordGapTerm04606_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04606, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04606_fast_pow_mod_ne_one

def fullRecordGapValue04607 : Nat := fullRecordGapCenterValue + 179342

theorem fullRecordGapTerm04607_eq_value :
    recordGapCenter + 179342 = fullRecordGapValue04607 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04607_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04607 (fullRecordGapValue04607 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04607_not_prime : ¬(recordGapCenter + 179342).Prime := by
  rw [fullRecordGapTerm04607_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04607, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04607_fast_pow_mod_ne_one

def fullRecordGapValue04608 : Nat := fullRecordGapCenterValue + 179378

theorem fullRecordGapTerm04608_eq_value :
    recordGapCenter + 179378 = fullRecordGapValue04608 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04608_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04608 (fullRecordGapValue04608 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04608_not_prime : ¬(recordGapCenter + 179378).Prime := by
  rw [fullRecordGapTerm04608_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04608, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04608_fast_pow_mod_ne_one

end PrimeFactorUnimodality
