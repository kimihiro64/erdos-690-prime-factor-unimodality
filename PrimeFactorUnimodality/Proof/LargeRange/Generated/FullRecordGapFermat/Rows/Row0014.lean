import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue03329 : Nat := fullRecordGapCenterValue - 128218

theorem fullRecordGapTerm03329_eq_value :
    recordGapCenter - 128218 = fullRecordGapValue03329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03329 (fullRecordGapValue03329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03329_not_prime : ¬(recordGapCenter - 128218).Prime := by
  rw [fullRecordGapTerm03329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03329_fast_pow_mod_ne_one

def fullRecordGapValue03330 : Nat := fullRecordGapCenterValue - 128182

theorem fullRecordGapTerm03330_eq_value :
    recordGapCenter - 128182 = fullRecordGapValue03330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03330 (fullRecordGapValue03330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03330_not_prime : ¬(recordGapCenter - 128182).Prime := by
  rw [fullRecordGapTerm03330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03330_fast_pow_mod_ne_one

def fullRecordGapValue03331 : Nat := fullRecordGapCenterValue - 128134

theorem fullRecordGapTerm03331_eq_value :
    recordGapCenter - 128134 = fullRecordGapValue03331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03331 (fullRecordGapValue03331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03331_not_prime : ¬(recordGapCenter - 128134).Prime := by
  rw [fullRecordGapTerm03331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03331_fast_pow_mod_ne_one

def fullRecordGapValue03332 : Nat := fullRecordGapCenterValue - 128074

theorem fullRecordGapTerm03332_eq_value :
    recordGapCenter - 128074 = fullRecordGapValue03332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03332 (fullRecordGapValue03332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03332_not_prime : ¬(recordGapCenter - 128074).Prime := by
  rw [fullRecordGapTerm03332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03332_fast_pow_mod_ne_one

def fullRecordGapValue03333 : Nat := fullRecordGapCenterValue - 127858

theorem fullRecordGapTerm03333_eq_value :
    recordGapCenter - 127858 = fullRecordGapValue03333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03333 (fullRecordGapValue03333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03333_not_prime : ¬(recordGapCenter - 127858).Prime := by
  rw [fullRecordGapTerm03333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03333_fast_pow_mod_ne_one

def fullRecordGapValue03334 : Nat := fullRecordGapCenterValue - 127342

theorem fullRecordGapTerm03334_eq_value :
    recordGapCenter - 127342 = fullRecordGapValue03334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03334 (fullRecordGapValue03334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03334_not_prime : ¬(recordGapCenter - 127342).Prime := by
  rw [fullRecordGapTerm03334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03334_fast_pow_mod_ne_one

def fullRecordGapValue03335 : Nat := fullRecordGapCenterValue - 127294

theorem fullRecordGapTerm03335_eq_value :
    recordGapCenter - 127294 = fullRecordGapValue03335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03335 (fullRecordGapValue03335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03335_not_prime : ¬(recordGapCenter - 127294).Prime := by
  rw [fullRecordGapTerm03335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03335_fast_pow_mod_ne_one

def fullRecordGapValue03336 : Nat := fullRecordGapCenterValue - 127258

theorem fullRecordGapTerm03336_eq_value :
    recordGapCenter - 127258 = fullRecordGapValue03336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03336 (fullRecordGapValue03336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03336_not_prime : ¬(recordGapCenter - 127258).Prime := by
  rw [fullRecordGapTerm03336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03336_fast_pow_mod_ne_one

def fullRecordGapValue03337 : Nat := fullRecordGapCenterValue - 127234

theorem fullRecordGapTerm03337_eq_value :
    recordGapCenter - 127234 = fullRecordGapValue03337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03337 (fullRecordGapValue03337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03337_not_prime : ¬(recordGapCenter - 127234).Prime := by
  rw [fullRecordGapTerm03337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03337_fast_pow_mod_ne_one

def fullRecordGapValue03338 : Nat := fullRecordGapCenterValue - 127174

theorem fullRecordGapTerm03338_eq_value :
    recordGapCenter - 127174 = fullRecordGapValue03338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03338 (fullRecordGapValue03338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03338_not_prime : ¬(recordGapCenter - 127174).Prime := by
  rw [fullRecordGapTerm03338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03338_fast_pow_mod_ne_one

def fullRecordGapValue03339 : Nat := fullRecordGapCenterValue - 127042

theorem fullRecordGapTerm03339_eq_value :
    recordGapCenter - 127042 = fullRecordGapValue03339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03339 (fullRecordGapValue03339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03339_not_prime : ¬(recordGapCenter - 127042).Prime := by
  rw [fullRecordGapTerm03339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03339_fast_pow_mod_ne_one

def fullRecordGapValue03340 : Nat := fullRecordGapCenterValue - 127008

theorem fullRecordGapTerm03340_eq_value :
    recordGapCenter - 127008 = fullRecordGapValue03340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03340 (fullRecordGapValue03340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03340_not_prime : ¬(recordGapCenter - 127008).Prime := by
  rw [fullRecordGapTerm03340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03340_fast_pow_mod_ne_one

def fullRecordGapValue03341 : Nat := fullRecordGapCenterValue - 126838

theorem fullRecordGapTerm03341_eq_value :
    recordGapCenter - 126838 = fullRecordGapValue03341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03341 (fullRecordGapValue03341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03341_not_prime : ¬(recordGapCenter - 126838).Prime := by
  rw [fullRecordGapTerm03341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03341_fast_pow_mod_ne_one

def fullRecordGapValue03342 : Nat := fullRecordGapCenterValue - 126720

theorem fullRecordGapTerm03342_eq_value :
    recordGapCenter - 126720 = fullRecordGapValue03342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03342 (fullRecordGapValue03342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03342_not_prime : ¬(recordGapCenter - 126720).Prime := by
  rw [fullRecordGapTerm03342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03342_fast_pow_mod_ne_one

def fullRecordGapValue03343 : Nat := fullRecordGapCenterValue - 126622

theorem fullRecordGapTerm03343_eq_value :
    recordGapCenter - 126622 = fullRecordGapValue03343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03343 (fullRecordGapValue03343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03343_not_prime : ¬(recordGapCenter - 126622).Prime := by
  rw [fullRecordGapTerm03343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03343_fast_pow_mod_ne_one

def fullRecordGapValue03344 : Nat := fullRecordGapCenterValue - 126598

theorem fullRecordGapTerm03344_eq_value :
    recordGapCenter - 126598 = fullRecordGapValue03344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03344 (fullRecordGapValue03344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03344_not_prime : ¬(recordGapCenter - 126598).Prime := by
  rw [fullRecordGapTerm03344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03344_fast_pow_mod_ne_one

def fullRecordGapValue03345 : Nat := fullRecordGapCenterValue - 126562

theorem fullRecordGapTerm03345_eq_value :
    recordGapCenter - 126562 = fullRecordGapValue03345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03345 (fullRecordGapValue03345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03345_not_prime : ¬(recordGapCenter - 126562).Prime := by
  rw [fullRecordGapTerm03345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03345_fast_pow_mod_ne_one

def fullRecordGapValue03346 : Nat := fullRecordGapCenterValue - 126298

theorem fullRecordGapTerm03346_eq_value :
    recordGapCenter - 126298 = fullRecordGapValue03346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03346 (fullRecordGapValue03346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03346_not_prime : ¬(recordGapCenter - 126298).Prime := by
  rw [fullRecordGapTerm03346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03346_fast_pow_mod_ne_one

def fullRecordGapValue03347 : Nat := fullRecordGapCenterValue - 126118

theorem fullRecordGapTerm03347_eq_value :
    recordGapCenter - 126118 = fullRecordGapValue03347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03347 (fullRecordGapValue03347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03347_not_prime : ¬(recordGapCenter - 126118).Prime := by
  rw [fullRecordGapTerm03347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03347_fast_pow_mod_ne_one

def fullRecordGapValue03348 : Nat := fullRecordGapCenterValue - 125962

theorem fullRecordGapTerm03348_eq_value :
    recordGapCenter - 125962 = fullRecordGapValue03348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03348 (fullRecordGapValue03348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03348_not_prime : ¬(recordGapCenter - 125962).Prime := by
  rw [fullRecordGapTerm03348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03348_fast_pow_mod_ne_one

def fullRecordGapValue03349 : Nat := fullRecordGapCenterValue - 125842

theorem fullRecordGapTerm03349_eq_value :
    recordGapCenter - 125842 = fullRecordGapValue03349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03349 (fullRecordGapValue03349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03349_not_prime : ¬(recordGapCenter - 125842).Prime := by
  rw [fullRecordGapTerm03349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03349_fast_pow_mod_ne_one

def fullRecordGapValue03350 : Nat := fullRecordGapCenterValue - 125722

theorem fullRecordGapTerm03350_eq_value :
    recordGapCenter - 125722 = fullRecordGapValue03350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03350 (fullRecordGapValue03350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03350_not_prime : ¬(recordGapCenter - 125722).Prime := by
  rw [fullRecordGapTerm03350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03350_fast_pow_mod_ne_one

def fullRecordGapValue03351 : Nat := fullRecordGapCenterValue - 125638

theorem fullRecordGapTerm03351_eq_value :
    recordGapCenter - 125638 = fullRecordGapValue03351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03351 (fullRecordGapValue03351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03351_not_prime : ¬(recordGapCenter - 125638).Prime := by
  rw [fullRecordGapTerm03351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03351_fast_pow_mod_ne_one

def fullRecordGapValue03352 : Nat := fullRecordGapCenterValue - 124954

theorem fullRecordGapTerm03352_eq_value :
    recordGapCenter - 124954 = fullRecordGapValue03352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03352 (fullRecordGapValue03352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03352_not_prime : ¬(recordGapCenter - 124954).Prime := by
  rw [fullRecordGapTerm03352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03352_fast_pow_mod_ne_one

def fullRecordGapValue03353 : Nat := fullRecordGapCenterValue - 124702

theorem fullRecordGapTerm03353_eq_value :
    recordGapCenter - 124702 = fullRecordGapValue03353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03353 (fullRecordGapValue03353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03353_not_prime : ¬(recordGapCenter - 124702).Prime := by
  rw [fullRecordGapTerm03353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03353_fast_pow_mod_ne_one

def fullRecordGapValue03354 : Nat := fullRecordGapCenterValue - 124162

theorem fullRecordGapTerm03354_eq_value :
    recordGapCenter - 124162 = fullRecordGapValue03354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03354 (fullRecordGapValue03354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03354_not_prime : ¬(recordGapCenter - 124162).Prime := by
  rw [fullRecordGapTerm03354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03354_fast_pow_mod_ne_one

def fullRecordGapValue03355 : Nat := fullRecordGapCenterValue - 124114

theorem fullRecordGapTerm03355_eq_value :
    recordGapCenter - 124114 = fullRecordGapValue03355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03355 (fullRecordGapValue03355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03355_not_prime : ¬(recordGapCenter - 124114).Prime := by
  rw [fullRecordGapTerm03355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03355_fast_pow_mod_ne_one

def fullRecordGapValue03356 : Nat := fullRecordGapCenterValue - 123982

theorem fullRecordGapTerm03356_eq_value :
    recordGapCenter - 123982 = fullRecordGapValue03356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03356 (fullRecordGapValue03356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03356_not_prime : ¬(recordGapCenter - 123982).Prime := by
  rw [fullRecordGapTerm03356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03356_fast_pow_mod_ne_one

def fullRecordGapValue03357 : Nat := fullRecordGapCenterValue - 123958

theorem fullRecordGapTerm03357_eq_value :
    recordGapCenter - 123958 = fullRecordGapValue03357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03357 (fullRecordGapValue03357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03357_not_prime : ¬(recordGapCenter - 123958).Prime := by
  rw [fullRecordGapTerm03357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03357_fast_pow_mod_ne_one

def fullRecordGapValue03358 : Nat := fullRecordGapCenterValue - 123898

theorem fullRecordGapTerm03358_eq_value :
    recordGapCenter - 123898 = fullRecordGapValue03358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03358 (fullRecordGapValue03358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03358_not_prime : ¬(recordGapCenter - 123898).Prime := by
  rw [fullRecordGapTerm03358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03358_fast_pow_mod_ne_one

def fullRecordGapValue03359 : Nat := fullRecordGapCenterValue - 123562

theorem fullRecordGapTerm03359_eq_value :
    recordGapCenter - 123562 = fullRecordGapValue03359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03359 (fullRecordGapValue03359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03359_not_prime : ¬(recordGapCenter - 123562).Prime := by
  rw [fullRecordGapTerm03359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03359_fast_pow_mod_ne_one

def fullRecordGapValue03360 : Nat := fullRecordGapCenterValue - 123118

theorem fullRecordGapTerm03360_eq_value :
    recordGapCenter - 123118 = fullRecordGapValue03360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03360 (fullRecordGapValue03360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03360_not_prime : ¬(recordGapCenter - 123118).Prime := by
  rw [fullRecordGapTerm03360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03360_fast_pow_mod_ne_one

def fullRecordGapValue03361 : Nat := fullRecordGapCenterValue - 122880

theorem fullRecordGapTerm03361_eq_value :
    recordGapCenter - 122880 = fullRecordGapValue03361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03361 (fullRecordGapValue03361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03361_not_prime : ¬(recordGapCenter - 122880).Prime := by
  rw [fullRecordGapTerm03361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03361_fast_pow_mod_ne_one

def fullRecordGapValue03362 : Nat := fullRecordGapCenterValue - 122818

theorem fullRecordGapTerm03362_eq_value :
    recordGapCenter - 122818 = fullRecordGapValue03362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03362 (fullRecordGapValue03362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03362_not_prime : ¬(recordGapCenter - 122818).Prime := by
  rw [fullRecordGapTerm03362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03362_fast_pow_mod_ne_one

def fullRecordGapValue03363 : Nat := fullRecordGapCenterValue - 121834

theorem fullRecordGapTerm03363_eq_value :
    recordGapCenter - 121834 = fullRecordGapValue03363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03363 (fullRecordGapValue03363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03363_not_prime : ¬(recordGapCenter - 121834).Prime := by
  rw [fullRecordGapTerm03363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03363_fast_pow_mod_ne_one

def fullRecordGapValue03364 : Nat := fullRecordGapCenterValue - 121474

theorem fullRecordGapTerm03364_eq_value :
    recordGapCenter - 121474 = fullRecordGapValue03364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03364 (fullRecordGapValue03364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03364_not_prime : ¬(recordGapCenter - 121474).Prime := by
  rw [fullRecordGapTerm03364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03364_fast_pow_mod_ne_one

def fullRecordGapValue03365 : Nat := fullRecordGapCenterValue - 121438

theorem fullRecordGapTerm03365_eq_value :
    recordGapCenter - 121438 = fullRecordGapValue03365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03365 (fullRecordGapValue03365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03365_not_prime : ¬(recordGapCenter - 121438).Prime := by
  rw [fullRecordGapTerm03365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03365_fast_pow_mod_ne_one

def fullRecordGapValue03366 : Nat := fullRecordGapCenterValue - 121078

theorem fullRecordGapTerm03366_eq_value :
    recordGapCenter - 121078 = fullRecordGapValue03366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03366 (fullRecordGapValue03366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03366_not_prime : ¬(recordGapCenter - 121078).Prime := by
  rw [fullRecordGapTerm03366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03366_fast_pow_mod_ne_one

def fullRecordGapValue03367 : Nat := fullRecordGapCenterValue - 121042

theorem fullRecordGapTerm03367_eq_value :
    recordGapCenter - 121042 = fullRecordGapValue03367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03367 (fullRecordGapValue03367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03367_not_prime : ¬(recordGapCenter - 121042).Prime := by
  rw [fullRecordGapTerm03367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03367_fast_pow_mod_ne_one

def fullRecordGapValue03368 : Nat := fullRecordGapCenterValue - 120994

theorem fullRecordGapTerm03368_eq_value :
    recordGapCenter - 120994 = fullRecordGapValue03368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03368 (fullRecordGapValue03368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03368_not_prime : ¬(recordGapCenter - 120994).Prime := by
  rw [fullRecordGapTerm03368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03368_fast_pow_mod_ne_one

def fullRecordGapValue03369 : Nat := fullRecordGapCenterValue - 120514

theorem fullRecordGapTerm03369_eq_value :
    recordGapCenter - 120514 = fullRecordGapValue03369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03369 (fullRecordGapValue03369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03369_not_prime : ¬(recordGapCenter - 120514).Prime := by
  rw [fullRecordGapTerm03369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03369_fast_pow_mod_ne_one

def fullRecordGapValue03370 : Nat := fullRecordGapCenterValue - 120502

theorem fullRecordGapTerm03370_eq_value :
    recordGapCenter - 120502 = fullRecordGapValue03370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03370 (fullRecordGapValue03370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03370_not_prime : ¬(recordGapCenter - 120502).Prime := by
  rw [fullRecordGapTerm03370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03370_fast_pow_mod_ne_one

def fullRecordGapValue03371 : Nat := fullRecordGapCenterValue - 120214

theorem fullRecordGapTerm03371_eq_value :
    recordGapCenter - 120214 = fullRecordGapValue03371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03371 (fullRecordGapValue03371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03371_not_prime : ¬(recordGapCenter - 120214).Prime := by
  rw [fullRecordGapTerm03371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03371_fast_pow_mod_ne_one

def fullRecordGapValue03372 : Nat := fullRecordGapCenterValue - 120202

theorem fullRecordGapTerm03372_eq_value :
    recordGapCenter - 120202 = fullRecordGapValue03372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03372 (fullRecordGapValue03372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03372_not_prime : ¬(recordGapCenter - 120202).Prime := by
  rw [fullRecordGapTerm03372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03372_fast_pow_mod_ne_one

def fullRecordGapValue03373 : Nat := fullRecordGapCenterValue - 120154

theorem fullRecordGapTerm03373_eq_value :
    recordGapCenter - 120154 = fullRecordGapValue03373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03373 (fullRecordGapValue03373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03373_not_prime : ¬(recordGapCenter - 120154).Prime := by
  rw [fullRecordGapTerm03373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03373_fast_pow_mod_ne_one

def fullRecordGapValue03374 : Nat := fullRecordGapCenterValue - 120034

theorem fullRecordGapTerm03374_eq_value :
    recordGapCenter - 120034 = fullRecordGapValue03374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03374 (fullRecordGapValue03374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03374_not_prime : ¬(recordGapCenter - 120034).Prime := by
  rw [fullRecordGapTerm03374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03374_fast_pow_mod_ne_one

def fullRecordGapValue03375 : Nat := fullRecordGapCenterValue - 119914

theorem fullRecordGapTerm03375_eq_value :
    recordGapCenter - 119914 = fullRecordGapValue03375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03375 (fullRecordGapValue03375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03375_not_prime : ¬(recordGapCenter - 119914).Prime := by
  rw [fullRecordGapTerm03375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03375_fast_pow_mod_ne_one

def fullRecordGapValue03376 : Nat := fullRecordGapCenterValue - 119842

theorem fullRecordGapTerm03376_eq_value :
    recordGapCenter - 119842 = fullRecordGapValue03376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03376 (fullRecordGapValue03376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03376_not_prime : ¬(recordGapCenter - 119842).Prime := by
  rw [fullRecordGapTerm03376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03376_fast_pow_mod_ne_one

def fullRecordGapValue03377 : Nat := fullRecordGapCenterValue - 119758

theorem fullRecordGapTerm03377_eq_value :
    recordGapCenter - 119758 = fullRecordGapValue03377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03377 (fullRecordGapValue03377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03377_not_prime : ¬(recordGapCenter - 119758).Prime := by
  rw [fullRecordGapTerm03377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03377_fast_pow_mod_ne_one

def fullRecordGapValue03378 : Nat := fullRecordGapCenterValue - 119542

theorem fullRecordGapTerm03378_eq_value :
    recordGapCenter - 119542 = fullRecordGapValue03378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03378 (fullRecordGapValue03378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03378_not_prime : ¬(recordGapCenter - 119542).Prime := by
  rw [fullRecordGapTerm03378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03378_fast_pow_mod_ne_one

def fullRecordGapValue03379 : Nat := fullRecordGapCenterValue - 119338

theorem fullRecordGapTerm03379_eq_value :
    recordGapCenter - 119338 = fullRecordGapValue03379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03379 (fullRecordGapValue03379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03379_not_prime : ¬(recordGapCenter - 119338).Prime := by
  rw [fullRecordGapTerm03379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03379_fast_pow_mod_ne_one

def fullRecordGapValue03380 : Nat := fullRecordGapCenterValue - 119254

theorem fullRecordGapTerm03380_eq_value :
    recordGapCenter - 119254 = fullRecordGapValue03380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03380 (fullRecordGapValue03380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03380_not_prime : ¬(recordGapCenter - 119254).Prime := by
  rw [fullRecordGapTerm03380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03380_fast_pow_mod_ne_one

def fullRecordGapValue03381 : Nat := fullRecordGapCenterValue - 118942

theorem fullRecordGapTerm03381_eq_value :
    recordGapCenter - 118942 = fullRecordGapValue03381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03381 (fullRecordGapValue03381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03381_not_prime : ¬(recordGapCenter - 118942).Prime := by
  rw [fullRecordGapTerm03381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03381_fast_pow_mod_ne_one

def fullRecordGapValue03382 : Nat := fullRecordGapCenterValue - 118834

theorem fullRecordGapTerm03382_eq_value :
    recordGapCenter - 118834 = fullRecordGapValue03382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03382 (fullRecordGapValue03382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03382_not_prime : ¬(recordGapCenter - 118834).Prime := by
  rw [fullRecordGapTerm03382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03382_fast_pow_mod_ne_one

def fullRecordGapValue03383 : Nat := fullRecordGapCenterValue - 118800

theorem fullRecordGapTerm03383_eq_value :
    recordGapCenter - 118800 = fullRecordGapValue03383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03383 (fullRecordGapValue03383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03383_not_prime : ¬(recordGapCenter - 118800).Prime := by
  rw [fullRecordGapTerm03383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03383_fast_pow_mod_ne_one

def fullRecordGapValue03384 : Nat := fullRecordGapCenterValue - 118438

theorem fullRecordGapTerm03384_eq_value :
    recordGapCenter - 118438 = fullRecordGapValue03384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03384 (fullRecordGapValue03384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03384_not_prime : ¬(recordGapCenter - 118438).Prime := by
  rw [fullRecordGapTerm03384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03384_fast_pow_mod_ne_one

def fullRecordGapValue03385 : Nat := fullRecordGapCenterValue - 118414

theorem fullRecordGapTerm03385_eq_value :
    recordGapCenter - 118414 = fullRecordGapValue03385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03385 (fullRecordGapValue03385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03385_not_prime : ¬(recordGapCenter - 118414).Prime := by
  rw [fullRecordGapTerm03385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03385_fast_pow_mod_ne_one

def fullRecordGapValue03386 : Nat := fullRecordGapCenterValue - 118272

theorem fullRecordGapTerm03386_eq_value :
    recordGapCenter - 118272 = fullRecordGapValue03386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03386 (fullRecordGapValue03386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03386_not_prime : ¬(recordGapCenter - 118272).Prime := by
  rw [fullRecordGapTerm03386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03386_fast_pow_mod_ne_one

def fullRecordGapValue03387 : Nat := fullRecordGapCenterValue - 118138

theorem fullRecordGapTerm03387_eq_value :
    recordGapCenter - 118138 = fullRecordGapValue03387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03387 (fullRecordGapValue03387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03387_not_prime : ¬(recordGapCenter - 118138).Prime := by
  rw [fullRecordGapTerm03387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03387_fast_pow_mod_ne_one

def fullRecordGapValue03388 : Nat := fullRecordGapCenterValue - 118018

theorem fullRecordGapTerm03388_eq_value :
    recordGapCenter - 118018 = fullRecordGapValue03388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03388 (fullRecordGapValue03388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03388_not_prime : ¬(recordGapCenter - 118018).Prime := by
  rw [fullRecordGapTerm03388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03388_fast_pow_mod_ne_one

def fullRecordGapValue03389 : Nat := fullRecordGapCenterValue - 117934

theorem fullRecordGapTerm03389_eq_value :
    recordGapCenter - 117934 = fullRecordGapValue03389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03389 (fullRecordGapValue03389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03389_not_prime : ¬(recordGapCenter - 117934).Prime := by
  rw [fullRecordGapTerm03389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03389_fast_pow_mod_ne_one

def fullRecordGapValue03390 : Nat := fullRecordGapCenterValue - 117802

theorem fullRecordGapTerm03390_eq_value :
    recordGapCenter - 117802 = fullRecordGapValue03390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03390 (fullRecordGapValue03390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03390_not_prime : ¬(recordGapCenter - 117802).Prime := by
  rw [fullRecordGapTerm03390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03390_fast_pow_mod_ne_one

def fullRecordGapValue03391 : Nat := fullRecordGapCenterValue - 117778

theorem fullRecordGapTerm03391_eq_value :
    recordGapCenter - 117778 = fullRecordGapValue03391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03391 (fullRecordGapValue03391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03391_not_prime : ¬(recordGapCenter - 117778).Prime := by
  rw [fullRecordGapTerm03391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03391_fast_pow_mod_ne_one

def fullRecordGapValue03392 : Nat := fullRecordGapCenterValue - 117514

theorem fullRecordGapTerm03392_eq_value :
    recordGapCenter - 117514 = fullRecordGapValue03392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03392 (fullRecordGapValue03392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03392_not_prime : ¬(recordGapCenter - 117514).Prime := by
  rw [fullRecordGapTerm03392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03392_fast_pow_mod_ne_one

def fullRecordGapValue03393 : Nat := fullRecordGapCenterValue - 117358

theorem fullRecordGapTerm03393_eq_value :
    recordGapCenter - 117358 = fullRecordGapValue03393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03393 (fullRecordGapValue03393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03393_not_prime : ¬(recordGapCenter - 117358).Prime := by
  rw [fullRecordGapTerm03393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03393_fast_pow_mod_ne_one

def fullRecordGapValue03394 : Nat := fullRecordGapCenterValue - 116962

theorem fullRecordGapTerm03394_eq_value :
    recordGapCenter - 116962 = fullRecordGapValue03394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03394 (fullRecordGapValue03394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03394_not_prime : ¬(recordGapCenter - 116962).Prime := by
  rw [fullRecordGapTerm03394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03394_fast_pow_mod_ne_one

def fullRecordGapValue03395 : Nat := fullRecordGapCenterValue - 116902

theorem fullRecordGapTerm03395_eq_value :
    recordGapCenter - 116902 = fullRecordGapValue03395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03395 (fullRecordGapValue03395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03395_not_prime : ¬(recordGapCenter - 116902).Prime := by
  rw [fullRecordGapTerm03395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03395_fast_pow_mod_ne_one

def fullRecordGapValue03396 : Nat := fullRecordGapCenterValue - 116878

theorem fullRecordGapTerm03396_eq_value :
    recordGapCenter - 116878 = fullRecordGapValue03396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03396 (fullRecordGapValue03396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03396_not_prime : ¬(recordGapCenter - 116878).Prime := by
  rw [fullRecordGapTerm03396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03396_fast_pow_mod_ne_one

def fullRecordGapValue03397 : Nat := fullRecordGapCenterValue - 116458

theorem fullRecordGapTerm03397_eq_value :
    recordGapCenter - 116458 = fullRecordGapValue03397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03397 (fullRecordGapValue03397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03397_not_prime : ¬(recordGapCenter - 116458).Prime := by
  rw [fullRecordGapTerm03397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03397_fast_pow_mod_ne_one

def fullRecordGapValue03398 : Nat := fullRecordGapCenterValue - 116424

theorem fullRecordGapTerm03398_eq_value :
    recordGapCenter - 116424 = fullRecordGapValue03398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03398 (fullRecordGapValue03398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03398_not_prime : ¬(recordGapCenter - 116424).Prime := by
  rw [fullRecordGapTerm03398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03398_fast_pow_mod_ne_one

def fullRecordGapValue03399 : Nat := fullRecordGapCenterValue - 116422

theorem fullRecordGapTerm03399_eq_value :
    recordGapCenter - 116422 = fullRecordGapValue03399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03399 (fullRecordGapValue03399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03399_not_prime : ¬(recordGapCenter - 116422).Prime := by
  rw [fullRecordGapTerm03399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03399_fast_pow_mod_ne_one

def fullRecordGapValue03400 : Nat := fullRecordGapCenterValue - 116134

theorem fullRecordGapTerm03400_eq_value :
    recordGapCenter - 116134 = fullRecordGapValue03400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03400 (fullRecordGapValue03400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03400_not_prime : ¬(recordGapCenter - 116134).Prime := by
  rw [fullRecordGapTerm03400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03400_fast_pow_mod_ne_one

def fullRecordGapValue03401 : Nat := fullRecordGapCenterValue - 115762

theorem fullRecordGapTerm03401_eq_value :
    recordGapCenter - 115762 = fullRecordGapValue03401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03401 (fullRecordGapValue03401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03401_not_prime : ¬(recordGapCenter - 115762).Prime := by
  rw [fullRecordGapTerm03401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03401_fast_pow_mod_ne_one

def fullRecordGapValue03402 : Nat := fullRecordGapCenterValue - 115500

theorem fullRecordGapTerm03402_eq_value :
    recordGapCenter - 115500 = fullRecordGapValue03402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03402 (fullRecordGapValue03402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03402_not_prime : ¬(recordGapCenter - 115500).Prime := by
  rw [fullRecordGapTerm03402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03402_fast_pow_mod_ne_one

def fullRecordGapValue03403 : Nat := fullRecordGapCenterValue - 115114

theorem fullRecordGapTerm03403_eq_value :
    recordGapCenter - 115114 = fullRecordGapValue03403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03403 (fullRecordGapValue03403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03403_not_prime : ¬(recordGapCenter - 115114).Prime := by
  rw [fullRecordGapTerm03403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03403_fast_pow_mod_ne_one

def fullRecordGapValue03404 : Nat := fullRecordGapCenterValue - 115054

theorem fullRecordGapTerm03404_eq_value :
    recordGapCenter - 115054 = fullRecordGapValue03404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03404 (fullRecordGapValue03404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03404_not_prime : ¬(recordGapCenter - 115054).Prime := by
  rw [fullRecordGapTerm03404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03404_fast_pow_mod_ne_one

def fullRecordGapValue03405 : Nat := fullRecordGapCenterValue - 114694

theorem fullRecordGapTerm03405_eq_value :
    recordGapCenter - 114694 = fullRecordGapValue03405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03405 (fullRecordGapValue03405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03405_not_prime : ¬(recordGapCenter - 114694).Prime := by
  rw [fullRecordGapTerm03405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03405_fast_pow_mod_ne_one

def fullRecordGapValue03406 : Nat := fullRecordGapCenterValue - 114658

theorem fullRecordGapTerm03406_eq_value :
    recordGapCenter - 114658 = fullRecordGapValue03406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03406 (fullRecordGapValue03406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03406_not_prime : ¬(recordGapCenter - 114658).Prime := by
  rw [fullRecordGapTerm03406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03406_fast_pow_mod_ne_one

def fullRecordGapValue03407 : Nat := fullRecordGapCenterValue - 114502

theorem fullRecordGapTerm03407_eq_value :
    recordGapCenter - 114502 = fullRecordGapValue03407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03407 (fullRecordGapValue03407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03407_not_prime : ¬(recordGapCenter - 114502).Prime := by
  rw [fullRecordGapTerm03407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03407_fast_pow_mod_ne_one

def fullRecordGapValue03408 : Nat := fullRecordGapCenterValue - 114442

theorem fullRecordGapTerm03408_eq_value :
    recordGapCenter - 114442 = fullRecordGapValue03408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03408 (fullRecordGapValue03408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03408_not_prime : ¬(recordGapCenter - 114442).Prime := by
  rw [fullRecordGapTerm03408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03408_fast_pow_mod_ne_one

def fullRecordGapValue03409 : Nat := fullRecordGapCenterValue - 114298

theorem fullRecordGapTerm03409_eq_value :
    recordGapCenter - 114298 = fullRecordGapValue03409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03409 (fullRecordGapValue03409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03409_not_prime : ¬(recordGapCenter - 114298).Prime := by
  rw [fullRecordGapTerm03409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03409_fast_pow_mod_ne_one

def fullRecordGapValue03410 : Nat := fullRecordGapCenterValue - 113914

theorem fullRecordGapTerm03410_eq_value :
    recordGapCenter - 113914 = fullRecordGapValue03410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03410 (fullRecordGapValue03410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03410_not_prime : ¬(recordGapCenter - 113914).Prime := by
  rw [fullRecordGapTerm03410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03410_fast_pow_mod_ne_one

def fullRecordGapValue03411 : Nat := fullRecordGapCenterValue - 113902

theorem fullRecordGapTerm03411_eq_value :
    recordGapCenter - 113902 = fullRecordGapValue03411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03411 (fullRecordGapValue03411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03411_not_prime : ¬(recordGapCenter - 113902).Prime := by
  rw [fullRecordGapTerm03411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03411_fast_pow_mod_ne_one

def fullRecordGapValue03412 : Nat := fullRecordGapCenterValue - 113794

theorem fullRecordGapTerm03412_eq_value :
    recordGapCenter - 113794 = fullRecordGapValue03412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03412 (fullRecordGapValue03412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03412_not_prime : ¬(recordGapCenter - 113794).Prime := by
  rw [fullRecordGapTerm03412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03412_fast_pow_mod_ne_one

def fullRecordGapValue03413 : Nat := fullRecordGapCenterValue - 113494

theorem fullRecordGapTerm03413_eq_value :
    recordGapCenter - 113494 = fullRecordGapValue03413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03413 (fullRecordGapValue03413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03413_not_prime : ¬(recordGapCenter - 113494).Prime := by
  rw [fullRecordGapTerm03413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03413_fast_pow_mod_ne_one

def fullRecordGapValue03414 : Nat := fullRecordGapCenterValue - 113362

theorem fullRecordGapTerm03414_eq_value :
    recordGapCenter - 113362 = fullRecordGapValue03414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03414 (fullRecordGapValue03414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03414_not_prime : ¬(recordGapCenter - 113362).Prime := by
  rw [fullRecordGapTerm03414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03414_fast_pow_mod_ne_one

def fullRecordGapValue03415 : Nat := fullRecordGapCenterValue - 113038

theorem fullRecordGapTerm03415_eq_value :
    recordGapCenter - 113038 = fullRecordGapValue03415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03415 (fullRecordGapValue03415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03415_not_prime : ¬(recordGapCenter - 113038).Prime := by
  rw [fullRecordGapTerm03415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03415_fast_pow_mod_ne_one

def fullRecordGapValue03416 : Nat := fullRecordGapCenterValue - 112954

theorem fullRecordGapTerm03416_eq_value :
    recordGapCenter - 112954 = fullRecordGapValue03416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03416 (fullRecordGapValue03416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03416_not_prime : ¬(recordGapCenter - 112954).Prime := by
  rw [fullRecordGapTerm03416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03416_fast_pow_mod_ne_one

def fullRecordGapValue03417 : Nat := fullRecordGapCenterValue - 112738

theorem fullRecordGapTerm03417_eq_value :
    recordGapCenter - 112738 = fullRecordGapValue03417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03417 (fullRecordGapValue03417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03417_not_prime : ¬(recordGapCenter - 112738).Prime := by
  rw [fullRecordGapTerm03417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03417_fast_pow_mod_ne_one

def fullRecordGapValue03418 : Nat := fullRecordGapCenterValue - 112500

theorem fullRecordGapTerm03418_eq_value :
    recordGapCenter - 112500 = fullRecordGapValue03418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03418 (fullRecordGapValue03418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03418_not_prime : ¬(recordGapCenter - 112500).Prime := by
  rw [fullRecordGapTerm03418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03418_fast_pow_mod_ne_one

def fullRecordGapValue03419 : Nat := fullRecordGapCenterValue - 112474

theorem fullRecordGapTerm03419_eq_value :
    recordGapCenter - 112474 = fullRecordGapValue03419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03419 (fullRecordGapValue03419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03419_not_prime : ¬(recordGapCenter - 112474).Prime := by
  rw [fullRecordGapTerm03419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03419_fast_pow_mod_ne_one

def fullRecordGapValue03420 : Nat := fullRecordGapCenterValue - 112198

theorem fullRecordGapTerm03420_eq_value :
    recordGapCenter - 112198 = fullRecordGapValue03420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03420 (fullRecordGapValue03420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03420_not_prime : ¬(recordGapCenter - 112198).Prime := by
  rw [fullRecordGapTerm03420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03420_fast_pow_mod_ne_one

def fullRecordGapValue03421 : Nat := fullRecordGapCenterValue - 112018

theorem fullRecordGapTerm03421_eq_value :
    recordGapCenter - 112018 = fullRecordGapValue03421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03421 (fullRecordGapValue03421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03421_not_prime : ¬(recordGapCenter - 112018).Prime := by
  rw [fullRecordGapTerm03421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03421_fast_pow_mod_ne_one

def fullRecordGapValue03422 : Nat := fullRecordGapCenterValue - 112000

theorem fullRecordGapTerm03422_eq_value :
    recordGapCenter - 112000 = fullRecordGapValue03422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03422 (fullRecordGapValue03422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03422_not_prime : ¬(recordGapCenter - 112000).Prime := by
  rw [fullRecordGapTerm03422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03422_fast_pow_mod_ne_one

def fullRecordGapValue03423 : Nat := fullRecordGapCenterValue - 111934

theorem fullRecordGapTerm03423_eq_value :
    recordGapCenter - 111934 = fullRecordGapValue03423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03423 (fullRecordGapValue03423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03423_not_prime : ¬(recordGapCenter - 111934).Prime := by
  rw [fullRecordGapTerm03423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03423_fast_pow_mod_ne_one

def fullRecordGapValue03424 : Nat := fullRecordGapCenterValue - 111804

theorem fullRecordGapTerm03424_eq_value :
    recordGapCenter - 111804 = fullRecordGapValue03424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03424 (fullRecordGapValue03424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03424_not_prime : ¬(recordGapCenter - 111804).Prime := by
  rw [fullRecordGapTerm03424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03424_fast_pow_mod_ne_one

def fullRecordGapValue03425 : Nat := fullRecordGapCenterValue - 111802

theorem fullRecordGapTerm03425_eq_value :
    recordGapCenter - 111802 = fullRecordGapValue03425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03425 (fullRecordGapValue03425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03425_not_prime : ¬(recordGapCenter - 111802).Prime := by
  rw [fullRecordGapTerm03425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03425_fast_pow_mod_ne_one

def fullRecordGapValue03426 : Nat := fullRecordGapCenterValue - 111634

theorem fullRecordGapTerm03426_eq_value :
    recordGapCenter - 111634 = fullRecordGapValue03426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03426 (fullRecordGapValue03426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03426_not_prime : ¬(recordGapCenter - 111634).Prime := by
  rw [fullRecordGapTerm03426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03426_fast_pow_mod_ne_one

def fullRecordGapValue03427 : Nat := fullRecordGapCenterValue - 111394

theorem fullRecordGapTerm03427_eq_value :
    recordGapCenter - 111394 = fullRecordGapValue03427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03427 (fullRecordGapValue03427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03427_not_prime : ¬(recordGapCenter - 111394).Prime := by
  rw [fullRecordGapTerm03427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03427_fast_pow_mod_ne_one

def fullRecordGapValue03428 : Nat := fullRecordGapCenterValue - 111382

theorem fullRecordGapTerm03428_eq_value :
    recordGapCenter - 111382 = fullRecordGapValue03428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03428 (fullRecordGapValue03428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03428_not_prime : ¬(recordGapCenter - 111382).Prime := by
  rw [fullRecordGapTerm03428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03428_fast_pow_mod_ne_one

def fullRecordGapValue03429 : Nat := fullRecordGapCenterValue - 111334

theorem fullRecordGapTerm03429_eq_value :
    recordGapCenter - 111334 = fullRecordGapValue03429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03429 (fullRecordGapValue03429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03429_not_prime : ¬(recordGapCenter - 111334).Prime := by
  rw [fullRecordGapTerm03429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03429_fast_pow_mod_ne_one

def fullRecordGapValue03430 : Nat := fullRecordGapCenterValue - 111132

theorem fullRecordGapTerm03430_eq_value :
    recordGapCenter - 111132 = fullRecordGapValue03430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03430 (fullRecordGapValue03430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03430_not_prime : ¬(recordGapCenter - 111132).Prime := by
  rw [fullRecordGapTerm03430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03430_fast_pow_mod_ne_one

def fullRecordGapValue03431 : Nat := fullRecordGapCenterValue - 111022

theorem fullRecordGapTerm03431_eq_value :
    recordGapCenter - 111022 = fullRecordGapValue03431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03431 (fullRecordGapValue03431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03431_not_prime : ¬(recordGapCenter - 111022).Prime := by
  rw [fullRecordGapTerm03431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03431_fast_pow_mod_ne_one

def fullRecordGapValue03432 : Nat := fullRecordGapCenterValue - 110914

theorem fullRecordGapTerm03432_eq_value :
    recordGapCenter - 110914 = fullRecordGapValue03432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03432 (fullRecordGapValue03432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03432_not_prime : ¬(recordGapCenter - 110914).Prime := by
  rw [fullRecordGapTerm03432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03432_fast_pow_mod_ne_one

def fullRecordGapValue03433 : Nat := fullRecordGapCenterValue - 110674

theorem fullRecordGapTerm03433_eq_value :
    recordGapCenter - 110674 = fullRecordGapValue03433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03433 (fullRecordGapValue03433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03433_not_prime : ¬(recordGapCenter - 110674).Prime := by
  rw [fullRecordGapTerm03433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03433_fast_pow_mod_ne_one

def fullRecordGapValue03434 : Nat := fullRecordGapCenterValue - 110592

theorem fullRecordGapTerm03434_eq_value :
    recordGapCenter - 110592 = fullRecordGapValue03434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03434 (fullRecordGapValue03434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03434_not_prime : ¬(recordGapCenter - 110592).Prime := by
  rw [fullRecordGapTerm03434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03434_fast_pow_mod_ne_one

def fullRecordGapValue03435 : Nat := fullRecordGapCenterValue - 110458

theorem fullRecordGapTerm03435_eq_value :
    recordGapCenter - 110458 = fullRecordGapValue03435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03435 (fullRecordGapValue03435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03435_not_prime : ¬(recordGapCenter - 110458).Prime := by
  rw [fullRecordGapTerm03435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03435_fast_pow_mod_ne_one

def fullRecordGapValue03436 : Nat := fullRecordGapCenterValue - 110434

theorem fullRecordGapTerm03436_eq_value :
    recordGapCenter - 110434 = fullRecordGapValue03436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03436 (fullRecordGapValue03436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03436_not_prime : ¬(recordGapCenter - 110434).Prime := by
  rw [fullRecordGapTerm03436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03436_fast_pow_mod_ne_one

def fullRecordGapValue03437 : Nat := fullRecordGapCenterValue - 110250

theorem fullRecordGapTerm03437_eq_value :
    recordGapCenter - 110250 = fullRecordGapValue03437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03437 (fullRecordGapValue03437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03437_not_prime : ¬(recordGapCenter - 110250).Prime := by
  rw [fullRecordGapTerm03437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03437_fast_pow_mod_ne_one

def fullRecordGapValue03438 : Nat := fullRecordGapCenterValue - 108898

theorem fullRecordGapTerm03438_eq_value :
    recordGapCenter - 108898 = fullRecordGapValue03438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03438 (fullRecordGapValue03438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03438_not_prime : ¬(recordGapCenter - 108898).Prime := by
  rw [fullRecordGapTerm03438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03438_fast_pow_mod_ne_one

def fullRecordGapValue03439 : Nat := fullRecordGapCenterValue - 108874

theorem fullRecordGapTerm03439_eq_value :
    recordGapCenter - 108874 = fullRecordGapValue03439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03439 (fullRecordGapValue03439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03439_not_prime : ¬(recordGapCenter - 108874).Prime := by
  rw [fullRecordGapTerm03439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03439_fast_pow_mod_ne_one

def fullRecordGapValue03440 : Nat := fullRecordGapCenterValue - 108694

theorem fullRecordGapTerm03440_eq_value :
    recordGapCenter - 108694 = fullRecordGapValue03440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03440 (fullRecordGapValue03440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03440_not_prime : ¬(recordGapCenter - 108694).Prime := by
  rw [fullRecordGapTerm03440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03440_fast_pow_mod_ne_one

def fullRecordGapValue03441 : Nat := fullRecordGapCenterValue - 108502

theorem fullRecordGapTerm03441_eq_value :
    recordGapCenter - 108502 = fullRecordGapValue03441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03441 (fullRecordGapValue03441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03441_not_prime : ¬(recordGapCenter - 108502).Prime := by
  rw [fullRecordGapTerm03441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03441_fast_pow_mod_ne_one

def fullRecordGapValue03442 : Nat := fullRecordGapCenterValue - 107974

theorem fullRecordGapTerm03442_eq_value :
    recordGapCenter - 107974 = fullRecordGapValue03442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03442 (fullRecordGapValue03442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03442_not_prime : ¬(recordGapCenter - 107974).Prime := by
  rw [fullRecordGapTerm03442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03442_fast_pow_mod_ne_one

def fullRecordGapValue03443 : Nat := fullRecordGapCenterValue - 107902

theorem fullRecordGapTerm03443_eq_value :
    recordGapCenter - 107902 = fullRecordGapValue03443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03443 (fullRecordGapValue03443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03443_not_prime : ¬(recordGapCenter - 107902).Prime := by
  rw [fullRecordGapTerm03443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03443_fast_pow_mod_ne_one

def fullRecordGapValue03444 : Nat := fullRecordGapCenterValue - 107854

theorem fullRecordGapTerm03444_eq_value :
    recordGapCenter - 107854 = fullRecordGapValue03444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03444 (fullRecordGapValue03444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03444_not_prime : ¬(recordGapCenter - 107854).Prime := by
  rw [fullRecordGapTerm03444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03444_fast_pow_mod_ne_one

def fullRecordGapValue03445 : Nat := fullRecordGapCenterValue - 107800

theorem fullRecordGapTerm03445_eq_value :
    recordGapCenter - 107800 = fullRecordGapValue03445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03445 (fullRecordGapValue03445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03445_not_prime : ¬(recordGapCenter - 107800).Prime := by
  rw [fullRecordGapTerm03445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03445_fast_pow_mod_ne_one

def fullRecordGapValue03446 : Nat := fullRecordGapCenterValue - 107698

theorem fullRecordGapTerm03446_eq_value :
    recordGapCenter - 107698 = fullRecordGapValue03446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03446 (fullRecordGapValue03446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03446_not_prime : ¬(recordGapCenter - 107698).Prime := by
  rw [fullRecordGapTerm03446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03446_fast_pow_mod_ne_one

def fullRecordGapValue03447 : Nat := fullRecordGapCenterValue - 107662

theorem fullRecordGapTerm03447_eq_value :
    recordGapCenter - 107662 = fullRecordGapValue03447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03447 (fullRecordGapValue03447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03447_not_prime : ¬(recordGapCenter - 107662).Prime := by
  rw [fullRecordGapTerm03447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03447_fast_pow_mod_ne_one

def fullRecordGapValue03448 : Nat := fullRecordGapCenterValue - 107314

theorem fullRecordGapTerm03448_eq_value :
    recordGapCenter - 107314 = fullRecordGapValue03448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03448 (fullRecordGapValue03448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03448_not_prime : ¬(recordGapCenter - 107314).Prime := by
  rw [fullRecordGapTerm03448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03448_fast_pow_mod_ne_one

def fullRecordGapValue03449 : Nat := fullRecordGapCenterValue - 107278

theorem fullRecordGapTerm03449_eq_value :
    recordGapCenter - 107278 = fullRecordGapValue03449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03449 (fullRecordGapValue03449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03449_not_prime : ¬(recordGapCenter - 107278).Prime := by
  rw [fullRecordGapTerm03449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03449_fast_pow_mod_ne_one

def fullRecordGapValue03450 : Nat := fullRecordGapCenterValue - 107218

theorem fullRecordGapTerm03450_eq_value :
    recordGapCenter - 107218 = fullRecordGapValue03450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03450 (fullRecordGapValue03450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03450_not_prime : ¬(recordGapCenter - 107218).Prime := by
  rw [fullRecordGapTerm03450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03450_fast_pow_mod_ne_one

def fullRecordGapValue03451 : Nat := fullRecordGapCenterValue - 107194

theorem fullRecordGapTerm03451_eq_value :
    recordGapCenter - 107194 = fullRecordGapValue03451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03451 (fullRecordGapValue03451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03451_not_prime : ¬(recordGapCenter - 107194).Prime := by
  rw [fullRecordGapTerm03451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03451_fast_pow_mod_ne_one

def fullRecordGapValue03452 : Nat := fullRecordGapCenterValue - 107014

theorem fullRecordGapTerm03452_eq_value :
    recordGapCenter - 107014 = fullRecordGapValue03452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03452 (fullRecordGapValue03452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03452_not_prime : ¬(recordGapCenter - 107014).Prime := by
  rw [fullRecordGapTerm03452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03452_fast_pow_mod_ne_one

def fullRecordGapValue03453 : Nat := fullRecordGapCenterValue - 106722

theorem fullRecordGapTerm03453_eq_value :
    recordGapCenter - 106722 = fullRecordGapValue03453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03453 (fullRecordGapValue03453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03453_not_prime : ¬(recordGapCenter - 106722).Prime := by
  rw [fullRecordGapTerm03453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03453_fast_pow_mod_ne_one

def fullRecordGapValue03454 : Nat := fullRecordGapCenterValue - 106654

theorem fullRecordGapTerm03454_eq_value :
    recordGapCenter - 106654 = fullRecordGapValue03454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03454 (fullRecordGapValue03454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03454_not_prime : ¬(recordGapCenter - 106654).Prime := by
  rw [fullRecordGapTerm03454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03454_fast_pow_mod_ne_one

def fullRecordGapValue03455 : Nat := fullRecordGapCenterValue - 106402

theorem fullRecordGapTerm03455_eq_value :
    recordGapCenter - 106402 = fullRecordGapValue03455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03455 (fullRecordGapValue03455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03455_not_prime : ¬(recordGapCenter - 106402).Prime := by
  rw [fullRecordGapTerm03455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03455_fast_pow_mod_ne_one

def fullRecordGapValue03456 : Nat := fullRecordGapCenterValue - 106342

theorem fullRecordGapTerm03456_eq_value :
    recordGapCenter - 106342 = fullRecordGapValue03456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03456 (fullRecordGapValue03456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03456_not_prime : ¬(recordGapCenter - 106342).Prime := by
  rw [fullRecordGapTerm03456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03456_fast_pow_mod_ne_one

def fullRecordGapValue03457 : Nat := fullRecordGapCenterValue - 106294

theorem fullRecordGapTerm03457_eq_value :
    recordGapCenter - 106294 = fullRecordGapValue03457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03457 (fullRecordGapValue03457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03457_not_prime : ¬(recordGapCenter - 106294).Prime := by
  rw [fullRecordGapTerm03457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03457_fast_pow_mod_ne_one

def fullRecordGapValue03458 : Nat := fullRecordGapCenterValue - 106258

theorem fullRecordGapTerm03458_eq_value :
    recordGapCenter - 106258 = fullRecordGapValue03458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03458 (fullRecordGapValue03458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03458_not_prime : ¬(recordGapCenter - 106258).Prime := by
  rw [fullRecordGapTerm03458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03458_fast_pow_mod_ne_one

def fullRecordGapValue03459 : Nat := fullRecordGapCenterValue - 106234

theorem fullRecordGapTerm03459_eq_value :
    recordGapCenter - 106234 = fullRecordGapValue03459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03459 (fullRecordGapValue03459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03459_not_prime : ¬(recordGapCenter - 106234).Prime := by
  rw [fullRecordGapTerm03459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03459_fast_pow_mod_ne_one

def fullRecordGapValue03460 : Nat := fullRecordGapCenterValue - 106174

theorem fullRecordGapTerm03460_eq_value :
    recordGapCenter - 106174 = fullRecordGapValue03460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03460 (fullRecordGapValue03460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03460_not_prime : ¬(recordGapCenter - 106174).Prime := by
  rw [fullRecordGapTerm03460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03460_fast_pow_mod_ne_one

def fullRecordGapValue03461 : Nat := fullRecordGapCenterValue - 106102

theorem fullRecordGapTerm03461_eq_value :
    recordGapCenter - 106102 = fullRecordGapValue03461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03461 (fullRecordGapValue03461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03461_not_prime : ¬(recordGapCenter - 106102).Prime := by
  rw [fullRecordGapTerm03461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03461_fast_pow_mod_ne_one

def fullRecordGapValue03462 : Nat := fullRecordGapCenterValue - 105838

theorem fullRecordGapTerm03462_eq_value :
    recordGapCenter - 105838 = fullRecordGapValue03462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03462 (fullRecordGapValue03462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03462_not_prime : ¬(recordGapCenter - 105838).Prime := by
  rw [fullRecordGapTerm03462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03462_fast_pow_mod_ne_one

def fullRecordGapValue03463 : Nat := fullRecordGapCenterValue - 105454

theorem fullRecordGapTerm03463_eq_value :
    recordGapCenter - 105454 = fullRecordGapValue03463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03463 (fullRecordGapValue03463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03463_not_prime : ¬(recordGapCenter - 105454).Prime := by
  rw [fullRecordGapTerm03463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03463_fast_pow_mod_ne_one

def fullRecordGapValue03464 : Nat := fullRecordGapCenterValue - 105394

theorem fullRecordGapTerm03464_eq_value :
    recordGapCenter - 105394 = fullRecordGapValue03464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03464 (fullRecordGapValue03464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03464_not_prime : ¬(recordGapCenter - 105394).Prime := by
  rw [fullRecordGapTerm03464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03464_fast_pow_mod_ne_one

def fullRecordGapValue03465 : Nat := fullRecordGapCenterValue - 105082

theorem fullRecordGapTerm03465_eq_value :
    recordGapCenter - 105082 = fullRecordGapValue03465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03465 (fullRecordGapValue03465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03465_not_prime : ¬(recordGapCenter - 105082).Prime := by
  rw [fullRecordGapTerm03465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03465_fast_pow_mod_ne_one

def fullRecordGapValue03466 : Nat := fullRecordGapCenterValue - 105058

theorem fullRecordGapTerm03466_eq_value :
    recordGapCenter - 105058 = fullRecordGapValue03466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03466 (fullRecordGapValue03466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03466_not_prime : ¬(recordGapCenter - 105058).Prime := by
  rw [fullRecordGapTerm03466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03466_fast_pow_mod_ne_one

def fullRecordGapValue03467 : Nat := fullRecordGapCenterValue - 104722

theorem fullRecordGapTerm03467_eq_value :
    recordGapCenter - 104722 = fullRecordGapValue03467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03467 (fullRecordGapValue03467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03467_not_prime : ¬(recordGapCenter - 104722).Prime := by
  rw [fullRecordGapTerm03467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03467_fast_pow_mod_ne_one

def fullRecordGapValue03468 : Nat := fullRecordGapCenterValue - 104544

theorem fullRecordGapTerm03468_eq_value :
    recordGapCenter - 104544 = fullRecordGapValue03468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03468 (fullRecordGapValue03468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03468_not_prime : ¬(recordGapCenter - 104544).Prime := by
  rw [fullRecordGapTerm03468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03468_fast_pow_mod_ne_one

def fullRecordGapValue03469 : Nat := fullRecordGapCenterValue - 104362

theorem fullRecordGapTerm03469_eq_value :
    recordGapCenter - 104362 = fullRecordGapValue03469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03469 (fullRecordGapValue03469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03469_not_prime : ¬(recordGapCenter - 104362).Prime := by
  rw [fullRecordGapTerm03469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03469_fast_pow_mod_ne_one

def fullRecordGapValue03470 : Nat := fullRecordGapCenterValue - 103858

theorem fullRecordGapTerm03470_eq_value :
    recordGapCenter - 103858 = fullRecordGapValue03470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03470 (fullRecordGapValue03470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03470_not_prime : ¬(recordGapCenter - 103858).Prime := by
  rw [fullRecordGapTerm03470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03470_fast_pow_mod_ne_one

def fullRecordGapValue03471 : Nat := fullRecordGapCenterValue - 103498

theorem fullRecordGapTerm03471_eq_value :
    recordGapCenter - 103498 = fullRecordGapValue03471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03471 (fullRecordGapValue03471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03471_not_prime : ¬(recordGapCenter - 103498).Prime := by
  rw [fullRecordGapTerm03471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03471_fast_pow_mod_ne_one

def fullRecordGapValue03472 : Nat := fullRecordGapCenterValue - 103488

theorem fullRecordGapTerm03472_eq_value :
    recordGapCenter - 103488 = fullRecordGapValue03472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03472 (fullRecordGapValue03472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03472_not_prime : ¬(recordGapCenter - 103488).Prime := by
  rw [fullRecordGapTerm03472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03472_fast_pow_mod_ne_one

def fullRecordGapValue03473 : Nat := fullRecordGapCenterValue - 103438

theorem fullRecordGapTerm03473_eq_value :
    recordGapCenter - 103438 = fullRecordGapValue03473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03473 (fullRecordGapValue03473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03473_not_prime : ¬(recordGapCenter - 103438).Prime := by
  rw [fullRecordGapTerm03473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03473_fast_pow_mod_ne_one

def fullRecordGapValue03474 : Nat := fullRecordGapCenterValue - 103078

theorem fullRecordGapTerm03474_eq_value :
    recordGapCenter - 103078 = fullRecordGapValue03474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03474 (fullRecordGapValue03474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03474_not_prime : ¬(recordGapCenter - 103078).Prime := by
  rw [fullRecordGapTerm03474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03474_fast_pow_mod_ne_one

def fullRecordGapValue03475 : Nat := fullRecordGapCenterValue - 102958

theorem fullRecordGapTerm03475_eq_value :
    recordGapCenter - 102958 = fullRecordGapValue03475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03475 (fullRecordGapValue03475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03475_not_prime : ¬(recordGapCenter - 102958).Prime := by
  rw [fullRecordGapTerm03475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03475_fast_pow_mod_ne_one

def fullRecordGapValue03476 : Nat := fullRecordGapCenterValue - 102874

theorem fullRecordGapTerm03476_eq_value :
    recordGapCenter - 102874 = fullRecordGapValue03476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03476 (fullRecordGapValue03476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03476_not_prime : ¬(recordGapCenter - 102874).Prime := by
  rw [fullRecordGapTerm03476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03476_fast_pow_mod_ne_one

def fullRecordGapValue03477 : Nat := fullRecordGapCenterValue - 102694

theorem fullRecordGapTerm03477_eq_value :
    recordGapCenter - 102694 = fullRecordGapValue03477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03477 (fullRecordGapValue03477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03477_not_prime : ¬(recordGapCenter - 102694).Prime := by
  rw [fullRecordGapTerm03477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03477_fast_pow_mod_ne_one

def fullRecordGapValue03478 : Nat := fullRecordGapCenterValue - 102658

theorem fullRecordGapTerm03478_eq_value :
    recordGapCenter - 102658 = fullRecordGapValue03478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03478 (fullRecordGapValue03478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03478_not_prime : ¬(recordGapCenter - 102658).Prime := by
  rw [fullRecordGapTerm03478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03478_fast_pow_mod_ne_one

def fullRecordGapValue03479 : Nat := fullRecordGapCenterValue - 102514

theorem fullRecordGapTerm03479_eq_value :
    recordGapCenter - 102514 = fullRecordGapValue03479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03479 (fullRecordGapValue03479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03479_not_prime : ¬(recordGapCenter - 102514).Prime := by
  rw [fullRecordGapTerm03479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03479_fast_pow_mod_ne_one

def fullRecordGapValue03480 : Nat := fullRecordGapCenterValue - 102478

theorem fullRecordGapTerm03480_eq_value :
    recordGapCenter - 102478 = fullRecordGapValue03480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03480 (fullRecordGapValue03480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03480_not_prime : ¬(recordGapCenter - 102478).Prime := by
  rw [fullRecordGapTerm03480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03480_fast_pow_mod_ne_one

def fullRecordGapValue03481 : Nat := fullRecordGapCenterValue - 102262

theorem fullRecordGapTerm03481_eq_value :
    recordGapCenter - 102262 = fullRecordGapValue03481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03481 (fullRecordGapValue03481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03481_not_prime : ¬(recordGapCenter - 102262).Prime := by
  rw [fullRecordGapTerm03481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03481_fast_pow_mod_ne_one

def fullRecordGapValue03482 : Nat := fullRecordGapCenterValue - 102142

theorem fullRecordGapTerm03482_eq_value :
    recordGapCenter - 102142 = fullRecordGapValue03482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03482 (fullRecordGapValue03482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03482_not_prime : ¬(recordGapCenter - 102142).Prime := by
  rw [fullRecordGapTerm03482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03482_fast_pow_mod_ne_one

def fullRecordGapValue03483 : Nat := fullRecordGapCenterValue - 102118

theorem fullRecordGapTerm03483_eq_value :
    recordGapCenter - 102118 = fullRecordGapValue03483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03483 (fullRecordGapValue03483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03483_not_prime : ¬(recordGapCenter - 102118).Prime := by
  rw [fullRecordGapTerm03483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03483_fast_pow_mod_ne_one

def fullRecordGapValue03484 : Nat := fullRecordGapCenterValue - 102094

theorem fullRecordGapTerm03484_eq_value :
    recordGapCenter - 102094 = fullRecordGapValue03484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03484 (fullRecordGapValue03484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03484_not_prime : ¬(recordGapCenter - 102094).Prime := by
  rw [fullRecordGapTerm03484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03484_fast_pow_mod_ne_one

def fullRecordGapValue03485 : Nat := fullRecordGapCenterValue - 102060

theorem fullRecordGapTerm03485_eq_value :
    recordGapCenter - 102060 = fullRecordGapValue03485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03485 (fullRecordGapValue03485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03485_not_prime : ¬(recordGapCenter - 102060).Prime := by
  rw [fullRecordGapTerm03485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03485_fast_pow_mod_ne_one

def fullRecordGapValue03486 : Nat := fullRecordGapCenterValue - 101302

theorem fullRecordGapTerm03486_eq_value :
    recordGapCenter - 101302 = fullRecordGapValue03486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03486 (fullRecordGapValue03486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03486_not_prime : ¬(recordGapCenter - 101302).Prime := by
  rw [fullRecordGapTerm03486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03486_fast_pow_mod_ne_one

def fullRecordGapValue03487 : Nat := fullRecordGapCenterValue - 101254

theorem fullRecordGapTerm03487_eq_value :
    recordGapCenter - 101254 = fullRecordGapValue03487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03487 (fullRecordGapValue03487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03487_not_prime : ¬(recordGapCenter - 101254).Prime := by
  rw [fullRecordGapTerm03487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03487_fast_pow_mod_ne_one

def fullRecordGapValue03488 : Nat := fullRecordGapCenterValue - 101250

theorem fullRecordGapTerm03488_eq_value :
    recordGapCenter - 101250 = fullRecordGapValue03488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03488 (fullRecordGapValue03488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03488_not_prime : ¬(recordGapCenter - 101250).Prime := by
  rw [fullRecordGapTerm03488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03488_fast_pow_mod_ne_one

def fullRecordGapValue03489 : Nat := fullRecordGapCenterValue - 101098

theorem fullRecordGapTerm03489_eq_value :
    recordGapCenter - 101098 = fullRecordGapValue03489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03489 (fullRecordGapValue03489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03489_not_prime : ¬(recordGapCenter - 101098).Prime := by
  rw [fullRecordGapTerm03489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03489_fast_pow_mod_ne_one

def fullRecordGapValue03490 : Nat := fullRecordGapCenterValue - 100834

theorem fullRecordGapTerm03490_eq_value :
    recordGapCenter - 100834 = fullRecordGapValue03490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03490 (fullRecordGapValue03490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03490_not_prime : ¬(recordGapCenter - 100834).Prime := by
  rw [fullRecordGapTerm03490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03490_fast_pow_mod_ne_one

def fullRecordGapValue03491 : Nat := fullRecordGapCenterValue - 100774

theorem fullRecordGapTerm03491_eq_value :
    recordGapCenter - 100774 = fullRecordGapValue03491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03491 (fullRecordGapValue03491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03491_not_prime : ¬(recordGapCenter - 100774).Prime := by
  rw [fullRecordGapTerm03491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03491_fast_pow_mod_ne_one

def fullRecordGapValue03492 : Nat := fullRecordGapCenterValue - 100222

theorem fullRecordGapTerm03492_eq_value :
    recordGapCenter - 100222 = fullRecordGapValue03492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03492 (fullRecordGapValue03492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03492_not_prime : ¬(recordGapCenter - 100222).Prime := by
  rw [fullRecordGapTerm03492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03492_fast_pow_mod_ne_one

def fullRecordGapValue03493 : Nat := fullRecordGapCenterValue - 100174

theorem fullRecordGapTerm03493_eq_value :
    recordGapCenter - 100174 = fullRecordGapValue03493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03493 (fullRecordGapValue03493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03493_not_prime : ¬(recordGapCenter - 100174).Prime := by
  rw [fullRecordGapTerm03493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03493_fast_pow_mod_ne_one

def fullRecordGapValue03494 : Nat := fullRecordGapCenterValue - 100000

theorem fullRecordGapTerm03494_eq_value :
    recordGapCenter - 100000 = fullRecordGapValue03494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03494 (fullRecordGapValue03494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03494_not_prime : ¬(recordGapCenter - 100000).Prime := by
  rw [fullRecordGapTerm03494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03494_fast_pow_mod_ne_one

def fullRecordGapValue03495 : Nat := fullRecordGapCenterValue - 99874

theorem fullRecordGapTerm03495_eq_value :
    recordGapCenter - 99874 = fullRecordGapValue03495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03495 (fullRecordGapValue03495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03495_not_prime : ¬(recordGapCenter - 99874).Prime := by
  rw [fullRecordGapTerm03495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03495_fast_pow_mod_ne_one

def fullRecordGapValue03496 : Nat := fullRecordGapCenterValue - 99754

theorem fullRecordGapTerm03496_eq_value :
    recordGapCenter - 99754 = fullRecordGapValue03496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03496 (fullRecordGapValue03496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03496_not_prime : ¬(recordGapCenter - 99754).Prime := by
  rw [fullRecordGapTerm03496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03496_fast_pow_mod_ne_one

def fullRecordGapValue03497 : Nat := fullRecordGapCenterValue - 99742

theorem fullRecordGapTerm03497_eq_value :
    recordGapCenter - 99742 = fullRecordGapValue03497 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03497_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03497 (fullRecordGapValue03497 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03497_not_prime : ¬(recordGapCenter - 99742).Prime := by
  rw [fullRecordGapTerm03497_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03497, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03497_fast_pow_mod_ne_one

def fullRecordGapValue03498 : Nat := fullRecordGapCenterValue - 99622

theorem fullRecordGapTerm03498_eq_value :
    recordGapCenter - 99622 = fullRecordGapValue03498 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03498_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03498 (fullRecordGapValue03498 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03498_not_prime : ¬(recordGapCenter - 99622).Prime := by
  rw [fullRecordGapTerm03498_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03498, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03498_fast_pow_mod_ne_one

def fullRecordGapValue03499 : Nat := fullRecordGapCenterValue - 99574

theorem fullRecordGapTerm03499_eq_value :
    recordGapCenter - 99574 = fullRecordGapValue03499 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03499_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03499 (fullRecordGapValue03499 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03499_not_prime : ¬(recordGapCenter - 99574).Prime := by
  rw [fullRecordGapTerm03499_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03499, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03499_fast_pow_mod_ne_one

def fullRecordGapValue03500 : Nat := fullRecordGapCenterValue - 99454

theorem fullRecordGapTerm03500_eq_value :
    recordGapCenter - 99454 = fullRecordGapValue03500 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03500_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03500 (fullRecordGapValue03500 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03500_not_prime : ¬(recordGapCenter - 99454).Prime := by
  rw [fullRecordGapTerm03500_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03500, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03500_fast_pow_mod_ne_one

def fullRecordGapValue03501 : Nat := fullRecordGapCenterValue - 99000

theorem fullRecordGapTerm03501_eq_value :
    recordGapCenter - 99000 = fullRecordGapValue03501 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03501_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03501 (fullRecordGapValue03501 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03501_not_prime : ¬(recordGapCenter - 99000).Prime := by
  rw [fullRecordGapTerm03501_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03501, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03501_fast_pow_mod_ne_one

def fullRecordGapValue03502 : Nat := fullRecordGapCenterValue - 98962

theorem fullRecordGapTerm03502_eq_value :
    recordGapCenter - 98962 = fullRecordGapValue03502 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03502_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03502 (fullRecordGapValue03502 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03502_not_prime : ¬(recordGapCenter - 98962).Prime := by
  rw [fullRecordGapTerm03502_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03502, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03502_fast_pow_mod_ne_one

def fullRecordGapValue03503 : Nat := fullRecordGapCenterValue - 98818

theorem fullRecordGapTerm03503_eq_value :
    recordGapCenter - 98818 = fullRecordGapValue03503 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03503_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03503 (fullRecordGapValue03503 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03503_not_prime : ¬(recordGapCenter - 98818).Prime := by
  rw [fullRecordGapTerm03503_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03503, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03503_fast_pow_mod_ne_one

def fullRecordGapValue03504 : Nat := fullRecordGapCenterValue - 98662

theorem fullRecordGapTerm03504_eq_value :
    recordGapCenter - 98662 = fullRecordGapValue03504 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03504_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03504 (fullRecordGapValue03504 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03504_not_prime : ¬(recordGapCenter - 98662).Prime := by
  rw [fullRecordGapTerm03504_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03504, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03504_fast_pow_mod_ne_one

def fullRecordGapValue03505 : Nat := fullRecordGapCenterValue - 98614

theorem fullRecordGapTerm03505_eq_value :
    recordGapCenter - 98614 = fullRecordGapValue03505 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03505_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03505 (fullRecordGapValue03505 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03505_not_prime : ¬(recordGapCenter - 98614).Prime := by
  rw [fullRecordGapTerm03505_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03505, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03505_fast_pow_mod_ne_one

def fullRecordGapValue03506 : Nat := fullRecordGapCenterValue - 98422

theorem fullRecordGapTerm03506_eq_value :
    recordGapCenter - 98422 = fullRecordGapValue03506 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03506_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03506 (fullRecordGapValue03506 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03506_not_prime : ¬(recordGapCenter - 98422).Prime := by
  rw [fullRecordGapTerm03506_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03506, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03506_fast_pow_mod_ne_one

def fullRecordGapValue03507 : Nat := fullRecordGapCenterValue - 98314

theorem fullRecordGapTerm03507_eq_value :
    recordGapCenter - 98314 = fullRecordGapValue03507 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03507_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03507 (fullRecordGapValue03507 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03507_not_prime : ¬(recordGapCenter - 98314).Prime := by
  rw [fullRecordGapTerm03507_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03507, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03507_fast_pow_mod_ne_one

def fullRecordGapValue03508 : Nat := fullRecordGapCenterValue - 98304

theorem fullRecordGapTerm03508_eq_value :
    recordGapCenter - 98304 = fullRecordGapValue03508 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03508_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03508 (fullRecordGapValue03508 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03508_not_prime : ¬(recordGapCenter - 98304).Prime := by
  rw [fullRecordGapTerm03508_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03508, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03508_fast_pow_mod_ne_one

def fullRecordGapValue03509 : Nat := fullRecordGapCenterValue - 98074

theorem fullRecordGapTerm03509_eq_value :
    recordGapCenter - 98074 = fullRecordGapValue03509 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03509_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03509 (fullRecordGapValue03509 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03509_not_prime : ¬(recordGapCenter - 98074).Prime := by
  rw [fullRecordGapTerm03509_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03509, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03509_fast_pow_mod_ne_one

def fullRecordGapValue03510 : Nat := fullRecordGapCenterValue - 98062

theorem fullRecordGapTerm03510_eq_value :
    recordGapCenter - 98062 = fullRecordGapValue03510 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03510_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03510 (fullRecordGapValue03510 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03510_not_prime : ¬(recordGapCenter - 98062).Prime := by
  rw [fullRecordGapTerm03510_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03510, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03510_fast_pow_mod_ne_one

def fullRecordGapValue03511 : Nat := fullRecordGapCenterValue - 97738

theorem fullRecordGapTerm03511_eq_value :
    recordGapCenter - 97738 = fullRecordGapValue03511 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03511_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03511 (fullRecordGapValue03511 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03511_not_prime : ¬(recordGapCenter - 97738).Prime := by
  rw [fullRecordGapTerm03511_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03511, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03511_fast_pow_mod_ne_one

def fullRecordGapValue03512 : Nat := fullRecordGapCenterValue - 97558

theorem fullRecordGapTerm03512_eq_value :
    recordGapCenter - 97558 = fullRecordGapValue03512 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03512_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03512 (fullRecordGapValue03512 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03512_not_prime : ¬(recordGapCenter - 97558).Prime := by
  rw [fullRecordGapTerm03512_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03512, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03512_fast_pow_mod_ne_one

def fullRecordGapValue03513 : Nat := fullRecordGapCenterValue - 97054

theorem fullRecordGapTerm03513_eq_value :
    recordGapCenter - 97054 = fullRecordGapValue03513 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03513_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03513 (fullRecordGapValue03513 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03513_not_prime : ¬(recordGapCenter - 97054).Prime := by
  rw [fullRecordGapTerm03513_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03513, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03513_fast_pow_mod_ne_one

def fullRecordGapValue03514 : Nat := fullRecordGapCenterValue - 97020

theorem fullRecordGapTerm03514_eq_value :
    recordGapCenter - 97020 = fullRecordGapValue03514 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03514_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03514 (fullRecordGapValue03514 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03514_not_prime : ¬(recordGapCenter - 97020).Prime := by
  rw [fullRecordGapTerm03514_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03514, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03514_fast_pow_mod_ne_one

def fullRecordGapValue03515 : Nat := fullRecordGapCenterValue - 96898

theorem fullRecordGapTerm03515_eq_value :
    recordGapCenter - 96898 = fullRecordGapValue03515 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03515_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03515 (fullRecordGapValue03515 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03515_not_prime : ¬(recordGapCenter - 96898).Prime := by
  rw [fullRecordGapTerm03515_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03515, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03515_fast_pow_mod_ne_one

def fullRecordGapValue03516 : Nat := fullRecordGapCenterValue - 96682

theorem fullRecordGapTerm03516_eq_value :
    recordGapCenter - 96682 = fullRecordGapValue03516 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03516_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03516 (fullRecordGapValue03516 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03516_not_prime : ¬(recordGapCenter - 96682).Prime := by
  rw [fullRecordGapTerm03516_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03516, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03516_fast_pow_mod_ne_one

def fullRecordGapValue03517 : Nat := fullRecordGapCenterValue - 96598

theorem fullRecordGapTerm03517_eq_value :
    recordGapCenter - 96598 = fullRecordGapValue03517 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03517_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03517 (fullRecordGapValue03517 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03517_not_prime : ¬(recordGapCenter - 96598).Prime := by
  rw [fullRecordGapTerm03517_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03517, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03517_fast_pow_mod_ne_one

def fullRecordGapValue03518 : Nat := fullRecordGapCenterValue - 96394

theorem fullRecordGapTerm03518_eq_value :
    recordGapCenter - 96394 = fullRecordGapValue03518 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03518_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03518 (fullRecordGapValue03518 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03518_not_prime : ¬(recordGapCenter - 96394).Prime := by
  rw [fullRecordGapTerm03518_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03518, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03518_fast_pow_mod_ne_one

def fullRecordGapValue03519 : Nat := fullRecordGapCenterValue - 96228

theorem fullRecordGapTerm03519_eq_value :
    recordGapCenter - 96228 = fullRecordGapValue03519 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03519_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03519 (fullRecordGapValue03519 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03519_not_prime : ¬(recordGapCenter - 96228).Prime := by
  rw [fullRecordGapTerm03519_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03519, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03519_fast_pow_mod_ne_one

def fullRecordGapValue03520 : Nat := fullRecordGapCenterValue - 96000

theorem fullRecordGapTerm03520_eq_value :
    recordGapCenter - 96000 = fullRecordGapValue03520 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03520_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03520 (fullRecordGapValue03520 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03520_not_prime : ¬(recordGapCenter - 96000).Prime := by
  rw [fullRecordGapTerm03520_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03520, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03520_fast_pow_mod_ne_one

def fullRecordGapValue03521 : Nat := fullRecordGapCenterValue - 95962

theorem fullRecordGapTerm03521_eq_value :
    recordGapCenter - 95962 = fullRecordGapValue03521 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03521_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03521 (fullRecordGapValue03521 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03521_not_prime : ¬(recordGapCenter - 95962).Prime := by
  rw [fullRecordGapTerm03521_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03521, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03521_fast_pow_mod_ne_one

def fullRecordGapValue03522 : Nat := fullRecordGapCenterValue - 95878

theorem fullRecordGapTerm03522_eq_value :
    recordGapCenter - 95878 = fullRecordGapValue03522 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03522_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03522 (fullRecordGapValue03522 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03522_not_prime : ¬(recordGapCenter - 95878).Prime := by
  rw [fullRecordGapTerm03522_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03522, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03522_fast_pow_mod_ne_one

def fullRecordGapValue03523 : Nat := fullRecordGapCenterValue - 95554

theorem fullRecordGapTerm03523_eq_value :
    recordGapCenter - 95554 = fullRecordGapValue03523 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03523_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03523 (fullRecordGapValue03523 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03523_not_prime : ¬(recordGapCenter - 95554).Prime := by
  rw [fullRecordGapTerm03523_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03523, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03523_fast_pow_mod_ne_one

def fullRecordGapValue03524 : Nat := fullRecordGapCenterValue - 95482

theorem fullRecordGapTerm03524_eq_value :
    recordGapCenter - 95482 = fullRecordGapValue03524 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03524_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03524 (fullRecordGapValue03524 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03524_not_prime : ¬(recordGapCenter - 95482).Prime := by
  rw [fullRecordGapTerm03524_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03524, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03524_fast_pow_mod_ne_one

def fullRecordGapValue03525 : Nat := fullRecordGapCenterValue - 95434

theorem fullRecordGapTerm03525_eq_value :
    recordGapCenter - 95434 = fullRecordGapValue03525 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03525_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03525 (fullRecordGapValue03525 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03525_not_prime : ¬(recordGapCenter - 95434).Prime := by
  rw [fullRecordGapTerm03525_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03525, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03525_fast_pow_mod_ne_one

def fullRecordGapValue03526 : Nat := fullRecordGapCenterValue - 95422

theorem fullRecordGapTerm03526_eq_value :
    recordGapCenter - 95422 = fullRecordGapValue03526 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03526_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03526 (fullRecordGapValue03526 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03526_not_prime : ¬(recordGapCenter - 95422).Prime := by
  rw [fullRecordGapTerm03526_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03526, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03526_fast_pow_mod_ne_one

def fullRecordGapValue03527 : Nat := fullRecordGapCenterValue - 95398

theorem fullRecordGapTerm03527_eq_value :
    recordGapCenter - 95398 = fullRecordGapValue03527 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03527_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03527 (fullRecordGapValue03527 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03527_not_prime : ¬(recordGapCenter - 95398).Prime := by
  rw [fullRecordGapTerm03527_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03527, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03527_fast_pow_mod_ne_one

def fullRecordGapValue03528 : Nat := fullRecordGapCenterValue - 95218

theorem fullRecordGapTerm03528_eq_value :
    recordGapCenter - 95218 = fullRecordGapValue03528 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03528_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03528 (fullRecordGapValue03528 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03528_not_prime : ¬(recordGapCenter - 95218).Prime := by
  rw [fullRecordGapTerm03528_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03528, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03528_fast_pow_mod_ne_one

def fullRecordGapValue03529 : Nat := fullRecordGapCenterValue - 94918

theorem fullRecordGapTerm03529_eq_value :
    recordGapCenter - 94918 = fullRecordGapValue03529 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03529_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03529 (fullRecordGapValue03529 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03529_not_prime : ¬(recordGapCenter - 94918).Prime := by
  rw [fullRecordGapTerm03529_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03529, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03529_fast_pow_mod_ne_one

def fullRecordGapValue03530 : Nat := fullRecordGapCenterValue - 94864

theorem fullRecordGapTerm03530_eq_value :
    recordGapCenter - 94864 = fullRecordGapValue03530 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03530_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03530 (fullRecordGapValue03530 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03530_not_prime : ¬(recordGapCenter - 94864).Prime := by
  rw [fullRecordGapTerm03530_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03530, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03530_fast_pow_mod_ne_one

def fullRecordGapValue03531 : Nat := fullRecordGapCenterValue - 94762

theorem fullRecordGapTerm03531_eq_value :
    recordGapCenter - 94762 = fullRecordGapValue03531 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03531_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03531 (fullRecordGapValue03531 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03531_not_prime : ¬(recordGapCenter - 94762).Prime := by
  rw [fullRecordGapTerm03531_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03531, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03531_fast_pow_mod_ne_one

def fullRecordGapValue03532 : Nat := fullRecordGapCenterValue - 94702

theorem fullRecordGapTerm03532_eq_value :
    recordGapCenter - 94702 = fullRecordGapValue03532 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03532_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03532 (fullRecordGapValue03532 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03532_not_prime : ¬(recordGapCenter - 94702).Prime := by
  rw [fullRecordGapTerm03532_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03532, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03532_fast_pow_mod_ne_one

def fullRecordGapValue03533 : Nat := fullRecordGapCenterValue - 94678

theorem fullRecordGapTerm03533_eq_value :
    recordGapCenter - 94678 = fullRecordGapValue03533 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03533_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03533 (fullRecordGapValue03533 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03533_not_prime : ¬(recordGapCenter - 94678).Prime := by
  rw [fullRecordGapTerm03533_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03533, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03533_fast_pow_mod_ne_one

def fullRecordGapValue03534 : Nat := fullRecordGapCenterValue - 94500

theorem fullRecordGapTerm03534_eq_value :
    recordGapCenter - 94500 = fullRecordGapValue03534 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03534_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03534 (fullRecordGapValue03534 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03534_not_prime : ¬(recordGapCenter - 94500).Prime := by
  rw [fullRecordGapTerm03534_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03534, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03534_fast_pow_mod_ne_one

def fullRecordGapValue03535 : Nat := fullRecordGapCenterValue - 94474

theorem fullRecordGapTerm03535_eq_value :
    recordGapCenter - 94474 = fullRecordGapValue03535 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03535_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03535 (fullRecordGapValue03535 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03535_not_prime : ¬(recordGapCenter - 94474).Prime := by
  rw [fullRecordGapTerm03535_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03535, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03535_fast_pow_mod_ne_one

def fullRecordGapValue03536 : Nat := fullRecordGapCenterValue - 94258

theorem fullRecordGapTerm03536_eq_value :
    recordGapCenter - 94258 = fullRecordGapValue03536 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03536_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03536 (fullRecordGapValue03536 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03536_not_prime : ¬(recordGapCenter - 94258).Prime := by
  rw [fullRecordGapTerm03536_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03536, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03536_fast_pow_mod_ne_one

def fullRecordGapValue03537 : Nat := fullRecordGapCenterValue - 93994

theorem fullRecordGapTerm03537_eq_value :
    recordGapCenter - 93994 = fullRecordGapValue03537 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03537_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03537 (fullRecordGapValue03537 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03537_not_prime : ¬(recordGapCenter - 93994).Prime := by
  rw [fullRecordGapTerm03537_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03537, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03537_fast_pow_mod_ne_one

def fullRecordGapValue03538 : Nat := fullRecordGapCenterValue - 93838

theorem fullRecordGapTerm03538_eq_value :
    recordGapCenter - 93838 = fullRecordGapValue03538 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03538_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03538 (fullRecordGapValue03538 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03538_not_prime : ¬(recordGapCenter - 93838).Prime := by
  rw [fullRecordGapTerm03538_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03538, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03538_fast_pow_mod_ne_one

def fullRecordGapValue03539 : Nat := fullRecordGapCenterValue - 93778

theorem fullRecordGapTerm03539_eq_value :
    recordGapCenter - 93778 = fullRecordGapValue03539 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03539_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03539 (fullRecordGapValue03539 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03539_not_prime : ¬(recordGapCenter - 93778).Prime := by
  rw [fullRecordGapTerm03539_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03539, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03539_fast_pow_mod_ne_one

def fullRecordGapValue03540 : Nat := fullRecordGapCenterValue - 93634

theorem fullRecordGapTerm03540_eq_value :
    recordGapCenter - 93634 = fullRecordGapValue03540 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03540_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03540 (fullRecordGapValue03540 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03540_not_prime : ¬(recordGapCenter - 93634).Prime := by
  rw [fullRecordGapTerm03540_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03540, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03540_fast_pow_mod_ne_one

def fullRecordGapValue03541 : Nat := fullRecordGapCenterValue - 93538

theorem fullRecordGapTerm03541_eq_value :
    recordGapCenter - 93538 = fullRecordGapValue03541 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03541_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03541 (fullRecordGapValue03541 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03541_not_prime : ¬(recordGapCenter - 93538).Prime := by
  rw [fullRecordGapTerm03541_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03541, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03541_fast_pow_mod_ne_one

def fullRecordGapValue03542 : Nat := fullRecordGapCenterValue - 93358

theorem fullRecordGapTerm03542_eq_value :
    recordGapCenter - 93358 = fullRecordGapValue03542 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03542_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03542 (fullRecordGapValue03542 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03542_not_prime : ¬(recordGapCenter - 93358).Prime := by
  rw [fullRecordGapTerm03542_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03542, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03542_fast_pow_mod_ne_one

def fullRecordGapValue03543 : Nat := fullRecordGapCenterValue - 93312

theorem fullRecordGapTerm03543_eq_value :
    recordGapCenter - 93312 = fullRecordGapValue03543 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03543_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03543 (fullRecordGapValue03543 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03543_not_prime : ¬(recordGapCenter - 93312).Prime := by
  rw [fullRecordGapTerm03543_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03543, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03543_fast_pow_mod_ne_one

def fullRecordGapValue03544 : Nat := fullRecordGapCenterValue - 93202

theorem fullRecordGapTerm03544_eq_value :
    recordGapCenter - 93202 = fullRecordGapValue03544 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03544_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03544 (fullRecordGapValue03544 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03544_not_prime : ¬(recordGapCenter - 93202).Prime := by
  rw [fullRecordGapTerm03544_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03544, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03544_fast_pow_mod_ne_one

def fullRecordGapValue03545 : Nat := fullRecordGapCenterValue - 93022

theorem fullRecordGapTerm03545_eq_value :
    recordGapCenter - 93022 = fullRecordGapValue03545 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03545_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03545 (fullRecordGapValue03545 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03545_not_prime : ¬(recordGapCenter - 93022).Prime := by
  rw [fullRecordGapTerm03545_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03545, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03545_fast_pow_mod_ne_one

def fullRecordGapValue03546 : Nat := fullRecordGapCenterValue - 92914

theorem fullRecordGapTerm03546_eq_value :
    recordGapCenter - 92914 = fullRecordGapValue03546 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03546_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03546 (fullRecordGapValue03546 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03546_not_prime : ¬(recordGapCenter - 92914).Prime := by
  rw [fullRecordGapTerm03546_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03546, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03546_fast_pow_mod_ne_one

def fullRecordGapValue03547 : Nat := fullRecordGapCenterValue - 92698

theorem fullRecordGapTerm03547_eq_value :
    recordGapCenter - 92698 = fullRecordGapValue03547 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03547_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03547 (fullRecordGapValue03547 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03547_not_prime : ¬(recordGapCenter - 92698).Prime := by
  rw [fullRecordGapTerm03547_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03547, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03547_fast_pow_mod_ne_one

def fullRecordGapValue03548 : Nat := fullRecordGapCenterValue - 92614

theorem fullRecordGapTerm03548_eq_value :
    recordGapCenter - 92614 = fullRecordGapValue03548 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03548_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03548 (fullRecordGapValue03548 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03548_not_prime : ¬(recordGapCenter - 92614).Prime := by
  rw [fullRecordGapTerm03548_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03548, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03548_fast_pow_mod_ne_one

def fullRecordGapValue03549 : Nat := fullRecordGapCenterValue - 92398

theorem fullRecordGapTerm03549_eq_value :
    recordGapCenter - 92398 = fullRecordGapValue03549 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03549_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03549 (fullRecordGapValue03549 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03549_not_prime : ¬(recordGapCenter - 92398).Prime := by
  rw [fullRecordGapTerm03549_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03549, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03549_fast_pow_mod_ne_one

def fullRecordGapValue03550 : Nat := fullRecordGapCenterValue - 92374

theorem fullRecordGapTerm03550_eq_value :
    recordGapCenter - 92374 = fullRecordGapValue03550 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03550_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03550 (fullRecordGapValue03550 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03550_not_prime : ¬(recordGapCenter - 92374).Prime := by
  rw [fullRecordGapTerm03550_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03550, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03550_fast_pow_mod_ne_one

def fullRecordGapValue03551 : Nat := fullRecordGapCenterValue - 92182

theorem fullRecordGapTerm03551_eq_value :
    recordGapCenter - 92182 = fullRecordGapValue03551 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03551_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03551 (fullRecordGapValue03551 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03551_not_prime : ¬(recordGapCenter - 92182).Prime := by
  rw [fullRecordGapTerm03551_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03551, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03551_fast_pow_mod_ne_one

def fullRecordGapValue03552 : Nat := fullRecordGapCenterValue - 92160

theorem fullRecordGapTerm03552_eq_value :
    recordGapCenter - 92160 = fullRecordGapValue03552 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03552_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03552 (fullRecordGapValue03552 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03552_not_prime : ¬(recordGapCenter - 92160).Prime := by
  rw [fullRecordGapTerm03552_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03552, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03552_fast_pow_mod_ne_one

def fullRecordGapValue03553 : Nat := fullRecordGapCenterValue - 92098

theorem fullRecordGapTerm03553_eq_value :
    recordGapCenter - 92098 = fullRecordGapValue03553 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03553_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03553 (fullRecordGapValue03553 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03553_not_prime : ¬(recordGapCenter - 92098).Prime := by
  rw [fullRecordGapTerm03553_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03553, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03553_fast_pow_mod_ne_one

def fullRecordGapValue03554 : Nat := fullRecordGapCenterValue - 91774

theorem fullRecordGapTerm03554_eq_value :
    recordGapCenter - 91774 = fullRecordGapValue03554 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03554_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03554 (fullRecordGapValue03554 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03554_not_prime : ¬(recordGapCenter - 91774).Prime := by
  rw [fullRecordGapTerm03554_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03554, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03554_fast_pow_mod_ne_one

def fullRecordGapValue03555 : Nat := fullRecordGapCenterValue - 91738

theorem fullRecordGapTerm03555_eq_value :
    recordGapCenter - 91738 = fullRecordGapValue03555 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03555_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03555 (fullRecordGapValue03555 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03555_not_prime : ¬(recordGapCenter - 91738).Prime := by
  rw [fullRecordGapTerm03555_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03555, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03555_fast_pow_mod_ne_one

def fullRecordGapValue03556 : Nat := fullRecordGapCenterValue - 91654

theorem fullRecordGapTerm03556_eq_value :
    recordGapCenter - 91654 = fullRecordGapValue03556 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03556_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03556 (fullRecordGapValue03556 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03556_not_prime : ¬(recordGapCenter - 91654).Prime := by
  rw [fullRecordGapTerm03556_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03556, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03556_fast_pow_mod_ne_one

def fullRecordGapValue03557 : Nat := fullRecordGapCenterValue - 91534

theorem fullRecordGapTerm03557_eq_value :
    recordGapCenter - 91534 = fullRecordGapValue03557 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03557_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03557 (fullRecordGapValue03557 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03557_not_prime : ¬(recordGapCenter - 91534).Prime := by
  rw [fullRecordGapTerm03557_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03557, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03557_fast_pow_mod_ne_one

def fullRecordGapValue03558 : Nat := fullRecordGapCenterValue - 91138

theorem fullRecordGapTerm03558_eq_value :
    recordGapCenter - 91138 = fullRecordGapValue03558 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03558_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03558 (fullRecordGapValue03558 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03558_not_prime : ¬(recordGapCenter - 91138).Prime := by
  rw [fullRecordGapTerm03558_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03558, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03558_fast_pow_mod_ne_one

def fullRecordGapValue03559 : Nat := fullRecordGapCenterValue - 91114

theorem fullRecordGapTerm03559_eq_value :
    recordGapCenter - 91114 = fullRecordGapValue03559 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03559_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03559 (fullRecordGapValue03559 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03559_not_prime : ¬(recordGapCenter - 91114).Prime := by
  rw [fullRecordGapTerm03559_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03559, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03559_fast_pow_mod_ne_one

def fullRecordGapValue03560 : Nat := fullRecordGapCenterValue - 90778

theorem fullRecordGapTerm03560_eq_value :
    recordGapCenter - 90778 = fullRecordGapValue03560 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03560_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03560 (fullRecordGapValue03560 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03560_not_prime : ¬(recordGapCenter - 90778).Prime := by
  rw [fullRecordGapTerm03560_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03560, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03560_fast_pow_mod_ne_one

def fullRecordGapValue03561 : Nat := fullRecordGapCenterValue - 90720

theorem fullRecordGapTerm03561_eq_value :
    recordGapCenter - 90720 = fullRecordGapValue03561 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03561_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03561 (fullRecordGapValue03561 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03561_not_prime : ¬(recordGapCenter - 90720).Prime := by
  rw [fullRecordGapTerm03561_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03561, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03561_fast_pow_mod_ne_one

def fullRecordGapValue03562 : Nat := fullRecordGapCenterValue - 90634

theorem fullRecordGapTerm03562_eq_value :
    recordGapCenter - 90634 = fullRecordGapValue03562 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03562_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03562 (fullRecordGapValue03562 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03562_not_prime : ¬(recordGapCenter - 90634).Prime := by
  rw [fullRecordGapTerm03562_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03562, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03562_fast_pow_mod_ne_one

def fullRecordGapValue03563 : Nat := fullRecordGapCenterValue - 90562

theorem fullRecordGapTerm03563_eq_value :
    recordGapCenter - 90562 = fullRecordGapValue03563 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03563_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03563 (fullRecordGapValue03563 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03563_not_prime : ¬(recordGapCenter - 90562).Prime := by
  rw [fullRecordGapTerm03563_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03563, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03563_fast_pow_mod_ne_one

def fullRecordGapValue03564 : Nat := fullRecordGapCenterValue - 90382

theorem fullRecordGapTerm03564_eq_value :
    recordGapCenter - 90382 = fullRecordGapValue03564 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03564_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03564 (fullRecordGapValue03564 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03564_not_prime : ¬(recordGapCenter - 90382).Prime := by
  rw [fullRecordGapTerm03564_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03564, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03564_fast_pow_mod_ne_one

def fullRecordGapValue03565 : Nat := fullRecordGapCenterValue - 90274

theorem fullRecordGapTerm03565_eq_value :
    recordGapCenter - 90274 = fullRecordGapValue03565 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03565_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03565 (fullRecordGapValue03565 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03565_not_prime : ¬(recordGapCenter - 90274).Prime := by
  rw [fullRecordGapTerm03565_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03565, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03565_fast_pow_mod_ne_one

def fullRecordGapValue03566 : Nat := fullRecordGapCenterValue - 90262

theorem fullRecordGapTerm03566_eq_value :
    recordGapCenter - 90262 = fullRecordGapValue03566 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03566_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03566 (fullRecordGapValue03566 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03566_not_prime : ¬(recordGapCenter - 90262).Prime := by
  rw [fullRecordGapTerm03566_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03566, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03566_fast_pow_mod_ne_one

def fullRecordGapValue03567 : Nat := fullRecordGapCenterValue - 89878

theorem fullRecordGapTerm03567_eq_value :
    recordGapCenter - 89878 = fullRecordGapValue03567 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03567_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03567 (fullRecordGapValue03567 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03567_not_prime : ¬(recordGapCenter - 89878).Prime := by
  rw [fullRecordGapTerm03567_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03567, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03567_fast_pow_mod_ne_one

def fullRecordGapValue03568 : Nat := fullRecordGapCenterValue - 89758

theorem fullRecordGapTerm03568_eq_value :
    recordGapCenter - 89758 = fullRecordGapValue03568 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03568_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03568 (fullRecordGapValue03568 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03568_not_prime : ¬(recordGapCenter - 89758).Prime := by
  rw [fullRecordGapTerm03568_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03568, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03568_fast_pow_mod_ne_one

def fullRecordGapValue03569 : Nat := fullRecordGapCenterValue - 89638

theorem fullRecordGapTerm03569_eq_value :
    recordGapCenter - 89638 = fullRecordGapValue03569 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03569_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03569 (fullRecordGapValue03569 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03569_not_prime : ¬(recordGapCenter - 89638).Prime := by
  rw [fullRecordGapTerm03569_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03569, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03569_fast_pow_mod_ne_one

def fullRecordGapValue03570 : Nat := fullRecordGapCenterValue - 89578

theorem fullRecordGapTerm03570_eq_value :
    recordGapCenter - 89578 = fullRecordGapValue03570 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03570_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03570 (fullRecordGapValue03570 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03570_not_prime : ¬(recordGapCenter - 89578).Prime := by
  rw [fullRecordGapTerm03570_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03570, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03570_fast_pow_mod_ne_one

def fullRecordGapValue03571 : Nat := fullRecordGapCenterValue - 89542

theorem fullRecordGapTerm03571_eq_value :
    recordGapCenter - 89542 = fullRecordGapValue03571 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03571_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03571 (fullRecordGapValue03571 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03571_not_prime : ¬(recordGapCenter - 89542).Prime := by
  rw [fullRecordGapTerm03571_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03571, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03571_fast_pow_mod_ne_one

def fullRecordGapValue03572 : Nat := fullRecordGapCenterValue - 89422

theorem fullRecordGapTerm03572_eq_value :
    recordGapCenter - 89422 = fullRecordGapValue03572 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03572_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03572 (fullRecordGapValue03572 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03572_not_prime : ¬(recordGapCenter - 89422).Prime := by
  rw [fullRecordGapTerm03572_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03572, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03572_fast_pow_mod_ne_one

def fullRecordGapValue03573 : Nat := fullRecordGapCenterValue - 89374

theorem fullRecordGapTerm03573_eq_value :
    recordGapCenter - 89374 = fullRecordGapValue03573 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03573_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03573 (fullRecordGapValue03573 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03573_not_prime : ¬(recordGapCenter - 89374).Prime := by
  rw [fullRecordGapTerm03573_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03573, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03573_fast_pow_mod_ne_one

def fullRecordGapValue03574 : Nat := fullRecordGapCenterValue - 89100

theorem fullRecordGapTerm03574_eq_value :
    recordGapCenter - 89100 = fullRecordGapValue03574 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03574_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03574 (fullRecordGapValue03574 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03574_not_prime : ¬(recordGapCenter - 89100).Prime := by
  rw [fullRecordGapTerm03574_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03574, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03574_fast_pow_mod_ne_one

def fullRecordGapValue03575 : Nat := fullRecordGapCenterValue - 89098

theorem fullRecordGapTerm03575_eq_value :
    recordGapCenter - 89098 = fullRecordGapValue03575 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03575_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03575 (fullRecordGapValue03575 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03575_not_prime : ¬(recordGapCenter - 89098).Prime := by
  rw [fullRecordGapTerm03575_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03575, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03575_fast_pow_mod_ne_one

def fullRecordGapValue03576 : Nat := fullRecordGapCenterValue - 89014

theorem fullRecordGapTerm03576_eq_value :
    recordGapCenter - 89014 = fullRecordGapValue03576 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03576_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03576 (fullRecordGapValue03576 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03576_not_prime : ¬(recordGapCenter - 89014).Prime := by
  rw [fullRecordGapTerm03576_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03576, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03576_fast_pow_mod_ne_one

def fullRecordGapValue03577 : Nat := fullRecordGapCenterValue - 88762

theorem fullRecordGapTerm03577_eq_value :
    recordGapCenter - 88762 = fullRecordGapValue03577 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03577_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03577 (fullRecordGapValue03577 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03577_not_prime : ¬(recordGapCenter - 88762).Prime := by
  rw [fullRecordGapTerm03577_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03577, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03577_fast_pow_mod_ne_one

def fullRecordGapValue03578 : Nat := fullRecordGapCenterValue - 88704

theorem fullRecordGapTerm03578_eq_value :
    recordGapCenter - 88704 = fullRecordGapValue03578 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03578_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03578 (fullRecordGapValue03578 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03578_not_prime : ¬(recordGapCenter - 88704).Prime := by
  rw [fullRecordGapTerm03578_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03578, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03578_fast_pow_mod_ne_one

def fullRecordGapValue03579 : Nat := fullRecordGapCenterValue - 88702

theorem fullRecordGapTerm03579_eq_value :
    recordGapCenter - 88702 = fullRecordGapValue03579 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03579_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03579 (fullRecordGapValue03579 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03579_not_prime : ¬(recordGapCenter - 88702).Prime := by
  rw [fullRecordGapTerm03579_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03579, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03579_fast_pow_mod_ne_one

def fullRecordGapValue03580 : Nat := fullRecordGapCenterValue - 88498

theorem fullRecordGapTerm03580_eq_value :
    recordGapCenter - 88498 = fullRecordGapValue03580 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03580_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03580 (fullRecordGapValue03580 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03580_not_prime : ¬(recordGapCenter - 88498).Prime := by
  rw [fullRecordGapTerm03580_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03580, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03580_fast_pow_mod_ne_one

def fullRecordGapValue03581 : Nat := fullRecordGapCenterValue - 88414

theorem fullRecordGapTerm03581_eq_value :
    recordGapCenter - 88414 = fullRecordGapValue03581 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03581_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03581 (fullRecordGapValue03581 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03581_not_prime : ¬(recordGapCenter - 88414).Prime := by
  rw [fullRecordGapTerm03581_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03581, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03581_fast_pow_mod_ne_one

def fullRecordGapValue03582 : Nat := fullRecordGapCenterValue - 88402

theorem fullRecordGapTerm03582_eq_value :
    recordGapCenter - 88402 = fullRecordGapValue03582 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03582_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03582 (fullRecordGapValue03582 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03582_not_prime : ¬(recordGapCenter - 88402).Prime := by
  rw [fullRecordGapTerm03582_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03582, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03582_fast_pow_mod_ne_one

def fullRecordGapValue03583 : Nat := fullRecordGapCenterValue - 88342

theorem fullRecordGapTerm03583_eq_value :
    recordGapCenter - 88342 = fullRecordGapValue03583 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03583_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03583 (fullRecordGapValue03583 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03583_not_prime : ¬(recordGapCenter - 88342).Prime := by
  rw [fullRecordGapTerm03583_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03583, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03583_fast_pow_mod_ne_one

def fullRecordGapValue03584 : Nat := fullRecordGapCenterValue - 88042

theorem fullRecordGapTerm03584_eq_value :
    recordGapCenter - 88042 = fullRecordGapValue03584 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03584_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03584 (fullRecordGapValue03584 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03584_not_prime : ¬(recordGapCenter - 88042).Prime := by
  rw [fullRecordGapTerm03584_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03584, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03584_fast_pow_mod_ne_one

end PrimeFactorUnimodality
