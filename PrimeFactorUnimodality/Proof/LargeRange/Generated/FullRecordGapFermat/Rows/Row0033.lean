import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue08193 : Nat := fullRecordGapCenterValue + 483222

theorem fullRecordGapTerm08193_eq_value :
    recordGapCenter + 483222 = fullRecordGapValue08193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08193 (fullRecordGapValue08193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08193_not_prime : ¬(recordGapCenter + 483222).Prime := by
  rw [fullRecordGapTerm08193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08193_fast_pow_mod_ne_one

def fullRecordGapValue08194 : Nat := fullRecordGapCenterValue + 483302

theorem fullRecordGapTerm08194_eq_value :
    recordGapCenter + 483302 = fullRecordGapValue08194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08194 (fullRecordGapValue08194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08194_not_prime : ¬(recordGapCenter + 483302).Prime := by
  rw [fullRecordGapTerm08194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08194_fast_pow_mod_ne_one

def fullRecordGapValue08195 : Nat := fullRecordGapCenterValue + 483326

theorem fullRecordGapTerm08195_eq_value :
    recordGapCenter + 483326 = fullRecordGapValue08195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08195 (fullRecordGapValue08195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08195_not_prime : ¬(recordGapCenter + 483326).Prime := by
  rw [fullRecordGapTerm08195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08195_fast_pow_mod_ne_one

def fullRecordGapValue08196 : Nat := fullRecordGapCenterValue + 483422

theorem fullRecordGapTerm08196_eq_value :
    recordGapCenter + 483422 = fullRecordGapValue08196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08196 (fullRecordGapValue08196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08196_not_prime : ¬(recordGapCenter + 483422).Prime := by
  rw [fullRecordGapTerm08196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08196_fast_pow_mod_ne_one

def fullRecordGapValue08197 : Nat := fullRecordGapCenterValue + 483596

theorem fullRecordGapTerm08197_eq_value :
    recordGapCenter + 483596 = fullRecordGapValue08197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08197 (fullRecordGapValue08197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08197_not_prime : ¬(recordGapCenter + 483596).Prime := by
  rw [fullRecordGapTerm08197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08197_fast_pow_mod_ne_one

def fullRecordGapValue08198 : Nat := fullRecordGapCenterValue + 483618

theorem fullRecordGapTerm08198_eq_value :
    recordGapCenter + 483618 = fullRecordGapValue08198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08198 (fullRecordGapValue08198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08198_not_prime : ¬(recordGapCenter + 483618).Prime := by
  rw [fullRecordGapTerm08198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08198_fast_pow_mod_ne_one

def fullRecordGapValue08199 : Nat := fullRecordGapCenterValue + 483668

theorem fullRecordGapTerm08199_eq_value :
    recordGapCenter + 483668 = fullRecordGapValue08199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08199 (fullRecordGapValue08199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08199_not_prime : ¬(recordGapCenter + 483668).Prime := by
  rw [fullRecordGapTerm08199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08199_fast_pow_mod_ne_one

def fullRecordGapValue08200 : Nat := fullRecordGapCenterValue + 483830

theorem fullRecordGapTerm08200_eq_value :
    recordGapCenter + 483830 = fullRecordGapValue08200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08200 (fullRecordGapValue08200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08200_not_prime : ¬(recordGapCenter + 483830).Prime := by
  rw [fullRecordGapTerm08200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08200_fast_pow_mod_ne_one

def fullRecordGapValue08201 : Nat := fullRecordGapCenterValue + 483840

theorem fullRecordGapTerm08201_eq_value :
    recordGapCenter + 483840 = fullRecordGapValue08201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08201 (fullRecordGapValue08201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08201_not_prime : ¬(recordGapCenter + 483840).Prime := by
  rw [fullRecordGapTerm08201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08201_fast_pow_mod_ne_one

def fullRecordGapValue08202 : Nat := fullRecordGapCenterValue + 483926

theorem fullRecordGapTerm08202_eq_value :
    recordGapCenter + 483926 = fullRecordGapValue08202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08202 (fullRecordGapValue08202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08202_not_prime : ¬(recordGapCenter + 483926).Prime := by
  rw [fullRecordGapTerm08202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08202_fast_pow_mod_ne_one

def fullRecordGapValue08203 : Nat := fullRecordGapCenterValue + 483942

theorem fullRecordGapTerm08203_eq_value :
    recordGapCenter + 483942 = fullRecordGapValue08203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08203 (fullRecordGapValue08203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08203_not_prime : ¬(recordGapCenter + 483942).Prime := by
  rw [fullRecordGapTerm08203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08203_fast_pow_mod_ne_one

def fullRecordGapValue08204 : Nat := fullRecordGapCenterValue + 484026

theorem fullRecordGapTerm08204_eq_value :
    recordGapCenter + 484026 = fullRecordGapValue08204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08204 (fullRecordGapValue08204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08204_not_prime : ¬(recordGapCenter + 484026).Prime := by
  rw [fullRecordGapTerm08204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08204_fast_pow_mod_ne_one

def fullRecordGapValue08205 : Nat := fullRecordGapCenterValue + 484076

theorem fullRecordGapTerm08205_eq_value :
    recordGapCenter + 484076 = fullRecordGapValue08205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08205 (fullRecordGapValue08205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08205_not_prime : ¬(recordGapCenter + 484076).Prime := by
  rw [fullRecordGapTerm08205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08205_fast_pow_mod_ne_one

def fullRecordGapValue08206 : Nat := fullRecordGapCenterValue + 484086

theorem fullRecordGapTerm08206_eq_value :
    recordGapCenter + 484086 = fullRecordGapValue08206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08206 (fullRecordGapValue08206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08206_not_prime : ¬(recordGapCenter + 484086).Prime := by
  rw [fullRecordGapTerm08206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08206_fast_pow_mod_ne_one

def fullRecordGapValue08207 : Nat := fullRecordGapCenterValue + 484166

theorem fullRecordGapTerm08207_eq_value :
    recordGapCenter + 484166 = fullRecordGapValue08207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08207 (fullRecordGapValue08207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08207_not_prime : ¬(recordGapCenter + 484166).Prime := by
  rw [fullRecordGapTerm08207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08207_fast_pow_mod_ne_one

def fullRecordGapValue08208 : Nat := fullRecordGapCenterValue + 484202

theorem fullRecordGapTerm08208_eq_value :
    recordGapCenter + 484202 = fullRecordGapValue08208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08208 (fullRecordGapValue08208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08208_not_prime : ¬(recordGapCenter + 484202).Prime := by
  rw [fullRecordGapTerm08208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08208_fast_pow_mod_ne_one

def fullRecordGapValue08209 : Nat := fullRecordGapCenterValue + 484628

theorem fullRecordGapTerm08209_eq_value :
    recordGapCenter + 484628 = fullRecordGapValue08209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08209 (fullRecordGapValue08209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08209_not_prime : ¬(recordGapCenter + 484628).Prime := by
  rw [fullRecordGapTerm08209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08209_fast_pow_mod_ne_one

def fullRecordGapValue08210 : Nat := fullRecordGapCenterValue + 484712

theorem fullRecordGapTerm08210_eq_value :
    recordGapCenter + 484712 = fullRecordGapValue08210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08210 (fullRecordGapValue08210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08210_not_prime : ¬(recordGapCenter + 484712).Prime := by
  rw [fullRecordGapTerm08210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08210_fast_pow_mod_ne_one

def fullRecordGapValue08211 : Nat := fullRecordGapCenterValue + 484982

theorem fullRecordGapTerm08211_eq_value :
    recordGapCenter + 484982 = fullRecordGapValue08211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08211 (fullRecordGapValue08211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08211_not_prime : ¬(recordGapCenter + 484982).Prime := by
  rw [fullRecordGapTerm08211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08211_fast_pow_mod_ne_one

def fullRecordGapValue08212 : Nat := fullRecordGapCenterValue + 484998

theorem fullRecordGapTerm08212_eq_value :
    recordGapCenter + 484998 = fullRecordGapValue08212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08212 (fullRecordGapValue08212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08212_not_prime : ¬(recordGapCenter + 484998).Prime := by
  rw [fullRecordGapTerm08212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08212_fast_pow_mod_ne_one

def fullRecordGapValue08213 : Nat := fullRecordGapCenterValue + 485018

theorem fullRecordGapTerm08213_eq_value :
    recordGapCenter + 485018 = fullRecordGapValue08213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08213 (fullRecordGapValue08213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08213_not_prime : ¬(recordGapCenter + 485018).Prime := by
  rw [fullRecordGapTerm08213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08213_fast_pow_mod_ne_one

def fullRecordGapValue08214 : Nat := fullRecordGapCenterValue + 485102

theorem fullRecordGapTerm08214_eq_value :
    recordGapCenter + 485102 = fullRecordGapValue08214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08214 (fullRecordGapValue08214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08214_not_prime : ¬(recordGapCenter + 485102).Prime := by
  rw [fullRecordGapTerm08214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08214_fast_pow_mod_ne_one

def fullRecordGapValue08215 : Nat := fullRecordGapCenterValue + 485178

theorem fullRecordGapTerm08215_eq_value :
    recordGapCenter + 485178 = fullRecordGapValue08215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08215 (fullRecordGapValue08215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08215_not_prime : ¬(recordGapCenter + 485178).Prime := by
  rw [fullRecordGapTerm08215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08215_fast_pow_mod_ne_one

def fullRecordGapValue08216 : Nat := fullRecordGapCenterValue + 485252

theorem fullRecordGapTerm08216_eq_value :
    recordGapCenter + 485252 = fullRecordGapValue08216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08216 (fullRecordGapValue08216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08216_not_prime : ¬(recordGapCenter + 485252).Prime := by
  rw [fullRecordGapTerm08216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08216_fast_pow_mod_ne_one

def fullRecordGapValue08217 : Nat := fullRecordGapCenterValue + 485270

theorem fullRecordGapTerm08217_eq_value :
    recordGapCenter + 485270 = fullRecordGapValue08217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08217 (fullRecordGapValue08217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08217_not_prime : ¬(recordGapCenter + 485270).Prime := by
  rw [fullRecordGapTerm08217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08217_fast_pow_mod_ne_one

def fullRecordGapValue08218 : Nat := fullRecordGapCenterValue + 485378

theorem fullRecordGapTerm08218_eq_value :
    recordGapCenter + 485378 = fullRecordGapValue08218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08218 (fullRecordGapValue08218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08218_not_prime : ¬(recordGapCenter + 485378).Prime := by
  rw [fullRecordGapTerm08218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08218_fast_pow_mod_ne_one

def fullRecordGapValue08219 : Nat := fullRecordGapCenterValue + 485390

theorem fullRecordGapTerm08219_eq_value :
    recordGapCenter + 485390 = fullRecordGapValue08219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08219 (fullRecordGapValue08219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08219_not_prime : ¬(recordGapCenter + 485390).Prime := by
  rw [fullRecordGapTerm08219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08219_fast_pow_mod_ne_one

def fullRecordGapValue08220 : Nat := fullRecordGapCenterValue + 485396

theorem fullRecordGapTerm08220_eq_value :
    recordGapCenter + 485396 = fullRecordGapValue08220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08220 (fullRecordGapValue08220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08220_not_prime : ¬(recordGapCenter + 485396).Prime := by
  rw [fullRecordGapTerm08220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08220_fast_pow_mod_ne_one

def fullRecordGapValue08221 : Nat := fullRecordGapCenterValue + 485468

theorem fullRecordGapTerm08221_eq_value :
    recordGapCenter + 485468 = fullRecordGapValue08221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08221 (fullRecordGapValue08221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08221_not_prime : ¬(recordGapCenter + 485468).Prime := by
  rw [fullRecordGapTerm08221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08221_fast_pow_mod_ne_one

def fullRecordGapValue08222 : Nat := fullRecordGapCenterValue + 485516

theorem fullRecordGapTerm08222_eq_value :
    recordGapCenter + 485516 = fullRecordGapValue08222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08222 (fullRecordGapValue08222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08222_not_prime : ¬(recordGapCenter + 485516).Prime := by
  rw [fullRecordGapTerm08222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08222_fast_pow_mod_ne_one

def fullRecordGapValue08223 : Nat := fullRecordGapCenterValue + 485546

theorem fullRecordGapTerm08223_eq_value :
    recordGapCenter + 485546 = fullRecordGapValue08223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08223 (fullRecordGapValue08223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08223_not_prime : ¬(recordGapCenter + 485546).Prime := by
  rw [fullRecordGapTerm08223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08223_fast_pow_mod_ne_one

def fullRecordGapValue08224 : Nat := fullRecordGapCenterValue + 485612

theorem fullRecordGapTerm08224_eq_value :
    recordGapCenter + 485612 = fullRecordGapValue08224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08224 (fullRecordGapValue08224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08224_not_prime : ¬(recordGapCenter + 485612).Prime := by
  rw [fullRecordGapTerm08224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08224_fast_pow_mod_ne_one

def fullRecordGapValue08225 : Nat := fullRecordGapCenterValue + 485846

theorem fullRecordGapTerm08225_eq_value :
    recordGapCenter + 485846 = fullRecordGapValue08225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08225 (fullRecordGapValue08225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08225_not_prime : ¬(recordGapCenter + 485846).Prime := by
  rw [fullRecordGapTerm08225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08225_fast_pow_mod_ne_one

def fullRecordGapValue08226 : Nat := fullRecordGapCenterValue + 485930

theorem fullRecordGapTerm08226_eq_value :
    recordGapCenter + 485930 = fullRecordGapValue08226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08226 (fullRecordGapValue08226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08226_not_prime : ¬(recordGapCenter + 485930).Prime := by
  rw [fullRecordGapTerm08226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08226_fast_pow_mod_ne_one

def fullRecordGapValue08227 : Nat := fullRecordGapCenterValue + 485942

theorem fullRecordGapTerm08227_eq_value :
    recordGapCenter + 485942 = fullRecordGapValue08227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08227 (fullRecordGapValue08227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08227_not_prime : ¬(recordGapCenter + 485942).Prime := by
  rw [fullRecordGapTerm08227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08227_fast_pow_mod_ne_one

def fullRecordGapValue08228 : Nat := fullRecordGapCenterValue + 485948

theorem fullRecordGapTerm08228_eq_value :
    recordGapCenter + 485948 = fullRecordGapValue08228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08228 (fullRecordGapValue08228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08228_not_prime : ¬(recordGapCenter + 485948).Prime := by
  rw [fullRecordGapTerm08228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08228_fast_pow_mod_ne_one

def fullRecordGapValue08229 : Nat := fullRecordGapCenterValue + 485972

theorem fullRecordGapTerm08229_eq_value :
    recordGapCenter + 485972 = fullRecordGapValue08229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08229 (fullRecordGapValue08229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08229_not_prime : ¬(recordGapCenter + 485972).Prime := by
  rw [fullRecordGapTerm08229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08229_fast_pow_mod_ne_one

def fullRecordGapValue08230 : Nat := fullRecordGapCenterValue + 485978

theorem fullRecordGapTerm08230_eq_value :
    recordGapCenter + 485978 = fullRecordGapValue08230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08230 (fullRecordGapValue08230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08230_not_prime : ¬(recordGapCenter + 485978).Prime := by
  rw [fullRecordGapTerm08230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08230_fast_pow_mod_ne_one

def fullRecordGapValue08231 : Nat := fullRecordGapCenterValue + 486000

theorem fullRecordGapTerm08231_eq_value :
    recordGapCenter + 486000 = fullRecordGapValue08231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08231 (fullRecordGapValue08231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08231_not_prime : ¬(recordGapCenter + 486000).Prime := by
  rw [fullRecordGapTerm08231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08231_fast_pow_mod_ne_one

def fullRecordGapValue08232 : Nat := fullRecordGapCenterValue + 486182

theorem fullRecordGapTerm08232_eq_value :
    recordGapCenter + 486182 = fullRecordGapValue08232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08232 (fullRecordGapValue08232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08232_not_prime : ¬(recordGapCenter + 486182).Prime := by
  rw [fullRecordGapTerm08232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08232_fast_pow_mod_ne_one

def fullRecordGapValue08233 : Nat := fullRecordGapCenterValue + 486188

theorem fullRecordGapTerm08233_eq_value :
    recordGapCenter + 486188 = fullRecordGapValue08233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08233 (fullRecordGapValue08233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08233_not_prime : ¬(recordGapCenter + 486188).Prime := by
  rw [fullRecordGapTerm08233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08233_fast_pow_mod_ne_one

def fullRecordGapValue08234 : Nat := fullRecordGapCenterValue + 486236

theorem fullRecordGapTerm08234_eq_value :
    recordGapCenter + 486236 = fullRecordGapValue08234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08234 (fullRecordGapValue08234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08234_not_prime : ¬(recordGapCenter + 486236).Prime := by
  rw [fullRecordGapTerm08234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08234_fast_pow_mod_ne_one

def fullRecordGapValue08235 : Nat := fullRecordGapCenterValue + 486258

theorem fullRecordGapTerm08235_eq_value :
    recordGapCenter + 486258 = fullRecordGapValue08235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08235 (fullRecordGapValue08235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08235_not_prime : ¬(recordGapCenter + 486258).Prime := by
  rw [fullRecordGapTerm08235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08235_fast_pow_mod_ne_one

def fullRecordGapValue08236 : Nat := fullRecordGapCenterValue + 486462

theorem fullRecordGapTerm08236_eq_value :
    recordGapCenter + 486462 = fullRecordGapValue08236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08236 (fullRecordGapValue08236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08236_not_prime : ¬(recordGapCenter + 486462).Prime := by
  rw [fullRecordGapTerm08236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08236_fast_pow_mod_ne_one

def fullRecordGapValue08237 : Nat := fullRecordGapCenterValue + 486488

theorem fullRecordGapTerm08237_eq_value :
    recordGapCenter + 486488 = fullRecordGapValue08237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08237 (fullRecordGapValue08237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08237_not_prime : ¬(recordGapCenter + 486488).Prime := by
  rw [fullRecordGapTerm08237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08237_fast_pow_mod_ne_one

def fullRecordGapValue08238 : Nat := fullRecordGapCenterValue + 486582

theorem fullRecordGapTerm08238_eq_value :
    recordGapCenter + 486582 = fullRecordGapValue08238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08238 (fullRecordGapValue08238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08238_not_prime : ¬(recordGapCenter + 486582).Prime := by
  rw [fullRecordGapTerm08238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08238_fast_pow_mod_ne_one

def fullRecordGapValue08239 : Nat := fullRecordGapCenterValue + 486602

theorem fullRecordGapTerm08239_eq_value :
    recordGapCenter + 486602 = fullRecordGapValue08239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08239 (fullRecordGapValue08239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08239_not_prime : ¬(recordGapCenter + 486602).Prime := by
  rw [fullRecordGapTerm08239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08239_fast_pow_mod_ne_one

def fullRecordGapValue08240 : Nat := fullRecordGapCenterValue + 486606

theorem fullRecordGapTerm08240_eq_value :
    recordGapCenter + 486606 = fullRecordGapValue08240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08240 (fullRecordGapValue08240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08240_not_prime : ¬(recordGapCenter + 486606).Prime := by
  rw [fullRecordGapTerm08240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08240_fast_pow_mod_ne_one

def fullRecordGapValue08241 : Nat := fullRecordGapCenterValue + 486686

theorem fullRecordGapTerm08241_eq_value :
    recordGapCenter + 486686 = fullRecordGapValue08241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08241 (fullRecordGapValue08241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08241_not_prime : ¬(recordGapCenter + 486686).Prime := by
  rw [fullRecordGapTerm08241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08241_fast_pow_mod_ne_one

def fullRecordGapValue08242 : Nat := fullRecordGapCenterValue + 486782

theorem fullRecordGapTerm08242_eq_value :
    recordGapCenter + 486782 = fullRecordGapValue08242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08242 (fullRecordGapValue08242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08242_not_prime : ¬(recordGapCenter + 486782).Prime := by
  rw [fullRecordGapTerm08242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08242_fast_pow_mod_ne_one

def fullRecordGapValue08243 : Nat := fullRecordGapCenterValue + 486788

theorem fullRecordGapTerm08243_eq_value :
    recordGapCenter + 486788 = fullRecordGapValue08243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08243 (fullRecordGapValue08243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08243_not_prime : ¬(recordGapCenter + 486788).Prime := by
  rw [fullRecordGapTerm08243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08243_fast_pow_mod_ne_one

def fullRecordGapValue08244 : Nat := fullRecordGapCenterValue + 486806

theorem fullRecordGapTerm08244_eq_value :
    recordGapCenter + 486806 = fullRecordGapValue08244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08244 (fullRecordGapValue08244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08244_not_prime : ¬(recordGapCenter + 486806).Prime := by
  rw [fullRecordGapTerm08244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08244_fast_pow_mod_ne_one

def fullRecordGapValue08245 : Nat := fullRecordGapCenterValue + 486872

theorem fullRecordGapTerm08245_eq_value :
    recordGapCenter + 486872 = fullRecordGapValue08245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08245 (fullRecordGapValue08245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08245_not_prime : ¬(recordGapCenter + 486872).Prime := by
  rw [fullRecordGapTerm08245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08245_fast_pow_mod_ne_one

def fullRecordGapValue08246 : Nat := fullRecordGapCenterValue + 486942

theorem fullRecordGapTerm08246_eq_value :
    recordGapCenter + 486942 = fullRecordGapValue08246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08246 (fullRecordGapValue08246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08246_not_prime : ¬(recordGapCenter + 486942).Prime := by
  rw [fullRecordGapTerm08246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08246_fast_pow_mod_ne_one

def fullRecordGapValue08247 : Nat := fullRecordGapCenterValue + 487148

theorem fullRecordGapTerm08247_eq_value :
    recordGapCenter + 487148 = fullRecordGapValue08247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08247 (fullRecordGapValue08247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08247_not_prime : ¬(recordGapCenter + 487148).Prime := by
  rw [fullRecordGapTerm08247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08247_fast_pow_mod_ne_one

def fullRecordGapValue08248 : Nat := fullRecordGapCenterValue + 487166

theorem fullRecordGapTerm08248_eq_value :
    recordGapCenter + 487166 = fullRecordGapValue08248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08248 (fullRecordGapValue08248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08248_not_prime : ¬(recordGapCenter + 487166).Prime := by
  rw [fullRecordGapTerm08248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08248_fast_pow_mod_ne_one

def fullRecordGapValue08249 : Nat := fullRecordGapCenterValue + 487218

theorem fullRecordGapTerm08249_eq_value :
    recordGapCenter + 487218 = fullRecordGapValue08249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08249 (fullRecordGapValue08249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08249_not_prime : ¬(recordGapCenter + 487218).Prime := by
  rw [fullRecordGapTerm08249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08249_fast_pow_mod_ne_one

def fullRecordGapValue08250 : Nat := fullRecordGapCenterValue + 487226

theorem fullRecordGapTerm08250_eq_value :
    recordGapCenter + 487226 = fullRecordGapValue08250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08250 (fullRecordGapValue08250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08250_not_prime : ¬(recordGapCenter + 487226).Prime := by
  rw [fullRecordGapTerm08250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08250_fast_pow_mod_ne_one

def fullRecordGapValue08251 : Nat := fullRecordGapCenterValue + 487310

theorem fullRecordGapTerm08251_eq_value :
    recordGapCenter + 487310 = fullRecordGapValue08251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08251 (fullRecordGapValue08251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08251_not_prime : ¬(recordGapCenter + 487310).Prime := by
  rw [fullRecordGapTerm08251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08251_fast_pow_mod_ne_one

def fullRecordGapValue08252 : Nat := fullRecordGapCenterValue + 487338

theorem fullRecordGapTerm08252_eq_value :
    recordGapCenter + 487338 = fullRecordGapValue08252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08252 (fullRecordGapValue08252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08252_not_prime : ¬(recordGapCenter + 487338).Prime := by
  rw [fullRecordGapTerm08252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08252_fast_pow_mod_ne_one

def fullRecordGapValue08253 : Nat := fullRecordGapCenterValue + 487398

theorem fullRecordGapTerm08253_eq_value :
    recordGapCenter + 487398 = fullRecordGapValue08253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08253 (fullRecordGapValue08253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08253_not_prime : ¬(recordGapCenter + 487398).Prime := by
  rw [fullRecordGapTerm08253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08253_fast_pow_mod_ne_one

def fullRecordGapValue08254 : Nat := fullRecordGapCenterValue + 487496

theorem fullRecordGapTerm08254_eq_value :
    recordGapCenter + 487496 = fullRecordGapValue08254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08254 (fullRecordGapValue08254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08254_not_prime : ¬(recordGapCenter + 487496).Prime := by
  rw [fullRecordGapTerm08254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08254_fast_pow_mod_ne_one

def fullRecordGapValue08255 : Nat := fullRecordGapCenterValue + 487688

theorem fullRecordGapTerm08255_eq_value :
    recordGapCenter + 487688 = fullRecordGapValue08255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08255 (fullRecordGapValue08255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08255_not_prime : ¬(recordGapCenter + 487688).Prime := by
  rw [fullRecordGapTerm08255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08255_fast_pow_mod_ne_one

def fullRecordGapValue08256 : Nat := fullRecordGapCenterValue + 487748

theorem fullRecordGapTerm08256_eq_value :
    recordGapCenter + 487748 = fullRecordGapValue08256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08256 (fullRecordGapValue08256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08256_not_prime : ¬(recordGapCenter + 487748).Prime := by
  rw [fullRecordGapTerm08256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08256_fast_pow_mod_ne_one

def fullRecordGapValue08257 : Nat := fullRecordGapCenterValue + 487790

theorem fullRecordGapTerm08257_eq_value :
    recordGapCenter + 487790 = fullRecordGapValue08257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08257 (fullRecordGapValue08257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08257_not_prime : ¬(recordGapCenter + 487790).Prime := by
  rw [fullRecordGapTerm08257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08257_fast_pow_mod_ne_one

def fullRecordGapValue08258 : Nat := fullRecordGapCenterValue + 487796

theorem fullRecordGapTerm08258_eq_value :
    recordGapCenter + 487796 = fullRecordGapValue08258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08258 (fullRecordGapValue08258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08258_not_prime : ¬(recordGapCenter + 487796).Prime := by
  rw [fullRecordGapTerm08258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08258_fast_pow_mod_ne_one

def fullRecordGapValue08259 : Nat := fullRecordGapCenterValue + 487842

theorem fullRecordGapTerm08259_eq_value :
    recordGapCenter + 487842 = fullRecordGapValue08259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08259 (fullRecordGapValue08259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08259_not_prime : ¬(recordGapCenter + 487842).Prime := by
  rw [fullRecordGapTerm08259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08259_fast_pow_mod_ne_one

def fullRecordGapValue08260 : Nat := fullRecordGapCenterValue + 487946

theorem fullRecordGapTerm08260_eq_value :
    recordGapCenter + 487946 = fullRecordGapValue08260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08260 (fullRecordGapValue08260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08260_not_prime : ¬(recordGapCenter + 487946).Prime := by
  rw [fullRecordGapTerm08260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08260_fast_pow_mod_ne_one

def fullRecordGapValue08261 : Nat := fullRecordGapCenterValue + 488090

theorem fullRecordGapTerm08261_eq_value :
    recordGapCenter + 488090 = fullRecordGapValue08261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08261 (fullRecordGapValue08261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08261_not_prime : ¬(recordGapCenter + 488090).Prime := by
  rw [fullRecordGapTerm08261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08261_fast_pow_mod_ne_one

def fullRecordGapValue08262 : Nat := fullRecordGapCenterValue + 488216

theorem fullRecordGapTerm08262_eq_value :
    recordGapCenter + 488216 = fullRecordGapValue08262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08262 (fullRecordGapValue08262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08262_not_prime : ¬(recordGapCenter + 488216).Prime := by
  rw [fullRecordGapTerm08262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08262_fast_pow_mod_ne_one

def fullRecordGapValue08263 : Nat := fullRecordGapCenterValue + 488276

theorem fullRecordGapTerm08263_eq_value :
    recordGapCenter + 488276 = fullRecordGapValue08263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08263 (fullRecordGapValue08263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08263_not_prime : ¬(recordGapCenter + 488276).Prime := by
  rw [fullRecordGapTerm08263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08263_fast_pow_mod_ne_one

def fullRecordGapValue08264 : Nat := fullRecordGapCenterValue + 488282

theorem fullRecordGapTerm08264_eq_value :
    recordGapCenter + 488282 = fullRecordGapValue08264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08264 (fullRecordGapValue08264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08264_not_prime : ¬(recordGapCenter + 488282).Prime := by
  rw [fullRecordGapTerm08264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08264_fast_pow_mod_ne_one

def fullRecordGapValue08265 : Nat := fullRecordGapCenterValue + 488318

theorem fullRecordGapTerm08265_eq_value :
    recordGapCenter + 488318 = fullRecordGapValue08265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08265 (fullRecordGapValue08265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08265_not_prime : ¬(recordGapCenter + 488318).Prime := by
  rw [fullRecordGapTerm08265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08265_fast_pow_mod_ne_one

def fullRecordGapValue08266 : Nat := fullRecordGapCenterValue + 488468

theorem fullRecordGapTerm08266_eq_value :
    recordGapCenter + 488468 = fullRecordGapValue08266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08266 (fullRecordGapValue08266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08266_not_prime : ¬(recordGapCenter + 488468).Prime := by
  rw [fullRecordGapTerm08266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08266_fast_pow_mod_ne_one

def fullRecordGapValue08267 : Nat := fullRecordGapCenterValue + 488526

theorem fullRecordGapTerm08267_eq_value :
    recordGapCenter + 488526 = fullRecordGapValue08267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08267 (fullRecordGapValue08267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08267_not_prime : ¬(recordGapCenter + 488526).Prime := by
  rw [fullRecordGapTerm08267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08267_fast_pow_mod_ne_one

def fullRecordGapValue08268 : Nat := fullRecordGapCenterValue + 488582

theorem fullRecordGapTerm08268_eq_value :
    recordGapCenter + 488582 = fullRecordGapValue08268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08268 (fullRecordGapValue08268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08268_not_prime : ¬(recordGapCenter + 488582).Prime := by
  rw [fullRecordGapTerm08268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08268_fast_pow_mod_ne_one

def fullRecordGapValue08269 : Nat := fullRecordGapCenterValue + 488666

theorem fullRecordGapTerm08269_eq_value :
    recordGapCenter + 488666 = fullRecordGapValue08269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08269 (fullRecordGapValue08269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08269_not_prime : ¬(recordGapCenter + 488666).Prime := by
  rw [fullRecordGapTerm08269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08269_fast_pow_mod_ne_one

def fullRecordGapValue08270 : Nat := fullRecordGapCenterValue + 488678

theorem fullRecordGapTerm08270_eq_value :
    recordGapCenter + 488678 = fullRecordGapValue08270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08270 (fullRecordGapValue08270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08270_not_prime : ¬(recordGapCenter + 488678).Prime := by
  rw [fullRecordGapTerm08270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08270_fast_pow_mod_ne_one

def fullRecordGapValue08271 : Nat := fullRecordGapCenterValue + 488702

theorem fullRecordGapTerm08271_eq_value :
    recordGapCenter + 488702 = fullRecordGapValue08271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08271 (fullRecordGapValue08271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08271_not_prime : ¬(recordGapCenter + 488702).Prime := by
  rw [fullRecordGapTerm08271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08271_fast_pow_mod_ne_one

def fullRecordGapValue08272 : Nat := fullRecordGapCenterValue + 488762

theorem fullRecordGapTerm08272_eq_value :
    recordGapCenter + 488762 = fullRecordGapValue08272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08272 (fullRecordGapValue08272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08272_not_prime : ¬(recordGapCenter + 488762).Prime := by
  rw [fullRecordGapTerm08272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08272_fast_pow_mod_ne_one

def fullRecordGapValue08273 : Nat := fullRecordGapCenterValue + 488786

theorem fullRecordGapTerm08273_eq_value :
    recordGapCenter + 488786 = fullRecordGapValue08273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08273 (fullRecordGapValue08273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08273_not_prime : ¬(recordGapCenter + 488786).Prime := by
  rw [fullRecordGapTerm08273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08273_fast_pow_mod_ne_one

def fullRecordGapValue08274 : Nat := fullRecordGapCenterValue + 488822

theorem fullRecordGapTerm08274_eq_value :
    recordGapCenter + 488822 = fullRecordGapValue08274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08274 (fullRecordGapValue08274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08274_not_prime : ¬(recordGapCenter + 488822).Prime := by
  rw [fullRecordGapTerm08274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08274_fast_pow_mod_ne_one

def fullRecordGapValue08275 : Nat := fullRecordGapCenterValue + 488828

theorem fullRecordGapTerm08275_eq_value :
    recordGapCenter + 488828 = fullRecordGapValue08275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08275 (fullRecordGapValue08275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08275_not_prime : ¬(recordGapCenter + 488828).Prime := by
  rw [fullRecordGapTerm08275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08275_fast_pow_mod_ne_one

def fullRecordGapValue08276 : Nat := fullRecordGapCenterValue + 488876

theorem fullRecordGapTerm08276_eq_value :
    recordGapCenter + 488876 = fullRecordGapValue08276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08276 (fullRecordGapValue08276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08276_not_prime : ¬(recordGapCenter + 488876).Prime := by
  rw [fullRecordGapTerm08276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08276_fast_pow_mod_ne_one

def fullRecordGapValue08277 : Nat := fullRecordGapCenterValue + 489092

theorem fullRecordGapTerm08277_eq_value :
    recordGapCenter + 489092 = fullRecordGapValue08277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08277 (fullRecordGapValue08277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08277_not_prime : ¬(recordGapCenter + 489092).Prime := by
  rw [fullRecordGapTerm08277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08277_fast_pow_mod_ne_one

def fullRecordGapValue08278 : Nat := fullRecordGapCenterValue + 489198

theorem fullRecordGapTerm08278_eq_value :
    recordGapCenter + 489198 = fullRecordGapValue08278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08278 (fullRecordGapValue08278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08278_not_prime : ¬(recordGapCenter + 489198).Prime := by
  rw [fullRecordGapTerm08278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08278_fast_pow_mod_ne_one

def fullRecordGapValue08279 : Nat := fullRecordGapCenterValue + 489282

theorem fullRecordGapTerm08279_eq_value :
    recordGapCenter + 489282 = fullRecordGapValue08279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08279 (fullRecordGapValue08279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08279_not_prime : ¬(recordGapCenter + 489282).Prime := by
  rw [fullRecordGapTerm08279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08279_fast_pow_mod_ne_one

def fullRecordGapValue08280 : Nat := fullRecordGapCenterValue + 489318

theorem fullRecordGapTerm08280_eq_value :
    recordGapCenter + 489318 = fullRecordGapValue08280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08280 (fullRecordGapValue08280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08280_not_prime : ¬(recordGapCenter + 489318).Prime := by
  rw [fullRecordGapTerm08280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08280_fast_pow_mod_ne_one

def fullRecordGapValue08281 : Nat := fullRecordGapCenterValue + 489378

theorem fullRecordGapTerm08281_eq_value :
    recordGapCenter + 489378 = fullRecordGapValue08281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08281 (fullRecordGapValue08281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08281_not_prime : ¬(recordGapCenter + 489378).Prime := by
  rw [fullRecordGapTerm08281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08281_fast_pow_mod_ne_one

def fullRecordGapValue08282 : Nat := fullRecordGapCenterValue + 489506

theorem fullRecordGapTerm08282_eq_value :
    recordGapCenter + 489506 = fullRecordGapValue08282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08282 (fullRecordGapValue08282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08282_not_prime : ¬(recordGapCenter + 489506).Prime := by
  rw [fullRecordGapTerm08282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08282_fast_pow_mod_ne_one

def fullRecordGapValue08283 : Nat := fullRecordGapCenterValue + 489548

theorem fullRecordGapTerm08283_eq_value :
    recordGapCenter + 489548 = fullRecordGapValue08283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08283 (fullRecordGapValue08283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08283_not_prime : ¬(recordGapCenter + 489548).Prime := by
  rw [fullRecordGapTerm08283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08283_fast_pow_mod_ne_one

def fullRecordGapValue08284 : Nat := fullRecordGapCenterValue + 489882

theorem fullRecordGapTerm08284_eq_value :
    recordGapCenter + 489882 = fullRecordGapValue08284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08284 (fullRecordGapValue08284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08284_not_prime : ¬(recordGapCenter + 489882).Prime := by
  rw [fullRecordGapTerm08284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08284_fast_pow_mod_ne_one

def fullRecordGapValue08285 : Nat := fullRecordGapCenterValue + 489890

theorem fullRecordGapTerm08285_eq_value :
    recordGapCenter + 489890 = fullRecordGapValue08285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08285 (fullRecordGapValue08285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08285_not_prime : ¬(recordGapCenter + 489890).Prime := by
  rw [fullRecordGapTerm08285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08285_fast_pow_mod_ne_one

def fullRecordGapValue08286 : Nat := fullRecordGapCenterValue + 490026

theorem fullRecordGapTerm08286_eq_value :
    recordGapCenter + 490026 = fullRecordGapValue08286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08286 (fullRecordGapValue08286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08286_not_prime : ¬(recordGapCenter + 490026).Prime := by
  rw [fullRecordGapTerm08286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08286_fast_pow_mod_ne_one

def fullRecordGapValue08287 : Nat := fullRecordGapCenterValue + 490058

theorem fullRecordGapTerm08287_eq_value :
    recordGapCenter + 490058 = fullRecordGapValue08287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08287 (fullRecordGapValue08287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08287_not_prime : ¬(recordGapCenter + 490058).Prime := by
  rw [fullRecordGapTerm08287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08287_fast_pow_mod_ne_one

def fullRecordGapValue08288 : Nat := fullRecordGapCenterValue + 490206

theorem fullRecordGapTerm08288_eq_value :
    recordGapCenter + 490206 = fullRecordGapValue08288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08288 (fullRecordGapValue08288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08288_not_prime : ¬(recordGapCenter + 490206).Prime := by
  rw [fullRecordGapTerm08288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08288_fast_pow_mod_ne_one

def fullRecordGapValue08289 : Nat := fullRecordGapCenterValue + 490316

theorem fullRecordGapTerm08289_eq_value :
    recordGapCenter + 490316 = fullRecordGapValue08289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08289 (fullRecordGapValue08289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08289_not_prime : ¬(recordGapCenter + 490316).Prime := by
  rw [fullRecordGapTerm08289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08289_fast_pow_mod_ne_one

def fullRecordGapValue08290 : Nat := fullRecordGapCenterValue + 490346

theorem fullRecordGapTerm08290_eq_value :
    recordGapCenter + 490346 = fullRecordGapValue08290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08290 (fullRecordGapValue08290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08290_not_prime : ¬(recordGapCenter + 490346).Prime := by
  rw [fullRecordGapTerm08290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08290_fast_pow_mod_ne_one

def fullRecordGapValue08291 : Nat := fullRecordGapCenterValue + 490362

theorem fullRecordGapTerm08291_eq_value :
    recordGapCenter + 490362 = fullRecordGapValue08291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08291 (fullRecordGapValue08291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08291_not_prime : ¬(recordGapCenter + 490362).Prime := by
  rw [fullRecordGapTerm08291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08291_fast_pow_mod_ne_one

def fullRecordGapValue08292 : Nat := fullRecordGapCenterValue + 490436

theorem fullRecordGapTerm08292_eq_value :
    recordGapCenter + 490436 = fullRecordGapValue08292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08292 (fullRecordGapValue08292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08292_not_prime : ¬(recordGapCenter + 490436).Prime := by
  rw [fullRecordGapTerm08292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08292_fast_pow_mod_ne_one

def fullRecordGapValue08293 : Nat := fullRecordGapCenterValue + 490502

theorem fullRecordGapTerm08293_eq_value :
    recordGapCenter + 490502 = fullRecordGapValue08293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08293 (fullRecordGapValue08293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08293_not_prime : ¬(recordGapCenter + 490502).Prime := by
  rw [fullRecordGapTerm08293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08293_fast_pow_mod_ne_one

def fullRecordGapValue08294 : Nat := fullRecordGapCenterValue + 490598

theorem fullRecordGapTerm08294_eq_value :
    recordGapCenter + 490598 = fullRecordGapValue08294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08294 (fullRecordGapValue08294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08294_not_prime : ¬(recordGapCenter + 490598).Prime := by
  rw [fullRecordGapTerm08294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08294_fast_pow_mod_ne_one

def fullRecordGapValue08295 : Nat := fullRecordGapCenterValue + 490638

theorem fullRecordGapTerm08295_eq_value :
    recordGapCenter + 490638 = fullRecordGapValue08295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08295 (fullRecordGapValue08295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08295_not_prime : ¬(recordGapCenter + 490638).Prime := by
  rw [fullRecordGapTerm08295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08295_fast_pow_mod_ne_one

def fullRecordGapValue08296 : Nat := fullRecordGapCenterValue + 490712

theorem fullRecordGapTerm08296_eq_value :
    recordGapCenter + 490712 = fullRecordGapValue08296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08296 (fullRecordGapValue08296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08296_not_prime : ¬(recordGapCenter + 490712).Prime := by
  rw [fullRecordGapTerm08296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08296_fast_pow_mod_ne_one

def fullRecordGapValue08297 : Nat := fullRecordGapCenterValue + 490766

theorem fullRecordGapTerm08297_eq_value :
    recordGapCenter + 490766 = fullRecordGapValue08297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08297 (fullRecordGapValue08297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08297_not_prime : ¬(recordGapCenter + 490766).Prime := by
  rw [fullRecordGapTerm08297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08297_fast_pow_mod_ne_one

def fullRecordGapValue08298 : Nat := fullRecordGapCenterValue + 490856

theorem fullRecordGapTerm08298_eq_value :
    recordGapCenter + 490856 = fullRecordGapValue08298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08298 (fullRecordGapValue08298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08298_not_prime : ¬(recordGapCenter + 490856).Prime := by
  rw [fullRecordGapTerm08298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08298_fast_pow_mod_ne_one

def fullRecordGapValue08299 : Nat := fullRecordGapCenterValue + 491012

theorem fullRecordGapTerm08299_eq_value :
    recordGapCenter + 491012 = fullRecordGapValue08299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08299 (fullRecordGapValue08299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08299_not_prime : ¬(recordGapCenter + 491012).Prime := by
  rw [fullRecordGapTerm08299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08299_fast_pow_mod_ne_one

def fullRecordGapValue08300 : Nat := fullRecordGapCenterValue + 491030

theorem fullRecordGapTerm08300_eq_value :
    recordGapCenter + 491030 = fullRecordGapValue08300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08300 (fullRecordGapValue08300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08300_not_prime : ¬(recordGapCenter + 491030).Prime := by
  rw [fullRecordGapTerm08300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08300_fast_pow_mod_ne_one

def fullRecordGapValue08301 : Nat := fullRecordGapCenterValue + 491090

theorem fullRecordGapTerm08301_eq_value :
    recordGapCenter + 491090 = fullRecordGapValue08301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08301 (fullRecordGapValue08301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08301_not_prime : ¬(recordGapCenter + 491090).Prime := by
  rw [fullRecordGapTerm08301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08301_fast_pow_mod_ne_one

def fullRecordGapValue08302 : Nat := fullRecordGapCenterValue + 491258

theorem fullRecordGapTerm08302_eq_value :
    recordGapCenter + 491258 = fullRecordGapValue08302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08302 (fullRecordGapValue08302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08302_not_prime : ¬(recordGapCenter + 491258).Prime := by
  rw [fullRecordGapTerm08302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08302_fast_pow_mod_ne_one

def fullRecordGapValue08303 : Nat := fullRecordGapCenterValue + 491298

theorem fullRecordGapTerm08303_eq_value :
    recordGapCenter + 491298 = fullRecordGapValue08303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08303 (fullRecordGapValue08303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08303_not_prime : ¬(recordGapCenter + 491298).Prime := by
  rw [fullRecordGapTerm08303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08303_fast_pow_mod_ne_one

def fullRecordGapValue08304 : Nat := fullRecordGapCenterValue + 491306

theorem fullRecordGapTerm08304_eq_value :
    recordGapCenter + 491306 = fullRecordGapValue08304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08304 (fullRecordGapValue08304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08304_not_prime : ¬(recordGapCenter + 491306).Prime := by
  rw [fullRecordGapTerm08304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08304_fast_pow_mod_ne_one

def fullRecordGapValue08305 : Nat := fullRecordGapCenterValue + 491396

theorem fullRecordGapTerm08305_eq_value :
    recordGapCenter + 491396 = fullRecordGapValue08305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08305 (fullRecordGapValue08305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08305_not_prime : ¬(recordGapCenter + 491396).Prime := by
  rw [fullRecordGapTerm08305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08305_fast_pow_mod_ne_one

def fullRecordGapValue08306 : Nat := fullRecordGapCenterValue + 491528

theorem fullRecordGapTerm08306_eq_value :
    recordGapCenter + 491528 = fullRecordGapValue08306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08306 (fullRecordGapValue08306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08306_not_prime : ¬(recordGapCenter + 491528).Prime := by
  rw [fullRecordGapTerm08306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08306_fast_pow_mod_ne_one

def fullRecordGapValue08307 : Nat := fullRecordGapCenterValue + 491570

theorem fullRecordGapTerm08307_eq_value :
    recordGapCenter + 491570 = fullRecordGapValue08307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08307 (fullRecordGapValue08307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08307_not_prime : ¬(recordGapCenter + 491570).Prime := by
  rw [fullRecordGapTerm08307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08307_fast_pow_mod_ne_one

def fullRecordGapValue08308 : Nat := fullRecordGapCenterValue + 491702

theorem fullRecordGapTerm08308_eq_value :
    recordGapCenter + 491702 = fullRecordGapValue08308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08308 (fullRecordGapValue08308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08308_not_prime : ¬(recordGapCenter + 491702).Prime := by
  rw [fullRecordGapTerm08308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08308_fast_pow_mod_ne_one

def fullRecordGapValue08309 : Nat := fullRecordGapCenterValue + 491726

theorem fullRecordGapTerm08309_eq_value :
    recordGapCenter + 491726 = fullRecordGapValue08309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08309 (fullRecordGapValue08309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08309_not_prime : ¬(recordGapCenter + 491726).Prime := by
  rw [fullRecordGapTerm08309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08309_fast_pow_mod_ne_one

def fullRecordGapValue08310 : Nat := fullRecordGapCenterValue + 491822

theorem fullRecordGapTerm08310_eq_value :
    recordGapCenter + 491822 = fullRecordGapValue08310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08310 (fullRecordGapValue08310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08310_not_prime : ¬(recordGapCenter + 491822).Prime := by
  rw [fullRecordGapTerm08310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08310_fast_pow_mod_ne_one

def fullRecordGapValue08311 : Nat := fullRecordGapCenterValue + 491838

theorem fullRecordGapTerm08311_eq_value :
    recordGapCenter + 491838 = fullRecordGapValue08311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08311 (fullRecordGapValue08311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08311_not_prime : ¬(recordGapCenter + 491838).Prime := by
  rw [fullRecordGapTerm08311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08311_fast_pow_mod_ne_one

def fullRecordGapValue08312 : Nat := fullRecordGapCenterValue + 491930

theorem fullRecordGapTerm08312_eq_value :
    recordGapCenter + 491930 = fullRecordGapValue08312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08312 (fullRecordGapValue08312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08312_not_prime : ¬(recordGapCenter + 491930).Prime := by
  rw [fullRecordGapTerm08312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08312_fast_pow_mod_ne_one

def fullRecordGapValue08313 : Nat := fullRecordGapCenterValue + 492068

theorem fullRecordGapTerm08313_eq_value :
    recordGapCenter + 492068 = fullRecordGapValue08313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08313 (fullRecordGapValue08313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08313_not_prime : ¬(recordGapCenter + 492068).Prime := by
  rw [fullRecordGapTerm08313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08313_fast_pow_mod_ne_one

def fullRecordGapValue08314 : Nat := fullRecordGapCenterValue + 492146

theorem fullRecordGapTerm08314_eq_value :
    recordGapCenter + 492146 = fullRecordGapValue08314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08314 (fullRecordGapValue08314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08314_not_prime : ¬(recordGapCenter + 492146).Prime := by
  rw [fullRecordGapTerm08314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08314_fast_pow_mod_ne_one

def fullRecordGapValue08315 : Nat := fullRecordGapCenterValue + 492186

theorem fullRecordGapTerm08315_eq_value :
    recordGapCenter + 492186 = fullRecordGapValue08315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08315 (fullRecordGapValue08315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08315_not_prime : ¬(recordGapCenter + 492186).Prime := by
  rw [fullRecordGapTerm08315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08315_fast_pow_mod_ne_one

def fullRecordGapValue08316 : Nat := fullRecordGapCenterValue + 492230

theorem fullRecordGapTerm08316_eq_value :
    recordGapCenter + 492230 = fullRecordGapValue08316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08316 (fullRecordGapValue08316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08316_not_prime : ¬(recordGapCenter + 492230).Prime := by
  rw [fullRecordGapTerm08316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08316_fast_pow_mod_ne_one

def fullRecordGapValue08317 : Nat := fullRecordGapCenterValue + 492266

theorem fullRecordGapTerm08317_eq_value :
    recordGapCenter + 492266 = fullRecordGapValue08317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08317 (fullRecordGapValue08317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08317_not_prime : ¬(recordGapCenter + 492266).Prime := by
  rw [fullRecordGapTerm08317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08317_fast_pow_mod_ne_one

def fullRecordGapValue08318 : Nat := fullRecordGapCenterValue + 492306

theorem fullRecordGapTerm08318_eq_value :
    recordGapCenter + 492306 = fullRecordGapValue08318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08318 (fullRecordGapValue08318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08318_not_prime : ¬(recordGapCenter + 492306).Prime := by
  rw [fullRecordGapTerm08318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08318_fast_pow_mod_ne_one

def fullRecordGapValue08319 : Nat := fullRecordGapCenterValue + 492308

theorem fullRecordGapTerm08319_eq_value :
    recordGapCenter + 492308 = fullRecordGapValue08319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08319 (fullRecordGapValue08319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08319_not_prime : ¬(recordGapCenter + 492308).Prime := by
  rw [fullRecordGapTerm08319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08319_fast_pow_mod_ne_one

def fullRecordGapValue08320 : Nat := fullRecordGapCenterValue + 492332

theorem fullRecordGapTerm08320_eq_value :
    recordGapCenter + 492332 = fullRecordGapValue08320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08320 (fullRecordGapValue08320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08320_not_prime : ¬(recordGapCenter + 492332).Prime := by
  rw [fullRecordGapTerm08320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08320_fast_pow_mod_ne_one

def fullRecordGapValue08321 : Nat := fullRecordGapCenterValue + 492438

theorem fullRecordGapTerm08321_eq_value :
    recordGapCenter + 492438 = fullRecordGapValue08321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08321 (fullRecordGapValue08321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08321_not_prime : ¬(recordGapCenter + 492438).Prime := by
  rw [fullRecordGapTerm08321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08321_fast_pow_mod_ne_one

def fullRecordGapValue08322 : Nat := fullRecordGapCenterValue + 492482

theorem fullRecordGapTerm08322_eq_value :
    recordGapCenter + 492482 = fullRecordGapValue08322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08322 (fullRecordGapValue08322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08322_not_prime : ¬(recordGapCenter + 492482).Prime := by
  rw [fullRecordGapTerm08322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08322_fast_pow_mod_ne_one

def fullRecordGapValue08323 : Nat := fullRecordGapCenterValue + 492542

theorem fullRecordGapTerm08323_eq_value :
    recordGapCenter + 492542 = fullRecordGapValue08323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08323 (fullRecordGapValue08323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08323_not_prime : ¬(recordGapCenter + 492542).Prime := by
  rw [fullRecordGapTerm08323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08323_fast_pow_mod_ne_one

def fullRecordGapValue08324 : Nat := fullRecordGapCenterValue + 492782

theorem fullRecordGapTerm08324_eq_value :
    recordGapCenter + 492782 = fullRecordGapValue08324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08324 (fullRecordGapValue08324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08324_not_prime : ¬(recordGapCenter + 492782).Prime := by
  rw [fullRecordGapTerm08324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08324_fast_pow_mod_ne_one

def fullRecordGapValue08325 : Nat := fullRecordGapCenterValue + 492800

theorem fullRecordGapTerm08325_eq_value :
    recordGapCenter + 492800 = fullRecordGapValue08325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08325 (fullRecordGapValue08325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08325_not_prime : ¬(recordGapCenter + 492800).Prime := by
  rw [fullRecordGapTerm08325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08325_fast_pow_mod_ne_one

def fullRecordGapValue08326 : Nat := fullRecordGapCenterValue + 492836

theorem fullRecordGapTerm08326_eq_value :
    recordGapCenter + 492836 = fullRecordGapValue08326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08326 (fullRecordGapValue08326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08326_not_prime : ¬(recordGapCenter + 492836).Prime := by
  rw [fullRecordGapTerm08326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08326_fast_pow_mod_ne_one

def fullRecordGapValue08327 : Nat := fullRecordGapCenterValue + 492846

theorem fullRecordGapTerm08327_eq_value :
    recordGapCenter + 492846 = fullRecordGapValue08327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08327 (fullRecordGapValue08327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08327_not_prime : ¬(recordGapCenter + 492846).Prime := by
  rw [fullRecordGapTerm08327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08327_fast_pow_mod_ne_one

def fullRecordGapValue08328 : Nat := fullRecordGapCenterValue + 492872

theorem fullRecordGapTerm08328_eq_value :
    recordGapCenter + 492872 = fullRecordGapValue08328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08328 (fullRecordGapValue08328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08328_not_prime : ¬(recordGapCenter + 492872).Prime := by
  rw [fullRecordGapTerm08328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08328_fast_pow_mod_ne_one

def fullRecordGapValue08329 : Nat := fullRecordGapCenterValue + 492878

theorem fullRecordGapTerm08329_eq_value :
    recordGapCenter + 492878 = fullRecordGapValue08329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08329 (fullRecordGapValue08329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08329_not_prime : ¬(recordGapCenter + 492878).Prime := by
  rw [fullRecordGapTerm08329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08329_fast_pow_mod_ne_one

def fullRecordGapValue08330 : Nat := fullRecordGapCenterValue + 492956

theorem fullRecordGapTerm08330_eq_value :
    recordGapCenter + 492956 = fullRecordGapValue08330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08330 (fullRecordGapValue08330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08330_not_prime : ¬(recordGapCenter + 492956).Prime := by
  rw [fullRecordGapTerm08330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08330_fast_pow_mod_ne_one

def fullRecordGapValue08331 : Nat := fullRecordGapCenterValue + 493098

theorem fullRecordGapTerm08331_eq_value :
    recordGapCenter + 493098 = fullRecordGapValue08331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08331 (fullRecordGapValue08331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08331_not_prime : ¬(recordGapCenter + 493098).Prime := by
  rw [fullRecordGapTerm08331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08331_fast_pow_mod_ne_one

def fullRecordGapValue08332 : Nat := fullRecordGapCenterValue + 493158

theorem fullRecordGapTerm08332_eq_value :
    recordGapCenter + 493158 = fullRecordGapValue08332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08332 (fullRecordGapValue08332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08332_not_prime : ¬(recordGapCenter + 493158).Prime := by
  rw [fullRecordGapTerm08332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08332_fast_pow_mod_ne_one

def fullRecordGapValue08333 : Nat := fullRecordGapCenterValue + 493242

theorem fullRecordGapTerm08333_eq_value :
    recordGapCenter + 493242 = fullRecordGapValue08333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08333 (fullRecordGapValue08333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08333_not_prime : ¬(recordGapCenter + 493242).Prime := by
  rw [fullRecordGapTerm08333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08333_fast_pow_mod_ne_one

def fullRecordGapValue08334 : Nat := fullRecordGapCenterValue + 493418

theorem fullRecordGapTerm08334_eq_value :
    recordGapCenter + 493418 = fullRecordGapValue08334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08334 (fullRecordGapValue08334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08334_not_prime : ¬(recordGapCenter + 493418).Prime := by
  rw [fullRecordGapTerm08334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08334_fast_pow_mod_ne_one

def fullRecordGapValue08335 : Nat := fullRecordGapCenterValue + 493446

theorem fullRecordGapTerm08335_eq_value :
    recordGapCenter + 493446 = fullRecordGapValue08335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08335 (fullRecordGapValue08335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08335_not_prime : ¬(recordGapCenter + 493446).Prime := by
  rw [fullRecordGapTerm08335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08335_fast_pow_mod_ne_one

def fullRecordGapValue08336 : Nat := fullRecordGapCenterValue + 493448

theorem fullRecordGapTerm08336_eq_value :
    recordGapCenter + 493448 = fullRecordGapValue08336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08336 (fullRecordGapValue08336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08336_not_prime : ¬(recordGapCenter + 493448).Prime := by
  rw [fullRecordGapTerm08336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08336_fast_pow_mod_ne_one

def fullRecordGapValue08337 : Nat := fullRecordGapCenterValue + 493628

theorem fullRecordGapTerm08337_eq_value :
    recordGapCenter + 493628 = fullRecordGapValue08337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08337 (fullRecordGapValue08337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08337_not_prime : ¬(recordGapCenter + 493628).Prime := by
  rw [fullRecordGapTerm08337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08337_fast_pow_mod_ne_one

def fullRecordGapValue08338 : Nat := fullRecordGapCenterValue + 493670

theorem fullRecordGapTerm08338_eq_value :
    recordGapCenter + 493670 = fullRecordGapValue08338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08338 (fullRecordGapValue08338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08338_not_prime : ¬(recordGapCenter + 493670).Prime := by
  rw [fullRecordGapTerm08338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08338_fast_pow_mod_ne_one

def fullRecordGapValue08339 : Nat := fullRecordGapCenterValue + 493806

theorem fullRecordGapTerm08339_eq_value :
    recordGapCenter + 493806 = fullRecordGapValue08339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08339 (fullRecordGapValue08339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08339_not_prime : ¬(recordGapCenter + 493806).Prime := by
  rw [fullRecordGapTerm08339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08339_fast_pow_mod_ne_one

def fullRecordGapValue08340 : Nat := fullRecordGapCenterValue + 493832

theorem fullRecordGapTerm08340_eq_value :
    recordGapCenter + 493832 = fullRecordGapValue08340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08340 (fullRecordGapValue08340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08340_not_prime : ¬(recordGapCenter + 493832).Prime := by
  rw [fullRecordGapTerm08340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08340_fast_pow_mod_ne_one

def fullRecordGapValue08341 : Nat := fullRecordGapCenterValue + 493838

theorem fullRecordGapTerm08341_eq_value :
    recordGapCenter + 493838 = fullRecordGapValue08341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08341 (fullRecordGapValue08341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08341_not_prime : ¬(recordGapCenter + 493838).Prime := by
  rw [fullRecordGapTerm08341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08341_fast_pow_mod_ne_one

def fullRecordGapValue08342 : Nat := fullRecordGapCenterValue + 493958

theorem fullRecordGapTerm08342_eq_value :
    recordGapCenter + 493958 = fullRecordGapValue08342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08342 (fullRecordGapValue08342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08342_not_prime : ¬(recordGapCenter + 493958).Prime := by
  rw [fullRecordGapTerm08342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08342_fast_pow_mod_ne_one

def fullRecordGapValue08343 : Nat := fullRecordGapCenterValue + 494198

theorem fullRecordGapTerm08343_eq_value :
    recordGapCenter + 494198 = fullRecordGapValue08343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08343 (fullRecordGapValue08343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08343_not_prime : ¬(recordGapCenter + 494198).Prime := by
  rw [fullRecordGapTerm08343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08343_fast_pow_mod_ne_one

def fullRecordGapValue08344 : Nat := fullRecordGapCenterValue + 494282

theorem fullRecordGapTerm08344_eq_value :
    recordGapCenter + 494282 = fullRecordGapValue08344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08344 (fullRecordGapValue08344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08344_not_prime : ¬(recordGapCenter + 494282).Prime := by
  rw [fullRecordGapTerm08344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08344_fast_pow_mod_ne_one

def fullRecordGapValue08345 : Nat := fullRecordGapCenterValue + 494322

theorem fullRecordGapTerm08345_eq_value :
    recordGapCenter + 494322 = fullRecordGapValue08345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08345 (fullRecordGapValue08345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08345_not_prime : ¬(recordGapCenter + 494322).Prime := by
  rw [fullRecordGapTerm08345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08345_fast_pow_mod_ne_one

def fullRecordGapValue08346 : Nat := fullRecordGapCenterValue + 494330

theorem fullRecordGapTerm08346_eq_value :
    recordGapCenter + 494330 = fullRecordGapValue08346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08346 (fullRecordGapValue08346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08346_not_prime : ¬(recordGapCenter + 494330).Prime := by
  rw [fullRecordGapTerm08346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08346_fast_pow_mod_ne_one

def fullRecordGapValue08347 : Nat := fullRecordGapCenterValue + 494366

theorem fullRecordGapTerm08347_eq_value :
    recordGapCenter + 494366 = fullRecordGapValue08347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08347 (fullRecordGapValue08347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08347_not_prime : ¬(recordGapCenter + 494366).Prime := by
  rw [fullRecordGapTerm08347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08347_fast_pow_mod_ne_one

def fullRecordGapValue08348 : Nat := fullRecordGapCenterValue + 494618

theorem fullRecordGapTerm08348_eq_value :
    recordGapCenter + 494618 = fullRecordGapValue08348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08348 (fullRecordGapValue08348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08348_not_prime : ¬(recordGapCenter + 494618).Prime := by
  rw [fullRecordGapTerm08348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08348_fast_pow_mod_ne_one

def fullRecordGapValue08349 : Nat := fullRecordGapCenterValue + 494630

theorem fullRecordGapTerm08349_eq_value :
    recordGapCenter + 494630 = fullRecordGapValue08349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08349 (fullRecordGapValue08349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08349_not_prime : ¬(recordGapCenter + 494630).Prime := by
  rw [fullRecordGapTerm08349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08349_fast_pow_mod_ne_one

def fullRecordGapValue08350 : Nat := fullRecordGapCenterValue + 494762

theorem fullRecordGapTerm08350_eq_value :
    recordGapCenter + 494762 = fullRecordGapValue08350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08350 (fullRecordGapValue08350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08350_not_prime : ¬(recordGapCenter + 494762).Prime := by
  rw [fullRecordGapTerm08350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08350_fast_pow_mod_ne_one

def fullRecordGapValue08351 : Nat := fullRecordGapCenterValue + 494828

theorem fullRecordGapTerm08351_eq_value :
    recordGapCenter + 494828 = fullRecordGapValue08351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08351 (fullRecordGapValue08351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08351_not_prime : ¬(recordGapCenter + 494828).Prime := by
  rw [fullRecordGapTerm08351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08351_fast_pow_mod_ne_one

def fullRecordGapValue08352 : Nat := fullRecordGapCenterValue + 494898

theorem fullRecordGapTerm08352_eq_value :
    recordGapCenter + 494898 = fullRecordGapValue08352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08352 (fullRecordGapValue08352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08352_not_prime : ¬(recordGapCenter + 494898).Prime := by
  rw [fullRecordGapTerm08352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08352_fast_pow_mod_ne_one

def fullRecordGapValue08353 : Nat := fullRecordGapCenterValue + 495000

theorem fullRecordGapTerm08353_eq_value :
    recordGapCenter + 495000 = fullRecordGapValue08353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08353 (fullRecordGapValue08353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08353_not_prime : ¬(recordGapCenter + 495000).Prime := by
  rw [fullRecordGapTerm08353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08353_fast_pow_mod_ne_one

def fullRecordGapValue08354 : Nat := fullRecordGapCenterValue + 495038

theorem fullRecordGapTerm08354_eq_value :
    recordGapCenter + 495038 = fullRecordGapValue08354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08354 (fullRecordGapValue08354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08354_not_prime : ¬(recordGapCenter + 495038).Prime := by
  rw [fullRecordGapTerm08354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08354_fast_pow_mod_ne_one

def fullRecordGapValue08355 : Nat := fullRecordGapCenterValue + 495182

theorem fullRecordGapTerm08355_eq_value :
    recordGapCenter + 495182 = fullRecordGapValue08355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08355 (fullRecordGapValue08355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08355_not_prime : ¬(recordGapCenter + 495182).Prime := by
  rw [fullRecordGapTerm08355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08355_fast_pow_mod_ne_one

def fullRecordGapValue08356 : Nat := fullRecordGapCenterValue + 495206

theorem fullRecordGapTerm08356_eq_value :
    recordGapCenter + 495206 = fullRecordGapValue08356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08356 (fullRecordGapValue08356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08356_not_prime : ¬(recordGapCenter + 495206).Prime := by
  rw [fullRecordGapTerm08356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08356_fast_pow_mod_ne_one

def fullRecordGapValue08357 : Nat := fullRecordGapCenterValue + 495218

theorem fullRecordGapTerm08357_eq_value :
    recordGapCenter + 495218 = fullRecordGapValue08357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08357 (fullRecordGapValue08357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08357_not_prime : ¬(recordGapCenter + 495218).Prime := by
  rw [fullRecordGapTerm08357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08357_fast_pow_mod_ne_one

def fullRecordGapValue08358 : Nat := fullRecordGapCenterValue + 495230

theorem fullRecordGapTerm08358_eq_value :
    recordGapCenter + 495230 = fullRecordGapValue08358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08358 (fullRecordGapValue08358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08358_not_prime : ¬(recordGapCenter + 495230).Prime := by
  rw [fullRecordGapTerm08358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08358_fast_pow_mod_ne_one

def fullRecordGapValue08359 : Nat := fullRecordGapCenterValue + 495272

theorem fullRecordGapTerm08359_eq_value :
    recordGapCenter + 495272 = fullRecordGapValue08359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08359 (fullRecordGapValue08359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08359_not_prime : ¬(recordGapCenter + 495272).Prime := by
  rw [fullRecordGapTerm08359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08359_fast_pow_mod_ne_one

def fullRecordGapValue08360 : Nat := fullRecordGapCenterValue + 495290

theorem fullRecordGapTerm08360_eq_value :
    recordGapCenter + 495290 = fullRecordGapValue08360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08360 (fullRecordGapValue08360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08360_not_prime : ¬(recordGapCenter + 495290).Prime := by
  rw [fullRecordGapTerm08360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08360_fast_pow_mod_ne_one

def fullRecordGapValue08361 : Nat := fullRecordGapCenterValue + 495302

theorem fullRecordGapTerm08361_eq_value :
    recordGapCenter + 495302 = fullRecordGapValue08361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08361 (fullRecordGapValue08361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08361_not_prime : ¬(recordGapCenter + 495302).Prime := by
  rw [fullRecordGapTerm08361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08361_fast_pow_mod_ne_one

def fullRecordGapValue08362 : Nat := fullRecordGapCenterValue + 495332

theorem fullRecordGapTerm08362_eq_value :
    recordGapCenter + 495332 = fullRecordGapValue08362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08362 (fullRecordGapValue08362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08362_not_prime : ¬(recordGapCenter + 495332).Prime := by
  rw [fullRecordGapTerm08362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08362_fast_pow_mod_ne_one

def fullRecordGapValue08363 : Nat := fullRecordGapCenterValue + 495386

theorem fullRecordGapTerm08363_eq_value :
    recordGapCenter + 495386 = fullRecordGapValue08363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08363 (fullRecordGapValue08363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08363_not_prime : ¬(recordGapCenter + 495386).Prime := by
  rw [fullRecordGapTerm08363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08363_fast_pow_mod_ne_one

def fullRecordGapValue08364 : Nat := fullRecordGapCenterValue + 495402

theorem fullRecordGapTerm08364_eq_value :
    recordGapCenter + 495402 = fullRecordGapValue08364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08364 (fullRecordGapValue08364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08364_not_prime : ¬(recordGapCenter + 495402).Prime := by
  rw [fullRecordGapTerm08364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08364_fast_pow_mod_ne_one

def fullRecordGapValue08365 : Nat := fullRecordGapCenterValue + 495426

theorem fullRecordGapTerm08365_eq_value :
    recordGapCenter + 495426 = fullRecordGapValue08365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08365 (fullRecordGapValue08365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08365_not_prime : ¬(recordGapCenter + 495426).Prime := by
  rw [fullRecordGapTerm08365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08365_fast_pow_mod_ne_one

def fullRecordGapValue08366 : Nat := fullRecordGapCenterValue + 495692

theorem fullRecordGapTerm08366_eq_value :
    recordGapCenter + 495692 = fullRecordGapValue08366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08366 (fullRecordGapValue08366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08366_not_prime : ¬(recordGapCenter + 495692).Prime := by
  rw [fullRecordGapTerm08366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08366_fast_pow_mod_ne_one

def fullRecordGapValue08367 : Nat := fullRecordGapCenterValue + 495758

theorem fullRecordGapTerm08367_eq_value :
    recordGapCenter + 495758 = fullRecordGapValue08367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08367 (fullRecordGapValue08367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08367_not_prime : ¬(recordGapCenter + 495758).Prime := by
  rw [fullRecordGapTerm08367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08367_fast_pow_mod_ne_one

def fullRecordGapValue08368 : Nat := fullRecordGapCenterValue + 495798

theorem fullRecordGapTerm08368_eq_value :
    recordGapCenter + 495798 = fullRecordGapValue08368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08368 (fullRecordGapValue08368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08368_not_prime : ¬(recordGapCenter + 495798).Prime := by
  rw [fullRecordGapTerm08368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08368_fast_pow_mod_ne_one

def fullRecordGapValue08369 : Nat := fullRecordGapCenterValue + 495848

theorem fullRecordGapTerm08369_eq_value :
    recordGapCenter + 495848 = fullRecordGapValue08369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08369 (fullRecordGapValue08369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08369_not_prime : ¬(recordGapCenter + 495848).Prime := by
  rw [fullRecordGapTerm08369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08369_fast_pow_mod_ne_one

def fullRecordGapValue08370 : Nat := fullRecordGapCenterValue + 496130

theorem fullRecordGapTerm08370_eq_value :
    recordGapCenter + 496130 = fullRecordGapValue08370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08370 (fullRecordGapValue08370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08370_not_prime : ¬(recordGapCenter + 496130).Prime := by
  rw [fullRecordGapTerm08370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08370_fast_pow_mod_ne_one

def fullRecordGapValue08371 : Nat := fullRecordGapCenterValue + 496142

theorem fullRecordGapTerm08371_eq_value :
    recordGapCenter + 496142 = fullRecordGapValue08371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08371 (fullRecordGapValue08371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08371_not_prime : ¬(recordGapCenter + 496142).Prime := by
  rw [fullRecordGapTerm08371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08371_fast_pow_mod_ne_one

def fullRecordGapValue08372 : Nat := fullRecordGapCenterValue + 496178

theorem fullRecordGapTerm08372_eq_value :
    recordGapCenter + 496178 = fullRecordGapValue08372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08372 (fullRecordGapValue08372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08372_not_prime : ¬(recordGapCenter + 496178).Prime := by
  rw [fullRecordGapTerm08372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08372_fast_pow_mod_ne_one

def fullRecordGapValue08373 : Nat := fullRecordGapCenterValue + 496238

theorem fullRecordGapTerm08373_eq_value :
    recordGapCenter + 496238 = fullRecordGapValue08373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08373 (fullRecordGapValue08373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08373_not_prime : ¬(recordGapCenter + 496238).Prime := by
  rw [fullRecordGapTerm08373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08373_fast_pow_mod_ne_one

def fullRecordGapValue08374 : Nat := fullRecordGapCenterValue + 496268

theorem fullRecordGapTerm08374_eq_value :
    recordGapCenter + 496268 = fullRecordGapValue08374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08374 (fullRecordGapValue08374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08374_not_prime : ¬(recordGapCenter + 496268).Prime := by
  rw [fullRecordGapTerm08374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08374_fast_pow_mod_ne_one

def fullRecordGapValue08375 : Nat := fullRecordGapCenterValue + 496326

theorem fullRecordGapTerm08375_eq_value :
    recordGapCenter + 496326 = fullRecordGapValue08375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08375 (fullRecordGapValue08375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08375_not_prime : ¬(recordGapCenter + 496326).Prime := by
  rw [fullRecordGapTerm08375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08375_fast_pow_mod_ne_one

def fullRecordGapValue08376 : Nat := fullRecordGapCenterValue + 496358

theorem fullRecordGapTerm08376_eq_value :
    recordGapCenter + 496358 = fullRecordGapValue08376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08376 (fullRecordGapValue08376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08376_not_prime : ¬(recordGapCenter + 496358).Prime := by
  rw [fullRecordGapTerm08376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08376_fast_pow_mod_ne_one

def fullRecordGapValue08377 : Nat := fullRecordGapCenterValue + 496406

theorem fullRecordGapTerm08377_eq_value :
    recordGapCenter + 496406 = fullRecordGapValue08377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08377 (fullRecordGapValue08377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08377_not_prime : ¬(recordGapCenter + 496406).Prime := by
  rw [fullRecordGapTerm08377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08377_fast_pow_mod_ne_one

def fullRecordGapValue08378 : Nat := fullRecordGapCenterValue + 496532

theorem fullRecordGapTerm08378_eq_value :
    recordGapCenter + 496532 = fullRecordGapValue08378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08378 (fullRecordGapValue08378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08378_not_prime : ¬(recordGapCenter + 496532).Prime := by
  rw [fullRecordGapTerm08378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08378_fast_pow_mod_ne_one

def fullRecordGapValue08379 : Nat := fullRecordGapCenterValue + 496542

theorem fullRecordGapTerm08379_eq_value :
    recordGapCenter + 496542 = fullRecordGapValue08379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08379 (fullRecordGapValue08379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08379_not_prime : ¬(recordGapCenter + 496542).Prime := by
  rw [fullRecordGapTerm08379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08379_fast_pow_mod_ne_one

def fullRecordGapValue08380 : Nat := fullRecordGapCenterValue + 496556

theorem fullRecordGapTerm08380_eq_value :
    recordGapCenter + 496556 = fullRecordGapValue08380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08380 (fullRecordGapValue08380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08380_not_prime : ¬(recordGapCenter + 496556).Prime := by
  rw [fullRecordGapTerm08380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08380_fast_pow_mod_ne_one

def fullRecordGapValue08381 : Nat := fullRecordGapCenterValue + 496568

theorem fullRecordGapTerm08381_eq_value :
    recordGapCenter + 496568 = fullRecordGapValue08381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08381 (fullRecordGapValue08381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08381_not_prime : ¬(recordGapCenter + 496568).Prime := by
  rw [fullRecordGapTerm08381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08381_fast_pow_mod_ne_one

def fullRecordGapValue08382 : Nat := fullRecordGapCenterValue + 496598

theorem fullRecordGapTerm08382_eq_value :
    recordGapCenter + 496598 = fullRecordGapValue08382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08382 (fullRecordGapValue08382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08382_not_prime : ¬(recordGapCenter + 496598).Prime := by
  rw [fullRecordGapTerm08382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08382_fast_pow_mod_ne_one

def fullRecordGapValue08383 : Nat := fullRecordGapCenterValue + 496722

theorem fullRecordGapTerm08383_eq_value :
    recordGapCenter + 496722 = fullRecordGapValue08383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08383 (fullRecordGapValue08383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08383_not_prime : ¬(recordGapCenter + 496722).Prime := by
  rw [fullRecordGapTerm08383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08383_fast_pow_mod_ne_one

def fullRecordGapValue08384 : Nat := fullRecordGapCenterValue + 496802

theorem fullRecordGapTerm08384_eq_value :
    recordGapCenter + 496802 = fullRecordGapValue08384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08384 (fullRecordGapValue08384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08384_not_prime : ¬(recordGapCenter + 496802).Prime := by
  rw [fullRecordGapTerm08384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08384_fast_pow_mod_ne_one

def fullRecordGapValue08385 : Nat := fullRecordGapCenterValue + 497066

theorem fullRecordGapTerm08385_eq_value :
    recordGapCenter + 497066 = fullRecordGapValue08385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08385 (fullRecordGapValue08385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08385_not_prime : ¬(recordGapCenter + 497066).Prime := by
  rw [fullRecordGapTerm08385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08385_fast_pow_mod_ne_one

def fullRecordGapValue08386 : Nat := fullRecordGapCenterValue + 497298

theorem fullRecordGapTerm08386_eq_value :
    recordGapCenter + 497298 = fullRecordGapValue08386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08386 (fullRecordGapValue08386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08386_not_prime : ¬(recordGapCenter + 497298).Prime := by
  rw [fullRecordGapTerm08386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08386_fast_pow_mod_ne_one

def fullRecordGapValue08387 : Nat := fullRecordGapCenterValue + 497348

theorem fullRecordGapTerm08387_eq_value :
    recordGapCenter + 497348 = fullRecordGapValue08387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08387 (fullRecordGapValue08387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08387_not_prime : ¬(recordGapCenter + 497348).Prime := by
  rw [fullRecordGapTerm08387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08387_fast_pow_mod_ne_one

def fullRecordGapValue08388 : Nat := fullRecordGapCenterValue + 497390

theorem fullRecordGapTerm08388_eq_value :
    recordGapCenter + 497390 = fullRecordGapValue08388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08388 (fullRecordGapValue08388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08388_not_prime : ¬(recordGapCenter + 497390).Prime := by
  rw [fullRecordGapTerm08388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08388_fast_pow_mod_ne_one

def fullRecordGapValue08389 : Nat := fullRecordGapCenterValue + 497418

theorem fullRecordGapTerm08389_eq_value :
    recordGapCenter + 497418 = fullRecordGapValue08389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08389 (fullRecordGapValue08389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08389_not_prime : ¬(recordGapCenter + 497418).Prime := by
  rw [fullRecordGapTerm08389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08389_fast_pow_mod_ne_one

def fullRecordGapValue08390 : Nat := fullRecordGapCenterValue + 497498

theorem fullRecordGapTerm08390_eq_value :
    recordGapCenter + 497498 = fullRecordGapValue08390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08390 (fullRecordGapValue08390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08390_not_prime : ¬(recordGapCenter + 497498).Prime := by
  rw [fullRecordGapTerm08390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08390_fast_pow_mod_ne_one

def fullRecordGapValue08391 : Nat := fullRecordGapCenterValue + 497732

theorem fullRecordGapTerm08391_eq_value :
    recordGapCenter + 497732 = fullRecordGapValue08391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08391 (fullRecordGapValue08391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08391_not_prime : ¬(recordGapCenter + 497732).Prime := by
  rw [fullRecordGapTerm08391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08391_fast_pow_mod_ne_one

def fullRecordGapValue08392 : Nat := fullRecordGapCenterValue + 497738

theorem fullRecordGapTerm08392_eq_value :
    recordGapCenter + 497738 = fullRecordGapValue08392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08392 (fullRecordGapValue08392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08392_not_prime : ¬(recordGapCenter + 497738).Prime := by
  rw [fullRecordGapTerm08392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08392_fast_pow_mod_ne_one

def fullRecordGapValue08393 : Nat := fullRecordGapCenterValue + 497786

theorem fullRecordGapTerm08393_eq_value :
    recordGapCenter + 497786 = fullRecordGapValue08393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08393 (fullRecordGapValue08393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08393_not_prime : ¬(recordGapCenter + 497786).Prime := by
  rw [fullRecordGapTerm08393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08393_fast_pow_mod_ne_one

def fullRecordGapValue08394 : Nat := fullRecordGapCenterValue + 497870

theorem fullRecordGapTerm08394_eq_value :
    recordGapCenter + 497870 = fullRecordGapValue08394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08394 (fullRecordGapValue08394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08394_not_prime : ¬(recordGapCenter + 497870).Prime := by
  rw [fullRecordGapTerm08394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08394_fast_pow_mod_ne_one

def fullRecordGapValue08395 : Nat := fullRecordGapCenterValue + 498036

theorem fullRecordGapTerm08395_eq_value :
    recordGapCenter + 498036 = fullRecordGapValue08395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08395 (fullRecordGapValue08395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08395_not_prime : ¬(recordGapCenter + 498036).Prime := by
  rw [fullRecordGapTerm08395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08395_fast_pow_mod_ne_one

def fullRecordGapValue08396 : Nat := fullRecordGapCenterValue + 498282

theorem fullRecordGapTerm08396_eq_value :
    recordGapCenter + 498282 = fullRecordGapValue08396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08396 (fullRecordGapValue08396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08396_not_prime : ¬(recordGapCenter + 498282).Prime := by
  rw [fullRecordGapTerm08396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08396_fast_pow_mod_ne_one

def fullRecordGapValue08397 : Nat := fullRecordGapCenterValue + 498398

theorem fullRecordGapTerm08397_eq_value :
    recordGapCenter + 498398 = fullRecordGapValue08397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08397 (fullRecordGapValue08397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08397_not_prime : ¬(recordGapCenter + 498398).Prime := by
  rw [fullRecordGapTerm08397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08397_fast_pow_mod_ne_one

def fullRecordGapValue08398 : Nat := fullRecordGapCenterValue + 498558

theorem fullRecordGapTerm08398_eq_value :
    recordGapCenter + 498558 = fullRecordGapValue08398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08398 (fullRecordGapValue08398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08398_not_prime : ¬(recordGapCenter + 498558).Prime := by
  rw [fullRecordGapTerm08398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08398_fast_pow_mod_ne_one

def fullRecordGapValue08399 : Nat := fullRecordGapCenterValue + 498572

theorem fullRecordGapTerm08399_eq_value :
    recordGapCenter + 498572 = fullRecordGapValue08399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08399 (fullRecordGapValue08399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08399_not_prime : ¬(recordGapCenter + 498572).Prime := by
  rw [fullRecordGapTerm08399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08399_fast_pow_mod_ne_one

def fullRecordGapValue08400 : Nat := fullRecordGapCenterValue + 498702

theorem fullRecordGapTerm08400_eq_value :
    recordGapCenter + 498702 = fullRecordGapValue08400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08400 (fullRecordGapValue08400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08400_not_prime : ¬(recordGapCenter + 498702).Prime := by
  rw [fullRecordGapTerm08400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08400_fast_pow_mod_ne_one

def fullRecordGapValue08401 : Nat := fullRecordGapCenterValue + 498716

theorem fullRecordGapTerm08401_eq_value :
    recordGapCenter + 498716 = fullRecordGapValue08401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08401 (fullRecordGapValue08401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08401_not_prime : ¬(recordGapCenter + 498716).Prime := by
  rw [fullRecordGapTerm08401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08401_fast_pow_mod_ne_one

def fullRecordGapValue08402 : Nat := fullRecordGapCenterValue + 498776

theorem fullRecordGapTerm08402_eq_value :
    recordGapCenter + 498776 = fullRecordGapValue08402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08402 (fullRecordGapValue08402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08402_not_prime : ¬(recordGapCenter + 498776).Prime := by
  rw [fullRecordGapTerm08402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08402_fast_pow_mod_ne_one

def fullRecordGapValue08403 : Nat := fullRecordGapCenterValue + 498842

theorem fullRecordGapTerm08403_eq_value :
    recordGapCenter + 498842 = fullRecordGapValue08403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08403 (fullRecordGapValue08403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08403_not_prime : ¬(recordGapCenter + 498842).Prime := by
  rw [fullRecordGapTerm08403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08403_fast_pow_mod_ne_one

def fullRecordGapValue08404 : Nat := fullRecordGapCenterValue + 498878

theorem fullRecordGapTerm08404_eq_value :
    recordGapCenter + 498878 = fullRecordGapValue08404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08404 (fullRecordGapValue08404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08404_not_prime : ¬(recordGapCenter + 498878).Prime := by
  rw [fullRecordGapTerm08404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08404_fast_pow_mod_ne_one

def fullRecordGapValue08405 : Nat := fullRecordGapCenterValue + 499178

theorem fullRecordGapTerm08405_eq_value :
    recordGapCenter + 499178 = fullRecordGapValue08405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08405 (fullRecordGapValue08405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08405_not_prime : ¬(recordGapCenter + 499178).Prime := by
  rw [fullRecordGapTerm08405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08405_fast_pow_mod_ne_one

def fullRecordGapValue08406 : Nat := fullRecordGapCenterValue + 499370

theorem fullRecordGapTerm08406_eq_value :
    recordGapCenter + 499370 = fullRecordGapValue08406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08406 (fullRecordGapValue08406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08406_not_prime : ¬(recordGapCenter + 499370).Prime := by
  rw [fullRecordGapTerm08406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08406_fast_pow_mod_ne_one

def fullRecordGapValue08407 : Nat := fullRecordGapCenterValue + 499412

theorem fullRecordGapTerm08407_eq_value :
    recordGapCenter + 499412 = fullRecordGapValue08407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08407 (fullRecordGapValue08407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08407_not_prime : ¬(recordGapCenter + 499412).Prime := by
  rw [fullRecordGapTerm08407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08407_fast_pow_mod_ne_one

def fullRecordGapValue08408 : Nat := fullRecordGapCenterValue + 499430

theorem fullRecordGapTerm08408_eq_value :
    recordGapCenter + 499430 = fullRecordGapValue08408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08408 (fullRecordGapValue08408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08408_not_prime : ¬(recordGapCenter + 499430).Prime := by
  rw [fullRecordGapTerm08408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08408_fast_pow_mod_ne_one

def fullRecordGapValue08409 : Nat := fullRecordGapCenterValue + 499542

theorem fullRecordGapTerm08409_eq_value :
    recordGapCenter + 499542 = fullRecordGapValue08409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08409 (fullRecordGapValue08409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08409_not_prime : ¬(recordGapCenter + 499542).Prime := by
  rw [fullRecordGapTerm08409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08409_fast_pow_mod_ne_one

def fullRecordGapValue08410 : Nat := fullRecordGapCenterValue + 499602

theorem fullRecordGapTerm08410_eq_value :
    recordGapCenter + 499602 = fullRecordGapValue08410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08410 (fullRecordGapValue08410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08410_not_prime : ¬(recordGapCenter + 499602).Prime := by
  rw [fullRecordGapTerm08410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08410_fast_pow_mod_ne_one

def fullRecordGapValue08411 : Nat := fullRecordGapCenterValue + 499676

theorem fullRecordGapTerm08411_eq_value :
    recordGapCenter + 499676 = fullRecordGapValue08411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08411 (fullRecordGapValue08411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08411_not_prime : ¬(recordGapCenter + 499676).Prime := by
  rw [fullRecordGapTerm08411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08411_fast_pow_mod_ne_one

def fullRecordGapValue08412 : Nat := fullRecordGapCenterValue + 499706

theorem fullRecordGapTerm08412_eq_value :
    recordGapCenter + 499706 = fullRecordGapValue08412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08412 (fullRecordGapValue08412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08412_not_prime : ¬(recordGapCenter + 499706).Prime := by
  rw [fullRecordGapTerm08412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08412_fast_pow_mod_ne_one

def fullRecordGapValue08413 : Nat := fullRecordGapCenterValue + 499866

theorem fullRecordGapTerm08413_eq_value :
    recordGapCenter + 499866 = fullRecordGapValue08413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08413 (fullRecordGapValue08413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08413_not_prime : ¬(recordGapCenter + 499866).Prime := by
  rw [fullRecordGapTerm08413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08413_fast_pow_mod_ne_one

def fullRecordGapValue08414 : Nat := fullRecordGapCenterValue + 499886

theorem fullRecordGapTerm08414_eq_value :
    recordGapCenter + 499886 = fullRecordGapValue08414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08414 (fullRecordGapValue08414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08414_not_prime : ¬(recordGapCenter + 499886).Prime := by
  rw [fullRecordGapTerm08414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08414_fast_pow_mod_ne_one

def fullRecordGapValue08415 : Nat := fullRecordGapCenterValue + 499916

theorem fullRecordGapTerm08415_eq_value :
    recordGapCenter + 499916 = fullRecordGapValue08415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08415 (fullRecordGapValue08415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08415_not_prime : ¬(recordGapCenter + 499916).Prime := by
  rw [fullRecordGapTerm08415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08415_fast_pow_mod_ne_one

def fullRecordGapValue08416 : Nat := fullRecordGapCenterValue + 499976

theorem fullRecordGapTerm08416_eq_value :
    recordGapCenter + 499976 = fullRecordGapValue08416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08416 (fullRecordGapValue08416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08416_not_prime : ¬(recordGapCenter + 499976).Prime := by
  rw [fullRecordGapTerm08416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08416_fast_pow_mod_ne_one

def fullRecordGapValue08417 : Nat := fullRecordGapCenterValue + 500246

theorem fullRecordGapTerm08417_eq_value :
    recordGapCenter + 500246 = fullRecordGapValue08417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08417 (fullRecordGapValue08417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08417_not_prime : ¬(recordGapCenter + 500246).Prime := by
  rw [fullRecordGapTerm08417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08417_fast_pow_mod_ne_one

def fullRecordGapValue08418 : Nat := fullRecordGapCenterValue + 500252

theorem fullRecordGapTerm08418_eq_value :
    recordGapCenter + 500252 = fullRecordGapValue08418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08418 (fullRecordGapValue08418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08418_not_prime : ¬(recordGapCenter + 500252).Prime := by
  rw [fullRecordGapTerm08418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08418_fast_pow_mod_ne_one

def fullRecordGapValue08419 : Nat := fullRecordGapCenterValue + 500312

theorem fullRecordGapTerm08419_eq_value :
    recordGapCenter + 500312 = fullRecordGapValue08419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08419 (fullRecordGapValue08419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08419_not_prime : ¬(recordGapCenter + 500312).Prime := by
  rw [fullRecordGapTerm08419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08419_fast_pow_mod_ne_one

def fullRecordGapValue08420 : Nat := fullRecordGapCenterValue + 500330

theorem fullRecordGapTerm08420_eq_value :
    recordGapCenter + 500330 = fullRecordGapValue08420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08420 (fullRecordGapValue08420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08420_not_prime : ¬(recordGapCenter + 500330).Prime := by
  rw [fullRecordGapTerm08420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08420_fast_pow_mod_ne_one

def fullRecordGapValue08421 : Nat := fullRecordGapCenterValue + 500372

theorem fullRecordGapTerm08421_eq_value :
    recordGapCenter + 500372 = fullRecordGapValue08421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08421 (fullRecordGapValue08421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08421_not_prime : ¬(recordGapCenter + 500372).Prime := by
  rw [fullRecordGapTerm08421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08421_fast_pow_mod_ne_one

def fullRecordGapValue08422 : Nat := fullRecordGapCenterValue + 500406

theorem fullRecordGapTerm08422_eq_value :
    recordGapCenter + 500406 = fullRecordGapValue08422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08422 (fullRecordGapValue08422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08422_not_prime : ¬(recordGapCenter + 500406).Prime := by
  rw [fullRecordGapTerm08422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08422_fast_pow_mod_ne_one

def fullRecordGapValue08423 : Nat := fullRecordGapCenterValue + 500468

theorem fullRecordGapTerm08423_eq_value :
    recordGapCenter + 500468 = fullRecordGapValue08423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08423 (fullRecordGapValue08423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08423_not_prime : ¬(recordGapCenter + 500468).Prime := by
  rw [fullRecordGapTerm08423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08423_fast_pow_mod_ne_one

def fullRecordGapValue08424 : Nat := fullRecordGapCenterValue + 500510

theorem fullRecordGapTerm08424_eq_value :
    recordGapCenter + 500510 = fullRecordGapValue08424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08424 (fullRecordGapValue08424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08424_not_prime : ¬(recordGapCenter + 500510).Prime := by
  rw [fullRecordGapTerm08424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08424_fast_pow_mod_ne_one

def fullRecordGapValue08425 : Nat := fullRecordGapCenterValue + 500622

theorem fullRecordGapTerm08425_eq_value :
    recordGapCenter + 500622 = fullRecordGapValue08425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08425 (fullRecordGapValue08425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08425_not_prime : ¬(recordGapCenter + 500622).Prime := by
  rw [fullRecordGapTerm08425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08425_fast_pow_mod_ne_one

def fullRecordGapValue08426 : Nat := fullRecordGapCenterValue + 500690

theorem fullRecordGapTerm08426_eq_value :
    recordGapCenter + 500690 = fullRecordGapValue08426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08426 (fullRecordGapValue08426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08426_not_prime : ¬(recordGapCenter + 500690).Prime := by
  rw [fullRecordGapTerm08426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08426_fast_pow_mod_ne_one

def fullRecordGapValue08427 : Nat := fullRecordGapCenterValue + 500876

theorem fullRecordGapTerm08427_eq_value :
    recordGapCenter + 500876 = fullRecordGapValue08427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08427 (fullRecordGapValue08427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08427_not_prime : ¬(recordGapCenter + 500876).Prime := by
  rw [fullRecordGapTerm08427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08427_fast_pow_mod_ne_one

def fullRecordGapValue08428 : Nat := fullRecordGapCenterValue + 500882

theorem fullRecordGapTerm08428_eq_value :
    recordGapCenter + 500882 = fullRecordGapValue08428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08428 (fullRecordGapValue08428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08428_not_prime : ¬(recordGapCenter + 500882).Prime := by
  rw [fullRecordGapTerm08428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08428_fast_pow_mod_ne_one

def fullRecordGapValue08429 : Nat := fullRecordGapCenterValue + 500978

theorem fullRecordGapTerm08429_eq_value :
    recordGapCenter + 500978 = fullRecordGapValue08429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08429 (fullRecordGapValue08429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08429_not_prime : ¬(recordGapCenter + 500978).Prime := by
  rw [fullRecordGapTerm08429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08429_fast_pow_mod_ne_one

def fullRecordGapValue08430 : Nat := fullRecordGapCenterValue + 501086

theorem fullRecordGapTerm08430_eq_value :
    recordGapCenter + 501086 = fullRecordGapValue08430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08430 (fullRecordGapValue08430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08430_not_prime : ¬(recordGapCenter + 501086).Prime := by
  rw [fullRecordGapTerm08430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08430_fast_pow_mod_ne_one

def fullRecordGapValue08431 : Nat := fullRecordGapCenterValue + 501110

theorem fullRecordGapTerm08431_eq_value :
    recordGapCenter + 501110 = fullRecordGapValue08431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08431 (fullRecordGapValue08431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08431_not_prime : ¬(recordGapCenter + 501110).Prime := by
  rw [fullRecordGapTerm08431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08431_fast_pow_mod_ne_one

def fullRecordGapValue08432 : Nat := fullRecordGapCenterValue + 501362

theorem fullRecordGapTerm08432_eq_value :
    recordGapCenter + 501362 = fullRecordGapValue08432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08432 (fullRecordGapValue08432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08432_not_prime : ¬(recordGapCenter + 501362).Prime := by
  rw [fullRecordGapTerm08432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08432_fast_pow_mod_ne_one

def fullRecordGapValue08433 : Nat := fullRecordGapCenterValue + 501506

theorem fullRecordGapTerm08433_eq_value :
    recordGapCenter + 501506 = fullRecordGapValue08433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08433 (fullRecordGapValue08433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08433_not_prime : ¬(recordGapCenter + 501506).Prime := by
  rw [fullRecordGapTerm08433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08433_fast_pow_mod_ne_one

def fullRecordGapValue08434 : Nat := fullRecordGapCenterValue + 501548

theorem fullRecordGapTerm08434_eq_value :
    recordGapCenter + 501548 = fullRecordGapValue08434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08434 (fullRecordGapValue08434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08434_not_prime : ¬(recordGapCenter + 501548).Prime := by
  rw [fullRecordGapTerm08434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08434_fast_pow_mod_ne_one

def fullRecordGapValue08435 : Nat := fullRecordGapCenterValue + 501590

theorem fullRecordGapTerm08435_eq_value :
    recordGapCenter + 501590 = fullRecordGapValue08435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08435 (fullRecordGapValue08435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08435_not_prime : ¬(recordGapCenter + 501590).Prime := by
  rw [fullRecordGapTerm08435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08435_fast_pow_mod_ne_one

def fullRecordGapValue08436 : Nat := fullRecordGapCenterValue + 501692

theorem fullRecordGapTerm08436_eq_value :
    recordGapCenter + 501692 = fullRecordGapValue08436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08436 (fullRecordGapValue08436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08436_not_prime : ¬(recordGapCenter + 501692).Prime := by
  rw [fullRecordGapTerm08436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08436_fast_pow_mod_ne_one

def fullRecordGapValue08437 : Nat := fullRecordGapCenterValue + 501702

theorem fullRecordGapTerm08437_eq_value :
    recordGapCenter + 501702 = fullRecordGapValue08437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08437 (fullRecordGapValue08437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08437_not_prime : ¬(recordGapCenter + 501702).Prime := by
  rw [fullRecordGapTerm08437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08437_fast_pow_mod_ne_one

def fullRecordGapValue08438 : Nat := fullRecordGapCenterValue + 501716

theorem fullRecordGapTerm08438_eq_value :
    recordGapCenter + 501716 = fullRecordGapValue08438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08438 (fullRecordGapValue08438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08438_not_prime : ¬(recordGapCenter + 501716).Prime := by
  rw [fullRecordGapTerm08438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08438_fast_pow_mod_ne_one

def fullRecordGapValue08439 : Nat := fullRecordGapCenterValue + 501770

theorem fullRecordGapTerm08439_eq_value :
    recordGapCenter + 501770 = fullRecordGapValue08439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08439 (fullRecordGapValue08439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08439_not_prime : ¬(recordGapCenter + 501770).Prime := by
  rw [fullRecordGapTerm08439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08439_fast_pow_mod_ne_one

def fullRecordGapValue08440 : Nat := fullRecordGapCenterValue + 501848

theorem fullRecordGapTerm08440_eq_value :
    recordGapCenter + 501848 = fullRecordGapValue08440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08440 (fullRecordGapValue08440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08440_not_prime : ¬(recordGapCenter + 501848).Prime := by
  rw [fullRecordGapTerm08440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08440_fast_pow_mod_ne_one

def fullRecordGapValue08441 : Nat := fullRecordGapCenterValue + 501918

theorem fullRecordGapTerm08441_eq_value :
    recordGapCenter + 501918 = fullRecordGapValue08441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08441 (fullRecordGapValue08441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08441_not_prime : ¬(recordGapCenter + 501918).Prime := by
  rw [fullRecordGapTerm08441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08441_fast_pow_mod_ne_one

def fullRecordGapValue08442 : Nat := fullRecordGapCenterValue + 501938

theorem fullRecordGapTerm08442_eq_value :
    recordGapCenter + 501938 = fullRecordGapValue08442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08442 (fullRecordGapValue08442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08442_not_prime : ¬(recordGapCenter + 501938).Prime := by
  rw [fullRecordGapTerm08442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08442_fast_pow_mod_ne_one

def fullRecordGapValue08443 : Nat := fullRecordGapCenterValue + 501986

theorem fullRecordGapTerm08443_eq_value :
    recordGapCenter + 501986 = fullRecordGapValue08443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08443 (fullRecordGapValue08443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08443_not_prime : ¬(recordGapCenter + 501986).Prime := by
  rw [fullRecordGapTerm08443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08443_fast_pow_mod_ne_one

def fullRecordGapValue08444 : Nat := fullRecordGapCenterValue + 502070

theorem fullRecordGapTerm08444_eq_value :
    recordGapCenter + 502070 = fullRecordGapValue08444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08444 (fullRecordGapValue08444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08444_not_prime : ¬(recordGapCenter + 502070).Prime := by
  rw [fullRecordGapTerm08444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08444_fast_pow_mod_ne_one

def fullRecordGapValue08445 : Nat := fullRecordGapCenterValue + 502118

theorem fullRecordGapTerm08445_eq_value :
    recordGapCenter + 502118 = fullRecordGapValue08445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08445 (fullRecordGapValue08445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08445_not_prime : ¬(recordGapCenter + 502118).Prime := by
  rw [fullRecordGapTerm08445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08445_fast_pow_mod_ne_one

def fullRecordGapValue08446 : Nat := fullRecordGapCenterValue + 502310

theorem fullRecordGapTerm08446_eq_value :
    recordGapCenter + 502310 = fullRecordGapValue08446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08446 (fullRecordGapValue08446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08446_not_prime : ¬(recordGapCenter + 502310).Prime := by
  rw [fullRecordGapTerm08446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08446_fast_pow_mod_ne_one

def fullRecordGapValue08447 : Nat := fullRecordGapCenterValue + 502406

theorem fullRecordGapTerm08447_eq_value :
    recordGapCenter + 502406 = fullRecordGapValue08447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08447 (fullRecordGapValue08447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08447_not_prime : ¬(recordGapCenter + 502406).Prime := by
  rw [fullRecordGapTerm08447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08447_fast_pow_mod_ne_one

def fullRecordGapValue08448 : Nat := fullRecordGapCenterValue + 502526

theorem fullRecordGapTerm08448_eq_value :
    recordGapCenter + 502526 = fullRecordGapValue08448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08448 (fullRecordGapValue08448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08448_not_prime : ¬(recordGapCenter + 502526).Prime := by
  rw [fullRecordGapTerm08448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08448_fast_pow_mod_ne_one

end PrimeFactorUnimodality
