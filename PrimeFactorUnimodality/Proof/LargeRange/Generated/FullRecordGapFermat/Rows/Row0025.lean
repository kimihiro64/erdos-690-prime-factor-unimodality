import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue06145 : Nat := fullRecordGapCenterValue + 327266

theorem fullRecordGapTerm06145_eq_value :
    recordGapCenter + 327266 = fullRecordGapValue06145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06145 (fullRecordGapValue06145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06145_not_prime : ¬(recordGapCenter + 327266).Prime := by
  rw [fullRecordGapTerm06145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06145_fast_pow_mod_ne_one

def fullRecordGapValue06146 : Nat := fullRecordGapCenterValue + 327462

theorem fullRecordGapTerm06146_eq_value :
    recordGapCenter + 327462 = fullRecordGapValue06146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06146 (fullRecordGapValue06146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06146_not_prime : ¬(recordGapCenter + 327462).Prime := by
  rw [fullRecordGapTerm06146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06146_fast_pow_mod_ne_one

def fullRecordGapValue06147 : Nat := fullRecordGapCenterValue + 327482

theorem fullRecordGapTerm06147_eq_value :
    recordGapCenter + 327482 = fullRecordGapValue06147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06147 (fullRecordGapValue06147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06147_not_prime : ¬(recordGapCenter + 327482).Prime := by
  rw [fullRecordGapTerm06147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06147_fast_pow_mod_ne_one

def fullRecordGapValue06148 : Nat := fullRecordGapCenterValue + 327486

theorem fullRecordGapTerm06148_eq_value :
    recordGapCenter + 327486 = fullRecordGapValue06148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06148 (fullRecordGapValue06148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06148_not_prime : ¬(recordGapCenter + 327486).Prime := by
  rw [fullRecordGapTerm06148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06148_fast_pow_mod_ne_one

def fullRecordGapValue06149 : Nat := fullRecordGapCenterValue + 327638

theorem fullRecordGapTerm06149_eq_value :
    recordGapCenter + 327638 = fullRecordGapValue06149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06149 (fullRecordGapValue06149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06149_not_prime : ¬(recordGapCenter + 327638).Prime := by
  rw [fullRecordGapTerm06149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06149_fast_pow_mod_ne_one

def fullRecordGapValue06150 : Nat := fullRecordGapCenterValue + 327738

theorem fullRecordGapTerm06150_eq_value :
    recordGapCenter + 327738 = fullRecordGapValue06150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06150 (fullRecordGapValue06150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06150_not_prime : ¬(recordGapCenter + 327738).Prime := by
  rw [fullRecordGapTerm06150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06150_fast_pow_mod_ne_one

def fullRecordGapValue06151 : Nat := fullRecordGapCenterValue + 327786

theorem fullRecordGapTerm06151_eq_value :
    recordGapCenter + 327786 = fullRecordGapValue06151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06151 (fullRecordGapValue06151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06151_not_prime : ¬(recordGapCenter + 327786).Prime := by
  rw [fullRecordGapTerm06151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06151_fast_pow_mod_ne_one

def fullRecordGapValue06152 : Nat := fullRecordGapCenterValue + 327812

theorem fullRecordGapTerm06152_eq_value :
    recordGapCenter + 327812 = fullRecordGapValue06152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06152 (fullRecordGapValue06152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06152_not_prime : ¬(recordGapCenter + 327812).Prime := by
  rw [fullRecordGapTerm06152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06152_fast_pow_mod_ne_one

def fullRecordGapValue06153 : Nat := fullRecordGapCenterValue + 327882

theorem fullRecordGapTerm06153_eq_value :
    recordGapCenter + 327882 = fullRecordGapValue06153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06153 (fullRecordGapValue06153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06153_not_prime : ¬(recordGapCenter + 327882).Prime := by
  rw [fullRecordGapTerm06153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06153_fast_pow_mod_ne_one

def fullRecordGapValue06154 : Nat := fullRecordGapCenterValue + 327962

theorem fullRecordGapTerm06154_eq_value :
    recordGapCenter + 327962 = fullRecordGapValue06154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06154 (fullRecordGapValue06154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06154_not_prime : ¬(recordGapCenter + 327962).Prime := by
  rw [fullRecordGapTerm06154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06154_fast_pow_mod_ne_one

def fullRecordGapValue06155 : Nat := fullRecordGapCenterValue + 328022

theorem fullRecordGapTerm06155_eq_value :
    recordGapCenter + 328022 = fullRecordGapValue06155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06155 (fullRecordGapValue06155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06155_not_prime : ¬(recordGapCenter + 328022).Prime := by
  rw [fullRecordGapTerm06155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06155_fast_pow_mod_ne_one

def fullRecordGapValue06156 : Nat := fullRecordGapCenterValue + 328046

theorem fullRecordGapTerm06156_eq_value :
    recordGapCenter + 328046 = fullRecordGapValue06156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06156 (fullRecordGapValue06156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06156_not_prime : ¬(recordGapCenter + 328046).Prime := by
  rw [fullRecordGapTerm06156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06156_fast_pow_mod_ne_one

def fullRecordGapValue06157 : Nat := fullRecordGapCenterValue + 328298

theorem fullRecordGapTerm06157_eq_value :
    recordGapCenter + 328298 = fullRecordGapValue06157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06157 (fullRecordGapValue06157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06157_not_prime : ¬(recordGapCenter + 328298).Prime := by
  rw [fullRecordGapTerm06157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06157_fast_pow_mod_ne_one

def fullRecordGapValue06158 : Nat := fullRecordGapCenterValue + 328326

theorem fullRecordGapTerm06158_eq_value :
    recordGapCenter + 328326 = fullRecordGapValue06158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06158 (fullRecordGapValue06158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06158_not_prime : ¬(recordGapCenter + 328326).Prime := by
  rw [fullRecordGapTerm06158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06158_fast_pow_mod_ne_one

def fullRecordGapValue06159 : Nat := fullRecordGapCenterValue + 328466

theorem fullRecordGapTerm06159_eq_value :
    recordGapCenter + 328466 = fullRecordGapValue06159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06159 (fullRecordGapValue06159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06159_not_prime : ¬(recordGapCenter + 328466).Prime := by
  rw [fullRecordGapTerm06159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06159_fast_pow_mod_ne_one

def fullRecordGapValue06160 : Nat := fullRecordGapCenterValue + 328506

theorem fullRecordGapTerm06160_eq_value :
    recordGapCenter + 328506 = fullRecordGapValue06160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06160 (fullRecordGapValue06160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06160_not_prime : ¬(recordGapCenter + 328506).Prime := by
  rw [fullRecordGapTerm06160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06160_fast_pow_mod_ne_one

def fullRecordGapValue06161 : Nat := fullRecordGapCenterValue + 328598

theorem fullRecordGapTerm06161_eq_value :
    recordGapCenter + 328598 = fullRecordGapValue06161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06161 (fullRecordGapValue06161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06161_not_prime : ¬(recordGapCenter + 328598).Prime := by
  rw [fullRecordGapTerm06161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06161_fast_pow_mod_ne_one

def fullRecordGapValue06162 : Nat := fullRecordGapCenterValue + 328652

theorem fullRecordGapTerm06162_eq_value :
    recordGapCenter + 328652 = fullRecordGapValue06162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06162 (fullRecordGapValue06162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06162_not_prime : ¬(recordGapCenter + 328652).Prime := by
  rw [fullRecordGapTerm06162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06162_fast_pow_mod_ne_one

def fullRecordGapValue06163 : Nat := fullRecordGapCenterValue + 328722

theorem fullRecordGapTerm06163_eq_value :
    recordGapCenter + 328722 = fullRecordGapValue06163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06163 (fullRecordGapValue06163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06163_not_prime : ¬(recordGapCenter + 328722).Prime := by
  rw [fullRecordGapTerm06163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06163_fast_pow_mod_ne_one

def fullRecordGapValue06164 : Nat := fullRecordGapCenterValue + 328772

theorem fullRecordGapTerm06164_eq_value :
    recordGapCenter + 328772 = fullRecordGapValue06164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06164 (fullRecordGapValue06164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06164_not_prime : ¬(recordGapCenter + 328772).Prime := by
  rw [fullRecordGapTerm06164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06164_fast_pow_mod_ne_one

def fullRecordGapValue06165 : Nat := fullRecordGapCenterValue + 328868

theorem fullRecordGapTerm06165_eq_value :
    recordGapCenter + 328868 = fullRecordGapValue06165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06165 (fullRecordGapValue06165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06165_not_prime : ¬(recordGapCenter + 328868).Prime := by
  rw [fullRecordGapTerm06165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06165_fast_pow_mod_ne_one

def fullRecordGapValue06166 : Nat := fullRecordGapCenterValue + 328898

theorem fullRecordGapTerm06166_eq_value :
    recordGapCenter + 328898 = fullRecordGapValue06166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06166 (fullRecordGapValue06166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06166_not_prime : ¬(recordGapCenter + 328898).Prime := by
  rw [fullRecordGapTerm06166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06166_fast_pow_mod_ne_one

def fullRecordGapValue06167 : Nat := fullRecordGapCenterValue + 329228

theorem fullRecordGapTerm06167_eq_value :
    recordGapCenter + 329228 = fullRecordGapValue06167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06167 (fullRecordGapValue06167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06167_not_prime : ¬(recordGapCenter + 329228).Prime := by
  rw [fullRecordGapTerm06167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06167_fast_pow_mod_ne_one

def fullRecordGapValue06168 : Nat := fullRecordGapCenterValue + 329262

theorem fullRecordGapTerm06168_eq_value :
    recordGapCenter + 329262 = fullRecordGapValue06168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06168 (fullRecordGapValue06168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06168_not_prime : ¬(recordGapCenter + 329262).Prime := by
  rw [fullRecordGapTerm06168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06168_fast_pow_mod_ne_one

def fullRecordGapValue06169 : Nat := fullRecordGapCenterValue + 329366

theorem fullRecordGapTerm06169_eq_value :
    recordGapCenter + 329366 = fullRecordGapValue06169 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06169_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06169 (fullRecordGapValue06169 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06169_not_prime : ¬(recordGapCenter + 329366).Prime := by
  rw [fullRecordGapTerm06169_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06169, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06169_fast_pow_mod_ne_one

def fullRecordGapValue06170 : Nat := fullRecordGapCenterValue + 329442

theorem fullRecordGapTerm06170_eq_value :
    recordGapCenter + 329442 = fullRecordGapValue06170 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06170_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06170 (fullRecordGapValue06170 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06170_not_prime : ¬(recordGapCenter + 329442).Prime := by
  rw [fullRecordGapTerm06170_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06170, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06170_fast_pow_mod_ne_one

def fullRecordGapValue06171 : Nat := fullRecordGapCenterValue + 329502

theorem fullRecordGapTerm06171_eq_value :
    recordGapCenter + 329502 = fullRecordGapValue06171 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06171_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06171 (fullRecordGapValue06171 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06171_not_prime : ¬(recordGapCenter + 329502).Prime := by
  rw [fullRecordGapTerm06171_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06171, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06171_fast_pow_mod_ne_one

def fullRecordGapValue06172 : Nat := fullRecordGapCenterValue + 329618

theorem fullRecordGapTerm06172_eq_value :
    recordGapCenter + 329618 = fullRecordGapValue06172 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06172_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06172 (fullRecordGapValue06172 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06172_not_prime : ¬(recordGapCenter + 329618).Prime := by
  rw [fullRecordGapTerm06172_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06172, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06172_fast_pow_mod_ne_one

def fullRecordGapValue06173 : Nat := fullRecordGapCenterValue + 329828

theorem fullRecordGapTerm06173_eq_value :
    recordGapCenter + 329828 = fullRecordGapValue06173 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06173_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06173 (fullRecordGapValue06173 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06173_not_prime : ¬(recordGapCenter + 329828).Prime := by
  rw [fullRecordGapTerm06173_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06173, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06173_fast_pow_mod_ne_one

def fullRecordGapValue06174 : Nat := fullRecordGapCenterValue + 329852

theorem fullRecordGapTerm06174_eq_value :
    recordGapCenter + 329852 = fullRecordGapValue06174 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06174_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06174 (fullRecordGapValue06174 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06174_not_prime : ¬(recordGapCenter + 329852).Prime := by
  rw [fullRecordGapTerm06174_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06174, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06174_fast_pow_mod_ne_one

def fullRecordGapValue06175 : Nat := fullRecordGapCenterValue + 329876

theorem fullRecordGapTerm06175_eq_value :
    recordGapCenter + 329876 = fullRecordGapValue06175 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06175_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06175 (fullRecordGapValue06175 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06175_not_prime : ¬(recordGapCenter + 329876).Prime := by
  rw [fullRecordGapTerm06175_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06175, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06175_fast_pow_mod_ne_one

def fullRecordGapValue06176 : Nat := fullRecordGapCenterValue + 329948

theorem fullRecordGapTerm06176_eq_value :
    recordGapCenter + 329948 = fullRecordGapValue06176 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06176_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06176 (fullRecordGapValue06176 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06176_not_prime : ¬(recordGapCenter + 329948).Prime := by
  rw [fullRecordGapTerm06176_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06176, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06176_fast_pow_mod_ne_one

def fullRecordGapValue06177 : Nat := fullRecordGapCenterValue + 330002

theorem fullRecordGapTerm06177_eq_value :
    recordGapCenter + 330002 = fullRecordGapValue06177 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06177_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06177 (fullRecordGapValue06177 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06177_not_prime : ¬(recordGapCenter + 330002).Prime := by
  rw [fullRecordGapTerm06177_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06177, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06177_fast_pow_mod_ne_one

def fullRecordGapValue06178 : Nat := fullRecordGapCenterValue + 330206

theorem fullRecordGapTerm06178_eq_value :
    recordGapCenter + 330206 = fullRecordGapValue06178 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06178_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06178 (fullRecordGapValue06178 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06178_not_prime : ¬(recordGapCenter + 330206).Prime := by
  rw [fullRecordGapTerm06178_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06178, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06178_fast_pow_mod_ne_one

def fullRecordGapValue06179 : Nat := fullRecordGapCenterValue + 330306

theorem fullRecordGapTerm06179_eq_value :
    recordGapCenter + 330306 = fullRecordGapValue06179 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06179_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06179 (fullRecordGapValue06179 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06179_not_prime : ¬(recordGapCenter + 330306).Prime := by
  rw [fullRecordGapTerm06179_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06179, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06179_fast_pow_mod_ne_one

def fullRecordGapValue06180 : Nat := fullRecordGapCenterValue + 330366

theorem fullRecordGapTerm06180_eq_value :
    recordGapCenter + 330366 = fullRecordGapValue06180 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06180_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06180 (fullRecordGapValue06180 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06180_not_prime : ¬(recordGapCenter + 330366).Prime := by
  rw [fullRecordGapTerm06180_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06180, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06180_fast_pow_mod_ne_one

def fullRecordGapValue06181 : Nat := fullRecordGapCenterValue + 330422

theorem fullRecordGapTerm06181_eq_value :
    recordGapCenter + 330422 = fullRecordGapValue06181 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06181_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06181 (fullRecordGapValue06181 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06181_not_prime : ¬(recordGapCenter + 330422).Prime := by
  rw [fullRecordGapTerm06181_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06181, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06181_fast_pow_mod_ne_one

def fullRecordGapValue06182 : Nat := fullRecordGapCenterValue + 330452

theorem fullRecordGapTerm06182_eq_value :
    recordGapCenter + 330452 = fullRecordGapValue06182 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06182_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06182 (fullRecordGapValue06182 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06182_not_prime : ¬(recordGapCenter + 330452).Prime := by
  rw [fullRecordGapTerm06182_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06182, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06182_fast_pow_mod_ne_one

def fullRecordGapValue06183 : Nat := fullRecordGapCenterValue + 330626

theorem fullRecordGapTerm06183_eq_value :
    recordGapCenter + 330626 = fullRecordGapValue06183 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06183_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06183 (fullRecordGapValue06183 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06183_not_prime : ¬(recordGapCenter + 330626).Prime := by
  rw [fullRecordGapTerm06183_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06183, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06183_fast_pow_mod_ne_one

def fullRecordGapValue06184 : Nat := fullRecordGapCenterValue + 330662

theorem fullRecordGapTerm06184_eq_value :
    recordGapCenter + 330662 = fullRecordGapValue06184 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06184_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06184 (fullRecordGapValue06184 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06184_not_prime : ¬(recordGapCenter + 330662).Prime := by
  rw [fullRecordGapTerm06184_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06184, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06184_fast_pow_mod_ne_one

def fullRecordGapValue06185 : Nat := fullRecordGapCenterValue + 330698

theorem fullRecordGapTerm06185_eq_value :
    recordGapCenter + 330698 = fullRecordGapValue06185 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06185_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06185 (fullRecordGapValue06185 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06185_not_prime : ¬(recordGapCenter + 330698).Prime := by
  rw [fullRecordGapTerm06185_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06185, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06185_fast_pow_mod_ne_one

def fullRecordGapValue06186 : Nat := fullRecordGapCenterValue + 330758

theorem fullRecordGapTerm06186_eq_value :
    recordGapCenter + 330758 = fullRecordGapValue06186 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06186_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06186 (fullRecordGapValue06186 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06186_not_prime : ¬(recordGapCenter + 330758).Prime := by
  rw [fullRecordGapTerm06186_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06186, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06186_fast_pow_mod_ne_one

def fullRecordGapValue06187 : Nat := fullRecordGapCenterValue + 330782

theorem fullRecordGapTerm06187_eq_value :
    recordGapCenter + 330782 = fullRecordGapValue06187 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06187_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06187 (fullRecordGapValue06187 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06187_not_prime : ¬(recordGapCenter + 330782).Prime := by
  rw [fullRecordGapTerm06187_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06187, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06187_fast_pow_mod_ne_one

def fullRecordGapValue06188 : Nat := fullRecordGapCenterValue + 330926

theorem fullRecordGapTerm06188_eq_value :
    recordGapCenter + 330926 = fullRecordGapValue06188 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06188_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06188 (fullRecordGapValue06188 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06188_not_prime : ¬(recordGapCenter + 330926).Prime := by
  rw [fullRecordGapTerm06188_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06188, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06188_fast_pow_mod_ne_one

def fullRecordGapValue06189 : Nat := fullRecordGapCenterValue + 330978

theorem fullRecordGapTerm06189_eq_value :
    recordGapCenter + 330978 = fullRecordGapValue06189 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06189_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06189 (fullRecordGapValue06189 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06189_not_prime : ¬(recordGapCenter + 330978).Prime := by
  rw [fullRecordGapTerm06189_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06189, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06189_fast_pow_mod_ne_one

def fullRecordGapValue06190 : Nat := fullRecordGapCenterValue + 331026

theorem fullRecordGapTerm06190_eq_value :
    recordGapCenter + 331026 = fullRecordGapValue06190 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06190_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06190 (fullRecordGapValue06190 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06190_not_prime : ¬(recordGapCenter + 331026).Prime := by
  rw [fullRecordGapTerm06190_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06190, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06190_fast_pow_mod_ne_one

def fullRecordGapValue06191 : Nat := fullRecordGapCenterValue + 331082

theorem fullRecordGapTerm06191_eq_value :
    recordGapCenter + 331082 = fullRecordGapValue06191 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06191_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06191 (fullRecordGapValue06191 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06191_not_prime : ¬(recordGapCenter + 331082).Prime := by
  rw [fullRecordGapTerm06191_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06191, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06191_fast_pow_mod_ne_one

def fullRecordGapValue06192 : Nat := fullRecordGapCenterValue + 331202

theorem fullRecordGapTerm06192_eq_value :
    recordGapCenter + 331202 = fullRecordGapValue06192 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06192_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06192 (fullRecordGapValue06192 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06192_not_prime : ¬(recordGapCenter + 331202).Prime := by
  rw [fullRecordGapTerm06192_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06192, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06192_fast_pow_mod_ne_one

def fullRecordGapValue06193 : Nat := fullRecordGapCenterValue + 331242

theorem fullRecordGapTerm06193_eq_value :
    recordGapCenter + 331242 = fullRecordGapValue06193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06193 (fullRecordGapValue06193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06193_not_prime : ¬(recordGapCenter + 331242).Prime := by
  rw [fullRecordGapTerm06193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06193_fast_pow_mod_ne_one

def fullRecordGapValue06194 : Nat := fullRecordGapCenterValue + 331278

theorem fullRecordGapTerm06194_eq_value :
    recordGapCenter + 331278 = fullRecordGapValue06194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06194 (fullRecordGapValue06194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06194_not_prime : ¬(recordGapCenter + 331278).Prime := by
  rw [fullRecordGapTerm06194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06194_fast_pow_mod_ne_one

def fullRecordGapValue06195 : Nat := fullRecordGapCenterValue + 331346

theorem fullRecordGapTerm06195_eq_value :
    recordGapCenter + 331346 = fullRecordGapValue06195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06195 (fullRecordGapValue06195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06195_not_prime : ¬(recordGapCenter + 331346).Prime := by
  rw [fullRecordGapTerm06195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06195_fast_pow_mod_ne_one

def fullRecordGapValue06196 : Nat := fullRecordGapCenterValue + 331388

theorem fullRecordGapTerm06196_eq_value :
    recordGapCenter + 331388 = fullRecordGapValue06196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06196 (fullRecordGapValue06196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06196_not_prime : ¬(recordGapCenter + 331388).Prime := by
  rw [fullRecordGapTerm06196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06196_fast_pow_mod_ne_one

def fullRecordGapValue06197 : Nat := fullRecordGapCenterValue + 331418

theorem fullRecordGapTerm06197_eq_value :
    recordGapCenter + 331418 = fullRecordGapValue06197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06197 (fullRecordGapValue06197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06197_not_prime : ¬(recordGapCenter + 331418).Prime := by
  rw [fullRecordGapTerm06197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06197_fast_pow_mod_ne_one

def fullRecordGapValue06198 : Nat := fullRecordGapCenterValue + 331458

theorem fullRecordGapTerm06198_eq_value :
    recordGapCenter + 331458 = fullRecordGapValue06198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06198 (fullRecordGapValue06198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06198_not_prime : ¬(recordGapCenter + 331458).Prime := by
  rw [fullRecordGapTerm06198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06198_fast_pow_mod_ne_one

def fullRecordGapValue06199 : Nat := fullRecordGapCenterValue + 331532

theorem fullRecordGapTerm06199_eq_value :
    recordGapCenter + 331532 = fullRecordGapValue06199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06199 (fullRecordGapValue06199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06199_not_prime : ¬(recordGapCenter + 331532).Prime := by
  rw [fullRecordGapTerm06199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06199_fast_pow_mod_ne_one

def fullRecordGapValue06200 : Nat := fullRecordGapCenterValue + 331622

theorem fullRecordGapTerm06200_eq_value :
    recordGapCenter + 331622 = fullRecordGapValue06200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06200 (fullRecordGapValue06200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06200_not_prime : ¬(recordGapCenter + 331622).Prime := by
  rw [fullRecordGapTerm06200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06200_fast_pow_mod_ne_one

def fullRecordGapValue06201 : Nat := fullRecordGapCenterValue + 331746

theorem fullRecordGapTerm06201_eq_value :
    recordGapCenter + 331746 = fullRecordGapValue06201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06201 (fullRecordGapValue06201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06201_not_prime : ¬(recordGapCenter + 331746).Prime := by
  rw [fullRecordGapTerm06201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06201_fast_pow_mod_ne_one

def fullRecordGapValue06202 : Nat := fullRecordGapCenterValue + 331776

theorem fullRecordGapTerm06202_eq_value :
    recordGapCenter + 331776 = fullRecordGapValue06202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06202 (fullRecordGapValue06202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06202_not_prime : ¬(recordGapCenter + 331776).Prime := by
  rw [fullRecordGapTerm06202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06202_fast_pow_mod_ne_one

def fullRecordGapValue06203 : Nat := fullRecordGapCenterValue + 331986

theorem fullRecordGapTerm06203_eq_value :
    recordGapCenter + 331986 = fullRecordGapValue06203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06203 (fullRecordGapValue06203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06203_not_prime : ¬(recordGapCenter + 331986).Prime := by
  rw [fullRecordGapTerm06203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06203_fast_pow_mod_ne_one

def fullRecordGapValue06204 : Nat := fullRecordGapCenterValue + 332106

theorem fullRecordGapTerm06204_eq_value :
    recordGapCenter + 332106 = fullRecordGapValue06204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06204 (fullRecordGapValue06204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06204_not_prime : ¬(recordGapCenter + 332106).Prime := by
  rw [fullRecordGapTerm06204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06204_fast_pow_mod_ne_one

def fullRecordGapValue06205 : Nat := fullRecordGapCenterValue + 332126

theorem fullRecordGapTerm06205_eq_value :
    recordGapCenter + 332126 = fullRecordGapValue06205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06205 (fullRecordGapValue06205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06205_not_prime : ¬(recordGapCenter + 332126).Prime := by
  rw [fullRecordGapTerm06205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06205_fast_pow_mod_ne_one

def fullRecordGapValue06206 : Nat := fullRecordGapCenterValue + 332162

theorem fullRecordGapTerm06206_eq_value :
    recordGapCenter + 332162 = fullRecordGapValue06206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06206 (fullRecordGapValue06206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06206_not_prime : ¬(recordGapCenter + 332162).Prime := by
  rw [fullRecordGapTerm06206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06206_fast_pow_mod_ne_one

def fullRecordGapValue06207 : Nat := fullRecordGapCenterValue + 332252

theorem fullRecordGapTerm06207_eq_value :
    recordGapCenter + 332252 = fullRecordGapValue06207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06207 (fullRecordGapValue06207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06207_not_prime : ¬(recordGapCenter + 332252).Prime := by
  rw [fullRecordGapTerm06207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06207_fast_pow_mod_ne_one

def fullRecordGapValue06208 : Nat := fullRecordGapCenterValue + 332286

theorem fullRecordGapTerm06208_eq_value :
    recordGapCenter + 332286 = fullRecordGapValue06208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06208 (fullRecordGapValue06208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06208_not_prime : ¬(recordGapCenter + 332286).Prime := by
  rw [fullRecordGapTerm06208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06208_fast_pow_mod_ne_one

def fullRecordGapValue06209 : Nat := fullRecordGapCenterValue + 332466

theorem fullRecordGapTerm06209_eq_value :
    recordGapCenter + 332466 = fullRecordGapValue06209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06209 (fullRecordGapValue06209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06209_not_prime : ¬(recordGapCenter + 332466).Prime := by
  rw [fullRecordGapTerm06209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06209_fast_pow_mod_ne_one

def fullRecordGapValue06210 : Nat := fullRecordGapCenterValue + 332468

theorem fullRecordGapTerm06210_eq_value :
    recordGapCenter + 332468 = fullRecordGapValue06210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06210 (fullRecordGapValue06210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06210_not_prime : ¬(recordGapCenter + 332468).Prime := by
  rw [fullRecordGapTerm06210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06210_fast_pow_mod_ne_one

def fullRecordGapValue06211 : Nat := fullRecordGapCenterValue + 332708

theorem fullRecordGapTerm06211_eq_value :
    recordGapCenter + 332708 = fullRecordGapValue06211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06211 (fullRecordGapValue06211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06211_not_prime : ¬(recordGapCenter + 332708).Prime := by
  rw [fullRecordGapTerm06211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06211_fast_pow_mod_ne_one

def fullRecordGapValue06212 : Nat := fullRecordGapCenterValue + 332798

theorem fullRecordGapTerm06212_eq_value :
    recordGapCenter + 332798 = fullRecordGapValue06212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06212 (fullRecordGapValue06212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06212_not_prime : ¬(recordGapCenter + 332798).Prime := by
  rw [fullRecordGapTerm06212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06212_fast_pow_mod_ne_one

def fullRecordGapValue06213 : Nat := fullRecordGapCenterValue + 332858

theorem fullRecordGapTerm06213_eq_value :
    recordGapCenter + 332858 = fullRecordGapValue06213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06213 (fullRecordGapValue06213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06213_not_prime : ¬(recordGapCenter + 332858).Prime := by
  rw [fullRecordGapTerm06213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06213_fast_pow_mod_ne_one

def fullRecordGapValue06214 : Nat := fullRecordGapCenterValue + 332876

theorem fullRecordGapTerm06214_eq_value :
    recordGapCenter + 332876 = fullRecordGapValue06214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06214 (fullRecordGapValue06214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06214_not_prime : ¬(recordGapCenter + 332876).Prime := by
  rw [fullRecordGapTerm06214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06214_fast_pow_mod_ne_one

def fullRecordGapValue06215 : Nat := fullRecordGapCenterValue + 332942

theorem fullRecordGapTerm06215_eq_value :
    recordGapCenter + 332942 = fullRecordGapValue06215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06215 (fullRecordGapValue06215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06215_not_prime : ¬(recordGapCenter + 332942).Prime := by
  rw [fullRecordGapTerm06215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06215_fast_pow_mod_ne_one

def fullRecordGapValue06216 : Nat := fullRecordGapCenterValue + 333068

theorem fullRecordGapTerm06216_eq_value :
    recordGapCenter + 333068 = fullRecordGapValue06216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06216 (fullRecordGapValue06216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06216_not_prime : ¬(recordGapCenter + 333068).Prime := by
  rw [fullRecordGapTerm06216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06216_fast_pow_mod_ne_one

def fullRecordGapValue06217 : Nat := fullRecordGapCenterValue + 333246

theorem fullRecordGapTerm06217_eq_value :
    recordGapCenter + 333246 = fullRecordGapValue06217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06217 (fullRecordGapValue06217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06217_not_prime : ¬(recordGapCenter + 333246).Prime := by
  rw [fullRecordGapTerm06217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06217_fast_pow_mod_ne_one

def fullRecordGapValue06218 : Nat := fullRecordGapCenterValue + 333338

theorem fullRecordGapTerm06218_eq_value :
    recordGapCenter + 333338 = fullRecordGapValue06218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06218 (fullRecordGapValue06218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06218_not_prime : ¬(recordGapCenter + 333338).Prime := by
  rw [fullRecordGapTerm06218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06218_fast_pow_mod_ne_one

def fullRecordGapValue06219 : Nat := fullRecordGapCenterValue + 333446

theorem fullRecordGapTerm06219_eq_value :
    recordGapCenter + 333446 = fullRecordGapValue06219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06219 (fullRecordGapValue06219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06219_not_prime : ¬(recordGapCenter + 333446).Prime := by
  rw [fullRecordGapTerm06219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06219_fast_pow_mod_ne_one

def fullRecordGapValue06220 : Nat := fullRecordGapCenterValue + 333618

theorem fullRecordGapTerm06220_eq_value :
    recordGapCenter + 333618 = fullRecordGapValue06220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06220 (fullRecordGapValue06220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06220_not_prime : ¬(recordGapCenter + 333618).Prime := by
  rw [fullRecordGapTerm06220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06220_fast_pow_mod_ne_one

def fullRecordGapValue06221 : Nat := fullRecordGapCenterValue + 333698

theorem fullRecordGapTerm06221_eq_value :
    recordGapCenter + 333698 = fullRecordGapValue06221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06221 (fullRecordGapValue06221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06221_not_prime : ¬(recordGapCenter + 333698).Prime := by
  rw [fullRecordGapTerm06221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06221_fast_pow_mod_ne_one

def fullRecordGapValue06222 : Nat := fullRecordGapCenterValue + 333722

theorem fullRecordGapTerm06222_eq_value :
    recordGapCenter + 333722 = fullRecordGapValue06222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06222 (fullRecordGapValue06222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06222_not_prime : ¬(recordGapCenter + 333722).Prime := by
  rw [fullRecordGapTerm06222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06222_fast_pow_mod_ne_one

def fullRecordGapValue06223 : Nat := fullRecordGapCenterValue + 333786

theorem fullRecordGapTerm06223_eq_value :
    recordGapCenter + 333786 = fullRecordGapValue06223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06223 (fullRecordGapValue06223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06223_not_prime : ¬(recordGapCenter + 333786).Prime := by
  rw [fullRecordGapTerm06223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06223_fast_pow_mod_ne_one

def fullRecordGapValue06224 : Nat := fullRecordGapCenterValue + 333798

theorem fullRecordGapTerm06224_eq_value :
    recordGapCenter + 333798 = fullRecordGapValue06224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06224 (fullRecordGapValue06224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06224_not_prime : ¬(recordGapCenter + 333798).Prime := by
  rw [fullRecordGapTerm06224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06224_fast_pow_mod_ne_one

def fullRecordGapValue06225 : Nat := fullRecordGapCenterValue + 333818

theorem fullRecordGapTerm06225_eq_value :
    recordGapCenter + 333818 = fullRecordGapValue06225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06225 (fullRecordGapValue06225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06225_not_prime : ¬(recordGapCenter + 333818).Prime := by
  rw [fullRecordGapTerm06225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06225_fast_pow_mod_ne_one

def fullRecordGapValue06226 : Nat := fullRecordGapCenterValue + 333966

theorem fullRecordGapTerm06226_eq_value :
    recordGapCenter + 333966 = fullRecordGapValue06226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06226 (fullRecordGapValue06226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06226_not_prime : ¬(recordGapCenter + 333966).Prime := by
  rw [fullRecordGapTerm06226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06226_fast_pow_mod_ne_one

def fullRecordGapValue06227 : Nat := fullRecordGapCenterValue + 334148

theorem fullRecordGapTerm06227_eq_value :
    recordGapCenter + 334148 = fullRecordGapValue06227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06227 (fullRecordGapValue06227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06227_not_prime : ¬(recordGapCenter + 334148).Prime := by
  rw [fullRecordGapTerm06227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06227_fast_pow_mod_ne_one

def fullRecordGapValue06228 : Nat := fullRecordGapCenterValue + 334346

theorem fullRecordGapTerm06228_eq_value :
    recordGapCenter + 334346 = fullRecordGapValue06228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06228 (fullRecordGapValue06228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06228_not_prime : ¬(recordGapCenter + 334346).Prime := by
  rw [fullRecordGapTerm06228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06228_fast_pow_mod_ne_one

def fullRecordGapValue06229 : Nat := fullRecordGapCenterValue + 334388

theorem fullRecordGapTerm06229_eq_value :
    recordGapCenter + 334388 = fullRecordGapValue06229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06229 (fullRecordGapValue06229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06229_not_prime : ¬(recordGapCenter + 334388).Prime := by
  rw [fullRecordGapTerm06229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06229_fast_pow_mod_ne_one

def fullRecordGapValue06230 : Nat := fullRecordGapCenterValue + 334398

theorem fullRecordGapTerm06230_eq_value :
    recordGapCenter + 334398 = fullRecordGapValue06230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06230 (fullRecordGapValue06230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06230_not_prime : ¬(recordGapCenter + 334398).Prime := by
  rw [fullRecordGapTerm06230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06230_fast_pow_mod_ne_one

def fullRecordGapValue06231 : Nat := fullRecordGapCenterValue + 334556

theorem fullRecordGapTerm06231_eq_value :
    recordGapCenter + 334556 = fullRecordGapValue06231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06231 (fullRecordGapValue06231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06231_not_prime : ¬(recordGapCenter + 334556).Prime := by
  rw [fullRecordGapTerm06231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06231_fast_pow_mod_ne_one

def fullRecordGapValue06232 : Nat := fullRecordGapCenterValue + 334622

theorem fullRecordGapTerm06232_eq_value :
    recordGapCenter + 334622 = fullRecordGapValue06232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06232 (fullRecordGapValue06232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06232_not_prime : ¬(recordGapCenter + 334622).Prime := by
  rw [fullRecordGapTerm06232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06232_fast_pow_mod_ne_one

def fullRecordGapValue06233 : Nat := fullRecordGapCenterValue + 334652

theorem fullRecordGapTerm06233_eq_value :
    recordGapCenter + 334652 = fullRecordGapValue06233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06233 (fullRecordGapValue06233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06233_not_prime : ¬(recordGapCenter + 334652).Prime := by
  rw [fullRecordGapTerm06233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06233_fast_pow_mod_ne_one

def fullRecordGapValue06234 : Nat := fullRecordGapCenterValue + 334868

theorem fullRecordGapTerm06234_eq_value :
    recordGapCenter + 334868 = fullRecordGapValue06234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06234 (fullRecordGapValue06234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06234_not_prime : ¬(recordGapCenter + 334868).Prime := by
  rw [fullRecordGapTerm06234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06234_fast_pow_mod_ne_one

def fullRecordGapValue06235 : Nat := fullRecordGapCenterValue + 334982

theorem fullRecordGapTerm06235_eq_value :
    recordGapCenter + 334982 = fullRecordGapValue06235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06235 (fullRecordGapValue06235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06235_not_prime : ¬(recordGapCenter + 334982).Prime := by
  rw [fullRecordGapTerm06235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06235_fast_pow_mod_ne_one

def fullRecordGapValue06236 : Nat := fullRecordGapCenterValue + 335058

theorem fullRecordGapTerm06236_eq_value :
    recordGapCenter + 335058 = fullRecordGapValue06236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06236 (fullRecordGapValue06236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06236_not_prime : ¬(recordGapCenter + 335058).Prime := by
  rw [fullRecordGapTerm06236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06236_fast_pow_mod_ne_one

def fullRecordGapValue06237 : Nat := fullRecordGapCenterValue + 335186

theorem fullRecordGapTerm06237_eq_value :
    recordGapCenter + 335186 = fullRecordGapValue06237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06237 (fullRecordGapValue06237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06237_not_prime : ¬(recordGapCenter + 335186).Prime := by
  rw [fullRecordGapTerm06237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06237_fast_pow_mod_ne_one

def fullRecordGapValue06238 : Nat := fullRecordGapCenterValue + 335252

theorem fullRecordGapTerm06238_eq_value :
    recordGapCenter + 335252 = fullRecordGapValue06238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06238 (fullRecordGapValue06238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06238_not_prime : ¬(recordGapCenter + 335252).Prime := by
  rw [fullRecordGapTerm06238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06238_fast_pow_mod_ne_one

def fullRecordGapValue06239 : Nat := fullRecordGapCenterValue + 335366

theorem fullRecordGapTerm06239_eq_value :
    recordGapCenter + 335366 = fullRecordGapValue06239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06239 (fullRecordGapValue06239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06239_not_prime : ¬(recordGapCenter + 335366).Prime := by
  rw [fullRecordGapTerm06239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06239_fast_pow_mod_ne_one

def fullRecordGapValue06240 : Nat := fullRecordGapCenterValue + 335372

theorem fullRecordGapTerm06240_eq_value :
    recordGapCenter + 335372 = fullRecordGapValue06240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06240 (fullRecordGapValue06240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06240_not_prime : ¬(recordGapCenter + 335372).Prime := by
  rw [fullRecordGapTerm06240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06240_fast_pow_mod_ne_one

def fullRecordGapValue06241 : Nat := fullRecordGapCenterValue + 335406

theorem fullRecordGapTerm06241_eq_value :
    recordGapCenter + 335406 = fullRecordGapValue06241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06241 (fullRecordGapValue06241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06241_not_prime : ¬(recordGapCenter + 335406).Prime := by
  rw [fullRecordGapTerm06241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06241_fast_pow_mod_ne_one

def fullRecordGapValue06242 : Nat := fullRecordGapCenterValue + 335598

theorem fullRecordGapTerm06242_eq_value :
    recordGapCenter + 335598 = fullRecordGapValue06242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06242 (fullRecordGapValue06242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06242_not_prime : ¬(recordGapCenter + 335598).Prime := by
  rw [fullRecordGapTerm06242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06242_fast_pow_mod_ne_one

def fullRecordGapValue06243 : Nat := fullRecordGapCenterValue + 335732

theorem fullRecordGapTerm06243_eq_value :
    recordGapCenter + 335732 = fullRecordGapValue06243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06243 (fullRecordGapValue06243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06243_not_prime : ¬(recordGapCenter + 335732).Prime := by
  rw [fullRecordGapTerm06243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06243_fast_pow_mod_ne_one

def fullRecordGapValue06244 : Nat := fullRecordGapCenterValue + 335756

theorem fullRecordGapTerm06244_eq_value :
    recordGapCenter + 335756 = fullRecordGapValue06244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06244 (fullRecordGapValue06244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06244_not_prime : ¬(recordGapCenter + 335756).Prime := by
  rw [fullRecordGapTerm06244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06244_fast_pow_mod_ne_one

def fullRecordGapValue06245 : Nat := fullRecordGapCenterValue + 335876

theorem fullRecordGapTerm06245_eq_value :
    recordGapCenter + 335876 = fullRecordGapValue06245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06245 (fullRecordGapValue06245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06245_not_prime : ¬(recordGapCenter + 335876).Prime := by
  rw [fullRecordGapTerm06245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06245_fast_pow_mod_ne_one

def fullRecordGapValue06246 : Nat := fullRecordGapCenterValue + 335906

theorem fullRecordGapTerm06246_eq_value :
    recordGapCenter + 335906 = fullRecordGapValue06246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06246 (fullRecordGapValue06246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06246_not_prime : ¬(recordGapCenter + 335906).Prime := by
  rw [fullRecordGapTerm06246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06246_fast_pow_mod_ne_one

def fullRecordGapValue06247 : Nat := fullRecordGapCenterValue + 335982

theorem fullRecordGapTerm06247_eq_value :
    recordGapCenter + 335982 = fullRecordGapValue06247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06247 (fullRecordGapValue06247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06247_not_prime : ¬(recordGapCenter + 335982).Prime := by
  rw [fullRecordGapTerm06247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06247_fast_pow_mod_ne_one

def fullRecordGapValue06248 : Nat := fullRecordGapCenterValue + 336018

theorem fullRecordGapTerm06248_eq_value :
    recordGapCenter + 336018 = fullRecordGapValue06248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06248 (fullRecordGapValue06248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06248_not_prime : ¬(recordGapCenter + 336018).Prime := by
  rw [fullRecordGapTerm06248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06248_fast_pow_mod_ne_one

def fullRecordGapValue06249 : Nat := fullRecordGapCenterValue + 336026

theorem fullRecordGapTerm06249_eq_value :
    recordGapCenter + 336026 = fullRecordGapValue06249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06249 (fullRecordGapValue06249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06249_not_prime : ¬(recordGapCenter + 336026).Prime := by
  rw [fullRecordGapTerm06249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06249_fast_pow_mod_ne_one

def fullRecordGapValue06250 : Nat := fullRecordGapCenterValue + 336086

theorem fullRecordGapTerm06250_eq_value :
    recordGapCenter + 336086 = fullRecordGapValue06250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06250 (fullRecordGapValue06250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06250_not_prime : ¬(recordGapCenter + 336086).Prime := by
  rw [fullRecordGapTerm06250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06250_fast_pow_mod_ne_one

def fullRecordGapValue06251 : Nat := fullRecordGapCenterValue + 336236

theorem fullRecordGapTerm06251_eq_value :
    recordGapCenter + 336236 = fullRecordGapValue06251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06251 (fullRecordGapValue06251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06251_not_prime : ¬(recordGapCenter + 336236).Prime := by
  rw [fullRecordGapTerm06251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06251_fast_pow_mod_ne_one

def fullRecordGapValue06252 : Nat := fullRecordGapCenterValue + 336506

theorem fullRecordGapTerm06252_eq_value :
    recordGapCenter + 336506 = fullRecordGapValue06252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06252 (fullRecordGapValue06252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06252_not_prime : ¬(recordGapCenter + 336506).Prime := by
  rw [fullRecordGapTerm06252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06252_fast_pow_mod_ne_one

def fullRecordGapValue06253 : Nat := fullRecordGapCenterValue + 336522

theorem fullRecordGapTerm06253_eq_value :
    recordGapCenter + 336522 = fullRecordGapValue06253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06253 (fullRecordGapValue06253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06253_not_prime : ¬(recordGapCenter + 336522).Prime := by
  rw [fullRecordGapTerm06253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06253_fast_pow_mod_ne_one

def fullRecordGapValue06254 : Nat := fullRecordGapCenterValue + 336548

theorem fullRecordGapTerm06254_eq_value :
    recordGapCenter + 336548 = fullRecordGapValue06254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06254 (fullRecordGapValue06254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06254_not_prime : ¬(recordGapCenter + 336548).Prime := by
  rw [fullRecordGapTerm06254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06254_fast_pow_mod_ne_one

def fullRecordGapValue06255 : Nat := fullRecordGapCenterValue + 336558

theorem fullRecordGapTerm06255_eq_value :
    recordGapCenter + 336558 = fullRecordGapValue06255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06255 (fullRecordGapValue06255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06255_not_prime : ¬(recordGapCenter + 336558).Prime := by
  rw [fullRecordGapTerm06255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06255_fast_pow_mod_ne_one

def fullRecordGapValue06256 : Nat := fullRecordGapCenterValue + 336606

theorem fullRecordGapTerm06256_eq_value :
    recordGapCenter + 336606 = fullRecordGapValue06256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06256 (fullRecordGapValue06256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06256_not_prime : ¬(recordGapCenter + 336606).Prime := by
  rw [fullRecordGapTerm06256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06256_fast_pow_mod_ne_one

def fullRecordGapValue06257 : Nat := fullRecordGapCenterValue + 336738

theorem fullRecordGapTerm06257_eq_value :
    recordGapCenter + 336738 = fullRecordGapValue06257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06257 (fullRecordGapValue06257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06257_not_prime : ¬(recordGapCenter + 336738).Prime := by
  rw [fullRecordGapTerm06257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06257_fast_pow_mod_ne_one

def fullRecordGapValue06258 : Nat := fullRecordGapCenterValue + 336798

theorem fullRecordGapTerm06258_eq_value :
    recordGapCenter + 336798 = fullRecordGapValue06258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06258 (fullRecordGapValue06258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06258_not_prime : ¬(recordGapCenter + 336798).Prime := by
  rw [fullRecordGapTerm06258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06258_fast_pow_mod_ne_one

def fullRecordGapValue06259 : Nat := fullRecordGapCenterValue + 336956

theorem fullRecordGapTerm06259_eq_value :
    recordGapCenter + 336956 = fullRecordGapValue06259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06259 (fullRecordGapValue06259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06259_not_prime : ¬(recordGapCenter + 336956).Prime := by
  rw [fullRecordGapTerm06259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06259_fast_pow_mod_ne_one

def fullRecordGapValue06260 : Nat := fullRecordGapCenterValue + 336962

theorem fullRecordGapTerm06260_eq_value :
    recordGapCenter + 336962 = fullRecordGapValue06260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06260 (fullRecordGapValue06260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06260_not_prime : ¬(recordGapCenter + 336962).Prime := by
  rw [fullRecordGapTerm06260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06260_fast_pow_mod_ne_one

def fullRecordGapValue06261 : Nat := fullRecordGapCenterValue + 336998

theorem fullRecordGapTerm06261_eq_value :
    recordGapCenter + 336998 = fullRecordGapValue06261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06261 (fullRecordGapValue06261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06261_not_prime : ¬(recordGapCenter + 336998).Prime := by
  rw [fullRecordGapTerm06261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06261_fast_pow_mod_ne_one

def fullRecordGapValue06262 : Nat := fullRecordGapCenterValue + 337026

theorem fullRecordGapTerm06262_eq_value :
    recordGapCenter + 337026 = fullRecordGapValue06262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06262 (fullRecordGapValue06262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06262_not_prime : ¬(recordGapCenter + 337026).Prime := by
  rw [fullRecordGapTerm06262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06262_fast_pow_mod_ne_one

def fullRecordGapValue06263 : Nat := fullRecordGapCenterValue + 337118

theorem fullRecordGapTerm06263_eq_value :
    recordGapCenter + 337118 = fullRecordGapValue06263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06263 (fullRecordGapValue06263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06263_not_prime : ¬(recordGapCenter + 337118).Prime := by
  rw [fullRecordGapTerm06263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06263_fast_pow_mod_ne_one

def fullRecordGapValue06264 : Nat := fullRecordGapCenterValue + 337242

theorem fullRecordGapTerm06264_eq_value :
    recordGapCenter + 337242 = fullRecordGapValue06264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06264 (fullRecordGapValue06264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06264_not_prime : ¬(recordGapCenter + 337242).Prime := by
  rw [fullRecordGapTerm06264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06264_fast_pow_mod_ne_one

def fullRecordGapValue06265 : Nat := fullRecordGapCenterValue + 337286

theorem fullRecordGapTerm06265_eq_value :
    recordGapCenter + 337286 = fullRecordGapValue06265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06265 (fullRecordGapValue06265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06265_not_prime : ¬(recordGapCenter + 337286).Prime := by
  rw [fullRecordGapTerm06265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06265_fast_pow_mod_ne_one

def fullRecordGapValue06266 : Nat := fullRecordGapCenterValue + 337422

theorem fullRecordGapTerm06266_eq_value :
    recordGapCenter + 337422 = fullRecordGapValue06266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06266 (fullRecordGapValue06266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06266_not_prime : ¬(recordGapCenter + 337422).Prime := by
  rw [fullRecordGapTerm06266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06266_fast_pow_mod_ne_one

def fullRecordGapValue06267 : Nat := fullRecordGapCenterValue + 337500

theorem fullRecordGapTerm06267_eq_value :
    recordGapCenter + 337500 = fullRecordGapValue06267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06267 (fullRecordGapValue06267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06267_not_prime : ¬(recordGapCenter + 337500).Prime := by
  rw [fullRecordGapTerm06267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06267_fast_pow_mod_ne_one

def fullRecordGapValue06268 : Nat := fullRecordGapCenterValue + 337556

theorem fullRecordGapTerm06268_eq_value :
    recordGapCenter + 337556 = fullRecordGapValue06268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06268 (fullRecordGapValue06268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06268_not_prime : ¬(recordGapCenter + 337556).Prime := by
  rw [fullRecordGapTerm06268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06268_fast_pow_mod_ne_one

def fullRecordGapValue06269 : Nat := fullRecordGapCenterValue + 337562

theorem fullRecordGapTerm06269_eq_value :
    recordGapCenter + 337562 = fullRecordGapValue06269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06269 (fullRecordGapValue06269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06269_not_prime : ¬(recordGapCenter + 337562).Prime := by
  rw [fullRecordGapTerm06269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06269_fast_pow_mod_ne_one

def fullRecordGapValue06270 : Nat := fullRecordGapCenterValue + 337802

theorem fullRecordGapTerm06270_eq_value :
    recordGapCenter + 337802 = fullRecordGapValue06270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06270 (fullRecordGapValue06270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06270_not_prime : ¬(recordGapCenter + 337802).Prime := by
  rw [fullRecordGapTerm06270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06270_fast_pow_mod_ne_one

def fullRecordGapValue06271 : Nat := fullRecordGapCenterValue + 338126

theorem fullRecordGapTerm06271_eq_value :
    recordGapCenter + 338126 = fullRecordGapValue06271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06271 (fullRecordGapValue06271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06271_not_prime : ¬(recordGapCenter + 338126).Prime := by
  rw [fullRecordGapTerm06271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06271_fast_pow_mod_ne_one

def fullRecordGapValue06272 : Nat := fullRecordGapCenterValue + 338138

theorem fullRecordGapTerm06272_eq_value :
    recordGapCenter + 338138 = fullRecordGapValue06272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06272 (fullRecordGapValue06272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06272_not_prime : ¬(recordGapCenter + 338138).Prime := by
  rw [fullRecordGapTerm06272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06272_fast_pow_mod_ne_one

def fullRecordGapValue06273 : Nat := fullRecordGapCenterValue + 338222

theorem fullRecordGapTerm06273_eq_value :
    recordGapCenter + 338222 = fullRecordGapValue06273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06273 (fullRecordGapValue06273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06273_not_prime : ¬(recordGapCenter + 338222).Prime := by
  rw [fullRecordGapTerm06273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06273_fast_pow_mod_ne_one

def fullRecordGapValue06274 : Nat := fullRecordGapCenterValue + 338262

theorem fullRecordGapTerm06274_eq_value :
    recordGapCenter + 338262 = fullRecordGapValue06274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06274 (fullRecordGapValue06274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06274_not_prime : ¬(recordGapCenter + 338262).Prime := by
  rw [fullRecordGapTerm06274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06274_fast_pow_mod_ne_one

def fullRecordGapValue06275 : Nat := fullRecordGapCenterValue + 338502

theorem fullRecordGapTerm06275_eq_value :
    recordGapCenter + 338502 = fullRecordGapValue06275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06275 (fullRecordGapValue06275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06275_not_prime : ¬(recordGapCenter + 338502).Prime := by
  rw [fullRecordGapTerm06275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06275_fast_pow_mod_ne_one

def fullRecordGapValue06276 : Nat := fullRecordGapCenterValue + 338586

theorem fullRecordGapTerm06276_eq_value :
    recordGapCenter + 338586 = fullRecordGapValue06276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06276 (fullRecordGapValue06276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06276_not_prime : ¬(recordGapCenter + 338586).Prime := by
  rw [fullRecordGapTerm06276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06276_fast_pow_mod_ne_one

def fullRecordGapValue06277 : Nat := fullRecordGapCenterValue + 338612

theorem fullRecordGapTerm06277_eq_value :
    recordGapCenter + 338612 = fullRecordGapValue06277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06277 (fullRecordGapValue06277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06277_not_prime : ¬(recordGapCenter + 338612).Prime := by
  rw [fullRecordGapTerm06277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06277_fast_pow_mod_ne_one

def fullRecordGapValue06278 : Nat := fullRecordGapCenterValue + 338636

theorem fullRecordGapTerm06278_eq_value :
    recordGapCenter + 338636 = fullRecordGapValue06278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06278 (fullRecordGapValue06278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06278_not_prime : ¬(recordGapCenter + 338636).Prime := by
  rw [fullRecordGapTerm06278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06278_fast_pow_mod_ne_one

def fullRecordGapValue06279 : Nat := fullRecordGapCenterValue + 338942

theorem fullRecordGapTerm06279_eq_value :
    recordGapCenter + 338942 = fullRecordGapValue06279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06279 (fullRecordGapValue06279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06279_not_prime : ¬(recordGapCenter + 338942).Prime := by
  rw [fullRecordGapTerm06279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06279_fast_pow_mod_ne_one

def fullRecordGapValue06280 : Nat := fullRecordGapCenterValue + 338948

theorem fullRecordGapTerm06280_eq_value :
    recordGapCenter + 338948 = fullRecordGapValue06280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06280 (fullRecordGapValue06280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06280_not_prime : ¬(recordGapCenter + 338948).Prime := by
  rw [fullRecordGapTerm06280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06280_fast_pow_mod_ne_one

def fullRecordGapValue06281 : Nat := fullRecordGapCenterValue + 338966

theorem fullRecordGapTerm06281_eq_value :
    recordGapCenter + 338966 = fullRecordGapValue06281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06281 (fullRecordGapValue06281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06281_not_prime : ¬(recordGapCenter + 338966).Prime := by
  rw [fullRecordGapTerm06281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06281_fast_pow_mod_ne_one

def fullRecordGapValue06282 : Nat := fullRecordGapCenterValue + 338978

theorem fullRecordGapTerm06282_eq_value :
    recordGapCenter + 338978 = fullRecordGapValue06282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06282 (fullRecordGapValue06282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06282_not_prime : ¬(recordGapCenter + 338978).Prime := by
  rw [fullRecordGapTerm06282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06282_fast_pow_mod_ne_one

def fullRecordGapValue06283 : Nat := fullRecordGapCenterValue + 339006

theorem fullRecordGapTerm06283_eq_value :
    recordGapCenter + 339006 = fullRecordGapValue06283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06283 (fullRecordGapValue06283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06283_not_prime : ¬(recordGapCenter + 339006).Prime := by
  rw [fullRecordGapTerm06283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06283_fast_pow_mod_ne_one

def fullRecordGapValue06284 : Nat := fullRecordGapCenterValue + 339018

theorem fullRecordGapTerm06284_eq_value :
    recordGapCenter + 339018 = fullRecordGapValue06284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06284 (fullRecordGapValue06284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06284_not_prime : ¬(recordGapCenter + 339018).Prime := by
  rw [fullRecordGapTerm06284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06284_fast_pow_mod_ne_one

def fullRecordGapValue06285 : Nat := fullRecordGapCenterValue + 339182

theorem fullRecordGapTerm06285_eq_value :
    recordGapCenter + 339182 = fullRecordGapValue06285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06285 (fullRecordGapValue06285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06285_not_prime : ¬(recordGapCenter + 339182).Prime := by
  rw [fullRecordGapTerm06285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06285_fast_pow_mod_ne_one

def fullRecordGapValue06286 : Nat := fullRecordGapCenterValue + 339186

theorem fullRecordGapTerm06286_eq_value :
    recordGapCenter + 339186 = fullRecordGapValue06286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06286 (fullRecordGapValue06286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06286_not_prime : ¬(recordGapCenter + 339186).Prime := by
  rw [fullRecordGapTerm06286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06286_fast_pow_mod_ne_one

def fullRecordGapValue06287 : Nat := fullRecordGapCenterValue + 339266

theorem fullRecordGapTerm06287_eq_value :
    recordGapCenter + 339266 = fullRecordGapValue06287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06287 (fullRecordGapValue06287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06287_not_prime : ¬(recordGapCenter + 339266).Prime := by
  rw [fullRecordGapTerm06287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06287_fast_pow_mod_ne_one

def fullRecordGapValue06288 : Nat := fullRecordGapCenterValue + 339278

theorem fullRecordGapTerm06288_eq_value :
    recordGapCenter + 339278 = fullRecordGapValue06288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06288 (fullRecordGapValue06288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06288_not_prime : ¬(recordGapCenter + 339278).Prime := by
  rw [fullRecordGapTerm06288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06288_fast_pow_mod_ne_one

def fullRecordGapValue06289 : Nat := fullRecordGapCenterValue + 339428

theorem fullRecordGapTerm06289_eq_value :
    recordGapCenter + 339428 = fullRecordGapValue06289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06289 (fullRecordGapValue06289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06289_not_prime : ¬(recordGapCenter + 339428).Prime := by
  rw [fullRecordGapTerm06289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06289_fast_pow_mod_ne_one

def fullRecordGapValue06290 : Nat := fullRecordGapCenterValue + 339546

theorem fullRecordGapTerm06290_eq_value :
    recordGapCenter + 339546 = fullRecordGapValue06290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06290 (fullRecordGapValue06290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06290_not_prime : ¬(recordGapCenter + 339546).Prime := by
  rw [fullRecordGapTerm06290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06290_fast_pow_mod_ne_one

def fullRecordGapValue06291 : Nat := fullRecordGapCenterValue + 339686

theorem fullRecordGapTerm06291_eq_value :
    recordGapCenter + 339686 = fullRecordGapValue06291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06291 (fullRecordGapValue06291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06291_not_prime : ¬(recordGapCenter + 339686).Prime := by
  rw [fullRecordGapTerm06291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06291_fast_pow_mod_ne_one

def fullRecordGapValue06292 : Nat := fullRecordGapCenterValue + 339798

theorem fullRecordGapTerm06292_eq_value :
    recordGapCenter + 339798 = fullRecordGapValue06292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06292 (fullRecordGapValue06292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06292_not_prime : ¬(recordGapCenter + 339798).Prime := by
  rw [fullRecordGapTerm06292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06292_fast_pow_mod_ne_one

def fullRecordGapValue06293 : Nat := fullRecordGapCenterValue + 339866

theorem fullRecordGapTerm06293_eq_value :
    recordGapCenter + 339866 = fullRecordGapValue06293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06293 (fullRecordGapValue06293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06293_not_prime : ¬(recordGapCenter + 339866).Prime := by
  rw [fullRecordGapTerm06293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06293_fast_pow_mod_ne_one

def fullRecordGapValue06294 : Nat := fullRecordGapCenterValue + 339902

theorem fullRecordGapTerm06294_eq_value :
    recordGapCenter + 339902 = fullRecordGapValue06294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06294 (fullRecordGapValue06294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06294_not_prime : ¬(recordGapCenter + 339902).Prime := by
  rw [fullRecordGapTerm06294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06294_fast_pow_mod_ne_one

def fullRecordGapValue06295 : Nat := fullRecordGapCenterValue + 340026

theorem fullRecordGapTerm06295_eq_value :
    recordGapCenter + 340026 = fullRecordGapValue06295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06295 (fullRecordGapValue06295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06295_not_prime : ¬(recordGapCenter + 340026).Prime := by
  rw [fullRecordGapTerm06295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06295_fast_pow_mod_ne_one

def fullRecordGapValue06296 : Nat := fullRecordGapCenterValue + 340058

theorem fullRecordGapTerm06296_eq_value :
    recordGapCenter + 340058 = fullRecordGapValue06296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06296 (fullRecordGapValue06296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06296_not_prime : ¬(recordGapCenter + 340058).Prime := by
  rw [fullRecordGapTerm06296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06296_fast_pow_mod_ne_one

def fullRecordGapValue06297 : Nat := fullRecordGapCenterValue + 340086

theorem fullRecordGapTerm06297_eq_value :
    recordGapCenter + 340086 = fullRecordGapValue06297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06297 (fullRecordGapValue06297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06297_not_prime : ¬(recordGapCenter + 340086).Prime := by
  rw [fullRecordGapTerm06297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06297_fast_pow_mod_ne_one

def fullRecordGapValue06298 : Nat := fullRecordGapCenterValue + 340148

theorem fullRecordGapTerm06298_eq_value :
    recordGapCenter + 340148 = fullRecordGapValue06298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06298 (fullRecordGapValue06298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06298_not_prime : ¬(recordGapCenter + 340148).Prime := by
  rw [fullRecordGapTerm06298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06298_fast_pow_mod_ne_one

def fullRecordGapValue06299 : Nat := fullRecordGapCenterValue + 340436

theorem fullRecordGapTerm06299_eq_value :
    recordGapCenter + 340436 = fullRecordGapValue06299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06299 (fullRecordGapValue06299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06299_not_prime : ¬(recordGapCenter + 340436).Prime := by
  rw [fullRecordGapTerm06299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06299_fast_pow_mod_ne_one

def fullRecordGapValue06300 : Nat := fullRecordGapCenterValue + 340526

theorem fullRecordGapTerm06300_eq_value :
    recordGapCenter + 340526 = fullRecordGapValue06300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06300 (fullRecordGapValue06300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06300_not_prime : ¬(recordGapCenter + 340526).Prime := by
  rw [fullRecordGapTerm06300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06300_fast_pow_mod_ne_one

def fullRecordGapValue06301 : Nat := fullRecordGapCenterValue + 340698

theorem fullRecordGapTerm06301_eq_value :
    recordGapCenter + 340698 = fullRecordGapValue06301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06301 (fullRecordGapValue06301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06301_not_prime : ¬(recordGapCenter + 340698).Prime := by
  rw [fullRecordGapTerm06301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06301_fast_pow_mod_ne_one

def fullRecordGapValue06302 : Nat := fullRecordGapCenterValue + 340778

theorem fullRecordGapTerm06302_eq_value :
    recordGapCenter + 340778 = fullRecordGapValue06302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06302 (fullRecordGapValue06302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06302_not_prime : ¬(recordGapCenter + 340778).Prime := by
  rw [fullRecordGapTerm06302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06302_fast_pow_mod_ne_one

def fullRecordGapValue06303 : Nat := fullRecordGapCenterValue + 340796

theorem fullRecordGapTerm06303_eq_value :
    recordGapCenter + 340796 = fullRecordGapValue06303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06303 (fullRecordGapValue06303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06303_not_prime : ¬(recordGapCenter + 340796).Prime := by
  rw [fullRecordGapTerm06303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06303_fast_pow_mod_ne_one

def fullRecordGapValue06304 : Nat := fullRecordGapCenterValue + 340946

theorem fullRecordGapTerm06304_eq_value :
    recordGapCenter + 340946 = fullRecordGapValue06304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06304 (fullRecordGapValue06304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06304_not_prime : ¬(recordGapCenter + 340946).Prime := by
  rw [fullRecordGapTerm06304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06304_fast_pow_mod_ne_one

def fullRecordGapValue06305 : Nat := fullRecordGapCenterValue + 340988

theorem fullRecordGapTerm06305_eq_value :
    recordGapCenter + 340988 = fullRecordGapValue06305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06305 (fullRecordGapValue06305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06305_not_prime : ¬(recordGapCenter + 340988).Prime := by
  rw [fullRecordGapTerm06305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06305_fast_pow_mod_ne_one

def fullRecordGapValue06306 : Nat := fullRecordGapCenterValue + 341006

theorem fullRecordGapTerm06306_eq_value :
    recordGapCenter + 341006 = fullRecordGapValue06306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06306 (fullRecordGapValue06306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06306_not_prime : ¬(recordGapCenter + 341006).Prime := by
  rw [fullRecordGapTerm06306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06306_fast_pow_mod_ne_one

def fullRecordGapValue06307 : Nat := fullRecordGapCenterValue + 341036

theorem fullRecordGapTerm06307_eq_value :
    recordGapCenter + 341036 = fullRecordGapValue06307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06307 (fullRecordGapValue06307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06307_not_prime : ¬(recordGapCenter + 341036).Prime := by
  rw [fullRecordGapTerm06307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06307_fast_pow_mod_ne_one

def fullRecordGapValue06308 : Nat := fullRecordGapCenterValue + 341058

theorem fullRecordGapTerm06308_eq_value :
    recordGapCenter + 341058 = fullRecordGapValue06308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06308 (fullRecordGapValue06308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06308_not_prime : ¬(recordGapCenter + 341058).Prime := by
  rw [fullRecordGapTerm06308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06308_fast_pow_mod_ne_one

def fullRecordGapValue06309 : Nat := fullRecordGapCenterValue + 341346

theorem fullRecordGapTerm06309_eq_value :
    recordGapCenter + 341346 = fullRecordGapValue06309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06309 (fullRecordGapValue06309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06309_not_prime : ¬(recordGapCenter + 341346).Prime := by
  rw [fullRecordGapTerm06309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06309_fast_pow_mod_ne_one

def fullRecordGapValue06310 : Nat := fullRecordGapCenterValue + 341378

theorem fullRecordGapTerm06310_eq_value :
    recordGapCenter + 341378 = fullRecordGapValue06310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06310 (fullRecordGapValue06310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06310_not_prime : ¬(recordGapCenter + 341378).Prime := by
  rw [fullRecordGapTerm06310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06310_fast_pow_mod_ne_one

def fullRecordGapValue06311 : Nat := fullRecordGapCenterValue + 341538

theorem fullRecordGapTerm06311_eq_value :
    recordGapCenter + 341538 = fullRecordGapValue06311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06311 (fullRecordGapValue06311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06311_not_prime : ¬(recordGapCenter + 341538).Prime := by
  rw [fullRecordGapTerm06311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06311_fast_pow_mod_ne_one

def fullRecordGapValue06312 : Nat := fullRecordGapCenterValue + 341646

theorem fullRecordGapTerm06312_eq_value :
    recordGapCenter + 341646 = fullRecordGapValue06312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06312 (fullRecordGapValue06312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06312_not_prime : ¬(recordGapCenter + 341646).Prime := by
  rw [fullRecordGapTerm06312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06312_fast_pow_mod_ne_one

def fullRecordGapValue06313 : Nat := fullRecordGapCenterValue + 341708

theorem fullRecordGapTerm06313_eq_value :
    recordGapCenter + 341708 = fullRecordGapValue06313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06313 (fullRecordGapValue06313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06313_not_prime : ¬(recordGapCenter + 341708).Prime := by
  rw [fullRecordGapTerm06313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06313_fast_pow_mod_ne_one

def fullRecordGapValue06314 : Nat := fullRecordGapCenterValue + 341762

theorem fullRecordGapTerm06314_eq_value :
    recordGapCenter + 341762 = fullRecordGapValue06314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06314 (fullRecordGapValue06314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06314_not_prime : ¬(recordGapCenter + 341762).Prime := by
  rw [fullRecordGapTerm06314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06314_fast_pow_mod_ne_one

def fullRecordGapValue06315 : Nat := fullRecordGapCenterValue + 341798

theorem fullRecordGapTerm06315_eq_value :
    recordGapCenter + 341798 = fullRecordGapValue06315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06315 (fullRecordGapValue06315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06315_not_prime : ¬(recordGapCenter + 341798).Prime := by
  rw [fullRecordGapTerm06315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06315_fast_pow_mod_ne_one

def fullRecordGapValue06316 : Nat := fullRecordGapCenterValue + 341906

theorem fullRecordGapTerm06316_eq_value :
    recordGapCenter + 341906 = fullRecordGapValue06316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06316 (fullRecordGapValue06316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06316_not_prime : ¬(recordGapCenter + 341906).Prime := by
  rw [fullRecordGapTerm06316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06316_fast_pow_mod_ne_one

def fullRecordGapValue06317 : Nat := fullRecordGapCenterValue + 341948

theorem fullRecordGapTerm06317_eq_value :
    recordGapCenter + 341948 = fullRecordGapValue06317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06317 (fullRecordGapValue06317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06317_not_prime : ¬(recordGapCenter + 341948).Prime := by
  rw [fullRecordGapTerm06317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06317_fast_pow_mod_ne_one

def fullRecordGapValue06318 : Nat := fullRecordGapCenterValue + 341958

theorem fullRecordGapTerm06318_eq_value :
    recordGapCenter + 341958 = fullRecordGapValue06318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06318 (fullRecordGapValue06318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06318_not_prime : ¬(recordGapCenter + 341958).Prime := by
  rw [fullRecordGapTerm06318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06318_fast_pow_mod_ne_one

def fullRecordGapValue06319 : Nat := fullRecordGapCenterValue + 342086

theorem fullRecordGapTerm06319_eq_value :
    recordGapCenter + 342086 = fullRecordGapValue06319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06319 (fullRecordGapValue06319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06319_not_prime : ¬(recordGapCenter + 342086).Prime := by
  rw [fullRecordGapTerm06319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06319_fast_pow_mod_ne_one

def fullRecordGapValue06320 : Nat := fullRecordGapCenterValue + 342092

theorem fullRecordGapTerm06320_eq_value :
    recordGapCenter + 342092 = fullRecordGapValue06320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06320 (fullRecordGapValue06320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06320_not_prime : ¬(recordGapCenter + 342092).Prime := by
  rw [fullRecordGapTerm06320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06320_fast_pow_mod_ne_one

def fullRecordGapValue06321 : Nat := fullRecordGapCenterValue + 342326

theorem fullRecordGapTerm06321_eq_value :
    recordGapCenter + 342326 = fullRecordGapValue06321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06321 (fullRecordGapValue06321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06321_not_prime : ¬(recordGapCenter + 342326).Prime := by
  rw [fullRecordGapTerm06321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06321_fast_pow_mod_ne_one

def fullRecordGapValue06322 : Nat := fullRecordGapCenterValue + 342462

theorem fullRecordGapTerm06322_eq_value :
    recordGapCenter + 342462 = fullRecordGapValue06322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06322 (fullRecordGapValue06322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06322_not_prime : ¬(recordGapCenter + 342462).Prime := by
  rw [fullRecordGapTerm06322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06322_fast_pow_mod_ne_one

def fullRecordGapValue06323 : Nat := fullRecordGapCenterValue + 342542

theorem fullRecordGapTerm06323_eq_value :
    recordGapCenter + 342542 = fullRecordGapValue06323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06323 (fullRecordGapValue06323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06323_not_prime : ¬(recordGapCenter + 342542).Prime := by
  rw [fullRecordGapTerm06323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06323_fast_pow_mod_ne_one

def fullRecordGapValue06324 : Nat := fullRecordGapCenterValue + 342786

theorem fullRecordGapTerm06324_eq_value :
    recordGapCenter + 342786 = fullRecordGapValue06324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06324 (fullRecordGapValue06324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06324_not_prime : ¬(recordGapCenter + 342786).Prime := by
  rw [fullRecordGapTerm06324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06324_fast_pow_mod_ne_one

def fullRecordGapValue06325 : Nat := fullRecordGapCenterValue + 342806

theorem fullRecordGapTerm06325_eq_value :
    recordGapCenter + 342806 = fullRecordGapValue06325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06325 (fullRecordGapValue06325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06325_not_prime : ¬(recordGapCenter + 342806).Prime := by
  rw [fullRecordGapTerm06325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06325_fast_pow_mod_ne_one

def fullRecordGapValue06326 : Nat := fullRecordGapCenterValue + 342878

theorem fullRecordGapTerm06326_eq_value :
    recordGapCenter + 342878 = fullRecordGapValue06326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06326 (fullRecordGapValue06326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06326_not_prime : ¬(recordGapCenter + 342878).Prime := by
  rw [fullRecordGapTerm06326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06326_fast_pow_mod_ne_one

def fullRecordGapValue06327 : Nat := fullRecordGapCenterValue + 343038

theorem fullRecordGapTerm06327_eq_value :
    recordGapCenter + 343038 = fullRecordGapValue06327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06327 (fullRecordGapValue06327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06327_not_prime : ¬(recordGapCenter + 343038).Prime := by
  rw [fullRecordGapTerm06327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06327_fast_pow_mod_ne_one

def fullRecordGapValue06328 : Nat := fullRecordGapCenterValue + 343058

theorem fullRecordGapTerm06328_eq_value :
    recordGapCenter + 343058 = fullRecordGapValue06328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06328 (fullRecordGapValue06328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06328_not_prime : ¬(recordGapCenter + 343058).Prime := by
  rw [fullRecordGapTerm06328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06328_fast_pow_mod_ne_one

def fullRecordGapValue06329 : Nat := fullRecordGapCenterValue + 343106

theorem fullRecordGapTerm06329_eq_value :
    recordGapCenter + 343106 = fullRecordGapValue06329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06329 (fullRecordGapValue06329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06329_not_prime : ¬(recordGapCenter + 343106).Prime := by
  rw [fullRecordGapTerm06329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06329_fast_pow_mod_ne_one

def fullRecordGapValue06330 : Nat := fullRecordGapCenterValue + 343158

theorem fullRecordGapTerm06330_eq_value :
    recordGapCenter + 343158 = fullRecordGapValue06330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06330 (fullRecordGapValue06330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06330_not_prime : ¬(recordGapCenter + 343158).Prime := by
  rw [fullRecordGapTerm06330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06330_fast_pow_mod_ne_one

def fullRecordGapValue06331 : Nat := fullRecordGapCenterValue + 343166

theorem fullRecordGapTerm06331_eq_value :
    recordGapCenter + 343166 = fullRecordGapValue06331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06331 (fullRecordGapValue06331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06331_not_prime : ¬(recordGapCenter + 343166).Prime := by
  rw [fullRecordGapTerm06331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06331_fast_pow_mod_ne_one

def fullRecordGapValue06332 : Nat := fullRecordGapCenterValue + 343268

theorem fullRecordGapTerm06332_eq_value :
    recordGapCenter + 343268 = fullRecordGapValue06332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06332 (fullRecordGapValue06332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06332_not_prime : ¬(recordGapCenter + 343268).Prime := by
  rw [fullRecordGapTerm06332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06332_fast_pow_mod_ne_one

def fullRecordGapValue06333 : Nat := fullRecordGapCenterValue + 343316

theorem fullRecordGapTerm06333_eq_value :
    recordGapCenter + 343316 = fullRecordGapValue06333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06333 (fullRecordGapValue06333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06333_not_prime : ¬(recordGapCenter + 343316).Prime := by
  rw [fullRecordGapTerm06333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06333_fast_pow_mod_ne_one

def fullRecordGapValue06334 : Nat := fullRecordGapCenterValue + 343446

theorem fullRecordGapTerm06334_eq_value :
    recordGapCenter + 343446 = fullRecordGapValue06334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06334 (fullRecordGapValue06334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06334_not_prime : ¬(recordGapCenter + 343446).Prime := by
  rw [fullRecordGapTerm06334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06334_fast_pow_mod_ne_one

def fullRecordGapValue06335 : Nat := fullRecordGapCenterValue + 343506

theorem fullRecordGapTerm06335_eq_value :
    recordGapCenter + 343506 = fullRecordGapValue06335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06335 (fullRecordGapValue06335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06335_not_prime : ¬(recordGapCenter + 343506).Prime := by
  rw [fullRecordGapTerm06335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06335_fast_pow_mod_ne_one

def fullRecordGapValue06336 : Nat := fullRecordGapCenterValue + 343598

theorem fullRecordGapTerm06336_eq_value :
    recordGapCenter + 343598 = fullRecordGapValue06336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06336 (fullRecordGapValue06336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06336_not_prime : ¬(recordGapCenter + 343598).Prime := by
  rw [fullRecordGapTerm06336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06336_fast_pow_mod_ne_one

def fullRecordGapValue06337 : Nat := fullRecordGapCenterValue + 343698

theorem fullRecordGapTerm06337_eq_value :
    recordGapCenter + 343698 = fullRecordGapValue06337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06337 (fullRecordGapValue06337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06337_not_prime : ¬(recordGapCenter + 343698).Prime := by
  rw [fullRecordGapTerm06337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06337_fast_pow_mod_ne_one

def fullRecordGapValue06338 : Nat := fullRecordGapCenterValue + 343778

theorem fullRecordGapTerm06338_eq_value :
    recordGapCenter + 343778 = fullRecordGapValue06338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06338 (fullRecordGapValue06338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06338_not_prime : ¬(recordGapCenter + 343778).Prime := by
  rw [fullRecordGapTerm06338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06338_fast_pow_mod_ne_one

def fullRecordGapValue06339 : Nat := fullRecordGapCenterValue + 343806

theorem fullRecordGapTerm06339_eq_value :
    recordGapCenter + 343806 = fullRecordGapValue06339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06339 (fullRecordGapValue06339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06339_not_prime : ¬(recordGapCenter + 343806).Prime := by
  rw [fullRecordGapTerm06339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06339_fast_pow_mod_ne_one

def fullRecordGapValue06340 : Nat := fullRecordGapCenterValue + 344082

theorem fullRecordGapTerm06340_eq_value :
    recordGapCenter + 344082 = fullRecordGapValue06340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06340 (fullRecordGapValue06340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06340_not_prime : ¬(recordGapCenter + 344082).Prime := by
  rw [fullRecordGapTerm06340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06340_fast_pow_mod_ne_one

def fullRecordGapValue06341 : Nat := fullRecordGapCenterValue + 344108

theorem fullRecordGapTerm06341_eq_value :
    recordGapCenter + 344108 = fullRecordGapValue06341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06341 (fullRecordGapValue06341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06341_not_prime : ¬(recordGapCenter + 344108).Prime := by
  rw [fullRecordGapTerm06341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06341_fast_pow_mod_ne_one

def fullRecordGapValue06342 : Nat := fullRecordGapCenterValue + 344138

theorem fullRecordGapTerm06342_eq_value :
    recordGapCenter + 344138 = fullRecordGapValue06342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06342 (fullRecordGapValue06342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06342_not_prime : ¬(recordGapCenter + 344138).Prime := by
  rw [fullRecordGapTerm06342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06342_fast_pow_mod_ne_one

def fullRecordGapValue06343 : Nat := fullRecordGapCenterValue + 344202

theorem fullRecordGapTerm06343_eq_value :
    recordGapCenter + 344202 = fullRecordGapValue06343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06343 (fullRecordGapValue06343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06343_not_prime : ¬(recordGapCenter + 344202).Prime := by
  rw [fullRecordGapTerm06343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06343_fast_pow_mod_ne_one

def fullRecordGapValue06344 : Nat := fullRecordGapCenterValue + 344306

theorem fullRecordGapTerm06344_eq_value :
    recordGapCenter + 344306 = fullRecordGapValue06344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06344 (fullRecordGapValue06344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06344_not_prime : ¬(recordGapCenter + 344306).Prime := by
  rw [fullRecordGapTerm06344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06344_fast_pow_mod_ne_one

def fullRecordGapValue06345 : Nat := fullRecordGapCenterValue + 344342

theorem fullRecordGapTerm06345_eq_value :
    recordGapCenter + 344342 = fullRecordGapValue06345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06345 (fullRecordGapValue06345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06345_not_prime : ¬(recordGapCenter + 344342).Prime := by
  rw [fullRecordGapTerm06345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06345_fast_pow_mod_ne_one

def fullRecordGapValue06346 : Nat := fullRecordGapCenterValue + 344438

theorem fullRecordGapTerm06346_eq_value :
    recordGapCenter + 344438 = fullRecordGapValue06346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06346 (fullRecordGapValue06346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06346_not_prime : ¬(recordGapCenter + 344438).Prime := by
  rw [fullRecordGapTerm06346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06346_fast_pow_mod_ne_one

def fullRecordGapValue06347 : Nat := fullRecordGapCenterValue + 344478

theorem fullRecordGapTerm06347_eq_value :
    recordGapCenter + 344478 = fullRecordGapValue06347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06347 (fullRecordGapValue06347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06347_not_prime : ¬(recordGapCenter + 344478).Prime := by
  rw [fullRecordGapTerm06347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06347_fast_pow_mod_ne_one

def fullRecordGapValue06348 : Nat := fullRecordGapCenterValue + 344486

theorem fullRecordGapTerm06348_eq_value :
    recordGapCenter + 344486 = fullRecordGapValue06348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06348 (fullRecordGapValue06348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06348_not_prime : ¬(recordGapCenter + 344486).Prime := by
  rw [fullRecordGapTerm06348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06348_fast_pow_mod_ne_one

def fullRecordGapValue06349 : Nat := fullRecordGapCenterValue + 344562

theorem fullRecordGapTerm06349_eq_value :
    recordGapCenter + 344562 = fullRecordGapValue06349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06349 (fullRecordGapValue06349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06349_not_prime : ¬(recordGapCenter + 344562).Prime := by
  rw [fullRecordGapTerm06349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06349_fast_pow_mod_ne_one

def fullRecordGapValue06350 : Nat := fullRecordGapCenterValue + 344642

theorem fullRecordGapTerm06350_eq_value :
    recordGapCenter + 344642 = fullRecordGapValue06350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06350 (fullRecordGapValue06350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06350_not_prime : ¬(recordGapCenter + 344642).Prime := by
  rw [fullRecordGapTerm06350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06350_fast_pow_mod_ne_one

def fullRecordGapValue06351 : Nat := fullRecordGapCenterValue + 344822

theorem fullRecordGapTerm06351_eq_value :
    recordGapCenter + 344822 = fullRecordGapValue06351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06351 (fullRecordGapValue06351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06351_not_prime : ¬(recordGapCenter + 344822).Prime := by
  rw [fullRecordGapTerm06351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06351_fast_pow_mod_ne_one

def fullRecordGapValue06352 : Nat := fullRecordGapCenterValue + 344922

theorem fullRecordGapTerm06352_eq_value :
    recordGapCenter + 344922 = fullRecordGapValue06352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06352 (fullRecordGapValue06352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06352_not_prime : ¬(recordGapCenter + 344922).Prime := by
  rw [fullRecordGapTerm06352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06352_fast_pow_mod_ne_one

def fullRecordGapValue06353 : Nat := fullRecordGapCenterValue + 344960

theorem fullRecordGapTerm06353_eq_value :
    recordGapCenter + 344960 = fullRecordGapValue06353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06353 (fullRecordGapValue06353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06353_not_prime : ¬(recordGapCenter + 344960).Prime := by
  rw [fullRecordGapTerm06353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06353_fast_pow_mod_ne_one

def fullRecordGapValue06354 : Nat := fullRecordGapCenterValue + 344996

theorem fullRecordGapTerm06354_eq_value :
    recordGapCenter + 344996 = fullRecordGapValue06354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06354 (fullRecordGapValue06354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06354_not_prime : ¬(recordGapCenter + 344996).Prime := by
  rw [fullRecordGapTerm06354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06354_fast_pow_mod_ne_one

def fullRecordGapValue06355 : Nat := fullRecordGapCenterValue + 345018

theorem fullRecordGapTerm06355_eq_value :
    recordGapCenter + 345018 = fullRecordGapValue06355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06355 (fullRecordGapValue06355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06355_not_prime : ¬(recordGapCenter + 345018).Prime := by
  rw [fullRecordGapTerm06355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06355_fast_pow_mod_ne_one

def fullRecordGapValue06356 : Nat := fullRecordGapCenterValue + 345038

theorem fullRecordGapTerm06356_eq_value :
    recordGapCenter + 345038 = fullRecordGapValue06356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06356 (fullRecordGapValue06356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06356_not_prime : ¬(recordGapCenter + 345038).Prime := by
  rw [fullRecordGapTerm06356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06356_fast_pow_mod_ne_one

def fullRecordGapValue06357 : Nat := fullRecordGapCenterValue + 345188

theorem fullRecordGapTerm06357_eq_value :
    recordGapCenter + 345188 = fullRecordGapValue06357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06357 (fullRecordGapValue06357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06357_not_prime : ¬(recordGapCenter + 345188).Prime := by
  rw [fullRecordGapTerm06357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06357_fast_pow_mod_ne_one

def fullRecordGapValue06358 : Nat := fullRecordGapCenterValue + 345206

theorem fullRecordGapTerm06358_eq_value :
    recordGapCenter + 345206 = fullRecordGapValue06358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06358 (fullRecordGapValue06358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06358_not_prime : ¬(recordGapCenter + 345206).Prime := by
  rw [fullRecordGapTerm06358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06358_fast_pow_mod_ne_one

def fullRecordGapValue06359 : Nat := fullRecordGapCenterValue + 345272

theorem fullRecordGapTerm06359_eq_value :
    recordGapCenter + 345272 = fullRecordGapValue06359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06359 (fullRecordGapValue06359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06359_not_prime : ¬(recordGapCenter + 345272).Prime := by
  rw [fullRecordGapTerm06359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06359_fast_pow_mod_ne_one

def fullRecordGapValue06360 : Nat := fullRecordGapCenterValue + 345416

theorem fullRecordGapTerm06360_eq_value :
    recordGapCenter + 345416 = fullRecordGapValue06360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06360 (fullRecordGapValue06360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06360_not_prime : ¬(recordGapCenter + 345416).Prime := by
  rw [fullRecordGapTerm06360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06360_fast_pow_mod_ne_one

def fullRecordGapValue06361 : Nat := fullRecordGapCenterValue + 345522

theorem fullRecordGapTerm06361_eq_value :
    recordGapCenter + 345522 = fullRecordGapValue06361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06361 (fullRecordGapValue06361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06361_not_prime : ¬(recordGapCenter + 345522).Prime := by
  rw [fullRecordGapTerm06361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06361_fast_pow_mod_ne_one

def fullRecordGapValue06362 : Nat := fullRecordGapCenterValue + 345602

theorem fullRecordGapTerm06362_eq_value :
    recordGapCenter + 345602 = fullRecordGapValue06362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06362 (fullRecordGapValue06362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06362_not_prime : ¬(recordGapCenter + 345602).Prime := by
  rw [fullRecordGapTerm06362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06362_fast_pow_mod_ne_one

def fullRecordGapValue06363 : Nat := fullRecordGapCenterValue + 345608

theorem fullRecordGapTerm06363_eq_value :
    recordGapCenter + 345608 = fullRecordGapValue06363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06363 (fullRecordGapValue06363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06363_not_prime : ¬(recordGapCenter + 345608).Prime := by
  rw [fullRecordGapTerm06363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06363_fast_pow_mod_ne_one

def fullRecordGapValue06364 : Nat := fullRecordGapCenterValue + 345866

theorem fullRecordGapTerm06364_eq_value :
    recordGapCenter + 345866 = fullRecordGapValue06364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06364 (fullRecordGapValue06364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06364_not_prime : ¬(recordGapCenter + 345866).Prime := by
  rw [fullRecordGapTerm06364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06364_fast_pow_mod_ne_one

def fullRecordGapValue06365 : Nat := fullRecordGapCenterValue + 345896

theorem fullRecordGapTerm06365_eq_value :
    recordGapCenter + 345896 = fullRecordGapValue06365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06365 (fullRecordGapValue06365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06365_not_prime : ¬(recordGapCenter + 345896).Prime := by
  rw [fullRecordGapTerm06365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06365_fast_pow_mod_ne_one

def fullRecordGapValue06366 : Nat := fullRecordGapCenterValue + 345908

theorem fullRecordGapTerm06366_eq_value :
    recordGapCenter + 345908 = fullRecordGapValue06366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06366 (fullRecordGapValue06366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06366_not_prime : ¬(recordGapCenter + 345908).Prime := by
  rw [fullRecordGapTerm06366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06366_fast_pow_mod_ne_one

def fullRecordGapValue06367 : Nat := fullRecordGapCenterValue + 345938

theorem fullRecordGapTerm06367_eq_value :
    recordGapCenter + 345938 = fullRecordGapValue06367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06367 (fullRecordGapValue06367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06367_not_prime : ¬(recordGapCenter + 345938).Prime := by
  rw [fullRecordGapTerm06367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06367_fast_pow_mod_ne_one

def fullRecordGapValue06368 : Nat := fullRecordGapCenterValue + 345986

theorem fullRecordGapTerm06368_eq_value :
    recordGapCenter + 345986 = fullRecordGapValue06368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06368 (fullRecordGapValue06368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06368_not_prime : ¬(recordGapCenter + 345986).Prime := by
  rw [fullRecordGapTerm06368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06368_fast_pow_mod_ne_one

def fullRecordGapValue06369 : Nat := fullRecordGapCenterValue + 346046

theorem fullRecordGapTerm06369_eq_value :
    recordGapCenter + 346046 = fullRecordGapValue06369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06369 (fullRecordGapValue06369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06369_not_prime : ¬(recordGapCenter + 346046).Prime := by
  rw [fullRecordGapTerm06369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06369_fast_pow_mod_ne_one

def fullRecordGapValue06370 : Nat := fullRecordGapCenterValue + 346088

theorem fullRecordGapTerm06370_eq_value :
    recordGapCenter + 346088 = fullRecordGapValue06370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06370 (fullRecordGapValue06370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06370_not_prime : ¬(recordGapCenter + 346088).Prime := by
  rw [fullRecordGapTerm06370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06370_fast_pow_mod_ne_one

def fullRecordGapValue06371 : Nat := fullRecordGapCenterValue + 346278

theorem fullRecordGapTerm06371_eq_value :
    recordGapCenter + 346278 = fullRecordGapValue06371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06371 (fullRecordGapValue06371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06371_not_prime : ¬(recordGapCenter + 346278).Prime := by
  rw [fullRecordGapTerm06371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06371_fast_pow_mod_ne_one

def fullRecordGapValue06372 : Nat := fullRecordGapCenterValue + 346362

theorem fullRecordGapTerm06372_eq_value :
    recordGapCenter + 346362 = fullRecordGapValue06372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06372 (fullRecordGapValue06372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06372_not_prime : ¬(recordGapCenter + 346362).Prime := by
  rw [fullRecordGapTerm06372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06372_fast_pow_mod_ne_one

def fullRecordGapValue06373 : Nat := fullRecordGapCenterValue + 346418

theorem fullRecordGapTerm06373_eq_value :
    recordGapCenter + 346418 = fullRecordGapValue06373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06373 (fullRecordGapValue06373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06373_not_prime : ¬(recordGapCenter + 346418).Prime := by
  rw [fullRecordGapTerm06373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06373_fast_pow_mod_ne_one

def fullRecordGapValue06374 : Nat := fullRecordGapCenterValue + 346586

theorem fullRecordGapTerm06374_eq_value :
    recordGapCenter + 346586 = fullRecordGapValue06374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06374 (fullRecordGapValue06374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06374_not_prime : ¬(recordGapCenter + 346586).Prime := by
  rw [fullRecordGapTerm06374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06374_fast_pow_mod_ne_one

def fullRecordGapValue06375 : Nat := fullRecordGapCenterValue + 346686

theorem fullRecordGapTerm06375_eq_value :
    recordGapCenter + 346686 = fullRecordGapValue06375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06375 (fullRecordGapValue06375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06375_not_prime : ¬(recordGapCenter + 346686).Prime := by
  rw [fullRecordGapTerm06375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06375_fast_pow_mod_ne_one

def fullRecordGapValue06376 : Nat := fullRecordGapCenterValue + 346722

theorem fullRecordGapTerm06376_eq_value :
    recordGapCenter + 346722 = fullRecordGapValue06376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06376 (fullRecordGapValue06376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06376_not_prime : ¬(recordGapCenter + 346722).Prime := by
  rw [fullRecordGapTerm06376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06376_fast_pow_mod_ne_one

def fullRecordGapValue06377 : Nat := fullRecordGapCenterValue + 346746

theorem fullRecordGapTerm06377_eq_value :
    recordGapCenter + 346746 = fullRecordGapValue06377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06377 (fullRecordGapValue06377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06377_not_prime : ¬(recordGapCenter + 346746).Prime := by
  rw [fullRecordGapTerm06377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06377_fast_pow_mod_ne_one

def fullRecordGapValue06378 : Nat := fullRecordGapCenterValue + 346946

theorem fullRecordGapTerm06378_eq_value :
    recordGapCenter + 346946 = fullRecordGapValue06378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06378 (fullRecordGapValue06378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06378_not_prime : ¬(recordGapCenter + 346946).Prime := by
  rw [fullRecordGapTerm06378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06378_fast_pow_mod_ne_one

def fullRecordGapValue06379 : Nat := fullRecordGapCenterValue + 347012

theorem fullRecordGapTerm06379_eq_value :
    recordGapCenter + 347012 = fullRecordGapValue06379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06379 (fullRecordGapValue06379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06379_not_prime : ¬(recordGapCenter + 347012).Prime := by
  rw [fullRecordGapTerm06379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06379_fast_pow_mod_ne_one

def fullRecordGapValue06380 : Nat := fullRecordGapCenterValue + 347118

theorem fullRecordGapTerm06380_eq_value :
    recordGapCenter + 347118 = fullRecordGapValue06380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06380 (fullRecordGapValue06380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06380_not_prime : ¬(recordGapCenter + 347118).Prime := by
  rw [fullRecordGapTerm06380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06380_fast_pow_mod_ne_one

def fullRecordGapValue06381 : Nat := fullRecordGapCenterValue + 347252

theorem fullRecordGapTerm06381_eq_value :
    recordGapCenter + 347252 = fullRecordGapValue06381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06381 (fullRecordGapValue06381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06381_not_prime : ¬(recordGapCenter + 347252).Prime := by
  rw [fullRecordGapTerm06381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06381_fast_pow_mod_ne_one

def fullRecordGapValue06382 : Nat := fullRecordGapCenterValue + 347342

theorem fullRecordGapTerm06382_eq_value :
    recordGapCenter + 347342 = fullRecordGapValue06382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06382 (fullRecordGapValue06382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06382_not_prime : ¬(recordGapCenter + 347342).Prime := by
  rw [fullRecordGapTerm06382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06382_fast_pow_mod_ne_one

def fullRecordGapValue06383 : Nat := fullRecordGapCenterValue + 347348

theorem fullRecordGapTerm06383_eq_value :
    recordGapCenter + 347348 = fullRecordGapValue06383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06383 (fullRecordGapValue06383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06383_not_prime : ¬(recordGapCenter + 347348).Prime := by
  rw [fullRecordGapTerm06383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06383_fast_pow_mod_ne_one

def fullRecordGapValue06384 : Nat := fullRecordGapCenterValue + 347366

theorem fullRecordGapTerm06384_eq_value :
    recordGapCenter + 347366 = fullRecordGapValue06384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06384 (fullRecordGapValue06384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06384_not_prime : ¬(recordGapCenter + 347366).Prime := by
  rw [fullRecordGapTerm06384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06384_fast_pow_mod_ne_one

def fullRecordGapValue06385 : Nat := fullRecordGapCenterValue + 347372

theorem fullRecordGapTerm06385_eq_value :
    recordGapCenter + 347372 = fullRecordGapValue06385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06385 (fullRecordGapValue06385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06385_not_prime : ¬(recordGapCenter + 347372).Prime := by
  rw [fullRecordGapTerm06385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06385_fast_pow_mod_ne_one

def fullRecordGapValue06386 : Nat := fullRecordGapCenterValue + 347406

theorem fullRecordGapTerm06386_eq_value :
    recordGapCenter + 347406 = fullRecordGapValue06386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06386 (fullRecordGapValue06386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06386_not_prime : ¬(recordGapCenter + 347406).Prime := by
  rw [fullRecordGapTerm06386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06386_fast_pow_mod_ne_one

def fullRecordGapValue06387 : Nat := fullRecordGapCenterValue + 347502

theorem fullRecordGapTerm06387_eq_value :
    recordGapCenter + 347502 = fullRecordGapValue06387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06387 (fullRecordGapValue06387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06387_not_prime : ¬(recordGapCenter + 347502).Prime := by
  rw [fullRecordGapTerm06387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06387_fast_pow_mod_ne_one

def fullRecordGapValue06388 : Nat := fullRecordGapCenterValue + 347558

theorem fullRecordGapTerm06388_eq_value :
    recordGapCenter + 347558 = fullRecordGapValue06388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06388 (fullRecordGapValue06388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06388_not_prime : ¬(recordGapCenter + 347558).Prime := by
  rw [fullRecordGapTerm06388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06388_fast_pow_mod_ne_one

def fullRecordGapValue06389 : Nat := fullRecordGapCenterValue + 347658

theorem fullRecordGapTerm06389_eq_value :
    recordGapCenter + 347658 = fullRecordGapValue06389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06389 (fullRecordGapValue06389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06389_not_prime : ¬(recordGapCenter + 347658).Prime := by
  rw [fullRecordGapTerm06389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06389_fast_pow_mod_ne_one

def fullRecordGapValue06390 : Nat := fullRecordGapCenterValue + 347756

theorem fullRecordGapTerm06390_eq_value :
    recordGapCenter + 347756 = fullRecordGapValue06390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06390 (fullRecordGapValue06390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06390_not_prime : ¬(recordGapCenter + 347756).Prime := by
  rw [fullRecordGapTerm06390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06390_fast_pow_mod_ne_one

def fullRecordGapValue06391 : Nat := fullRecordGapCenterValue + 347846

theorem fullRecordGapTerm06391_eq_value :
    recordGapCenter + 347846 = fullRecordGapValue06391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06391 (fullRecordGapValue06391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06391_not_prime : ¬(recordGapCenter + 347846).Prime := by
  rw [fullRecordGapTerm06391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06391_fast_pow_mod_ne_one

def fullRecordGapValue06392 : Nat := fullRecordGapCenterValue + 347862

theorem fullRecordGapTerm06392_eq_value :
    recordGapCenter + 347862 = fullRecordGapValue06392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06392 (fullRecordGapValue06392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06392_not_prime : ¬(recordGapCenter + 347862).Prime := by
  rw [fullRecordGapTerm06392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06392_fast_pow_mod_ne_one

def fullRecordGapValue06393 : Nat := fullRecordGapCenterValue + 347876

theorem fullRecordGapTerm06393_eq_value :
    recordGapCenter + 347876 = fullRecordGapValue06393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06393 (fullRecordGapValue06393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06393_not_prime : ¬(recordGapCenter + 347876).Prime := by
  rw [fullRecordGapTerm06393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06393_fast_pow_mod_ne_one

def fullRecordGapValue06394 : Nat := fullRecordGapCenterValue + 347946

theorem fullRecordGapTerm06394_eq_value :
    recordGapCenter + 347946 = fullRecordGapValue06394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06394 (fullRecordGapValue06394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06394_not_prime : ¬(recordGapCenter + 347946).Prime := by
  rw [fullRecordGapTerm06394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06394_fast_pow_mod_ne_one

def fullRecordGapValue06395 : Nat := fullRecordGapCenterValue + 347972

theorem fullRecordGapTerm06395_eq_value :
    recordGapCenter + 347972 = fullRecordGapValue06395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06395 (fullRecordGapValue06395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06395_not_prime : ¬(recordGapCenter + 347972).Prime := by
  rw [fullRecordGapTerm06395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06395_fast_pow_mod_ne_one

def fullRecordGapValue06396 : Nat := fullRecordGapCenterValue + 348078

theorem fullRecordGapTerm06396_eq_value :
    recordGapCenter + 348078 = fullRecordGapValue06396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06396 (fullRecordGapValue06396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06396_not_prime : ¬(recordGapCenter + 348078).Prime := by
  rw [fullRecordGapTerm06396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06396_fast_pow_mod_ne_one

def fullRecordGapValue06397 : Nat := fullRecordGapCenterValue + 348122

theorem fullRecordGapTerm06397_eq_value :
    recordGapCenter + 348122 = fullRecordGapValue06397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06397 (fullRecordGapValue06397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06397_not_prime : ¬(recordGapCenter + 348122).Prime := by
  rw [fullRecordGapTerm06397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06397_fast_pow_mod_ne_one

def fullRecordGapValue06398 : Nat := fullRecordGapCenterValue + 348162

theorem fullRecordGapTerm06398_eq_value :
    recordGapCenter + 348162 = fullRecordGapValue06398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06398 (fullRecordGapValue06398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06398_not_prime : ¬(recordGapCenter + 348162).Prime := by
  rw [fullRecordGapTerm06398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06398_fast_pow_mod_ne_one

def fullRecordGapValue06399 : Nat := fullRecordGapCenterValue + 348182

theorem fullRecordGapTerm06399_eq_value :
    recordGapCenter + 348182 = fullRecordGapValue06399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06399 (fullRecordGapValue06399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06399_not_prime : ¬(recordGapCenter + 348182).Prime := by
  rw [fullRecordGapTerm06399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06399_fast_pow_mod_ne_one

def fullRecordGapValue06400 : Nat := fullRecordGapCenterValue + 348338

theorem fullRecordGapTerm06400_eq_value :
    recordGapCenter + 348338 = fullRecordGapValue06400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06400 (fullRecordGapValue06400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06400_not_prime : ¬(recordGapCenter + 348338).Prime := by
  rw [fullRecordGapTerm06400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06400_fast_pow_mod_ne_one

end PrimeFactorUnimodality
