import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue04097 : Nat := fullRecordGapCenterValue + 91682

theorem fullRecordGapTerm04097_eq_value :
    recordGapCenter + 91682 = fullRecordGapValue04097 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04097_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04097 (fullRecordGapValue04097 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04097_not_prime : ¬(recordGapCenter + 91682).Prime := by
  rw [fullRecordGapTerm04097_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04097, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04097_fast_pow_mod_ne_one

def fullRecordGapValue04098 : Nat := fullRecordGapCenterValue + 92102

theorem fullRecordGapTerm04098_eq_value :
    recordGapCenter + 92102 = fullRecordGapValue04098 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04098_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04098 (fullRecordGapValue04098 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04098_not_prime : ¬(recordGapCenter + 92102).Prime := by
  rw [fullRecordGapTerm04098_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04098, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04098_fast_pow_mod_ne_one

def fullRecordGapValue04099 : Nat := fullRecordGapCenterValue + 92160

theorem fullRecordGapTerm04099_eq_value :
    recordGapCenter + 92160 = fullRecordGapValue04099 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04099_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04099 (fullRecordGapValue04099 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04099_not_prime : ¬(recordGapCenter + 92160).Prime := by
  rw [fullRecordGapTerm04099_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04099, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04099_fast_pow_mod_ne_one

def fullRecordGapValue04100 : Nat := fullRecordGapCenterValue + 92186

theorem fullRecordGapTerm04100_eq_value :
    recordGapCenter + 92186 = fullRecordGapValue04100 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04100_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04100 (fullRecordGapValue04100 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04100_not_prime : ¬(recordGapCenter + 92186).Prime := by
  rw [fullRecordGapTerm04100_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04100, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04100_fast_pow_mod_ne_one

def fullRecordGapValue04101 : Nat := fullRecordGapCenterValue + 92282

theorem fullRecordGapTerm04101_eq_value :
    recordGapCenter + 92282 = fullRecordGapValue04101 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04101_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04101 (fullRecordGapValue04101 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04101_not_prime : ¬(recordGapCenter + 92282).Prime := by
  rw [fullRecordGapTerm04101_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04101, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04101_fast_pow_mod_ne_one

def fullRecordGapValue04102 : Nat := fullRecordGapCenterValue + 92366

theorem fullRecordGapTerm04102_eq_value :
    recordGapCenter + 92366 = fullRecordGapValue04102 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04102_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04102 (fullRecordGapValue04102 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04102_not_prime : ¬(recordGapCenter + 92366).Prime := by
  rw [fullRecordGapTerm04102_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04102, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04102_fast_pow_mod_ne_one

def fullRecordGapValue04103 : Nat := fullRecordGapCenterValue + 92400

theorem fullRecordGapTerm04103_eq_value :
    recordGapCenter + 92400 = fullRecordGapValue04103 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04103_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04103 (fullRecordGapValue04103 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04103_not_prime : ¬(recordGapCenter + 92400).Prime := by
  rw [fullRecordGapTerm04103_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04103, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04103_fast_pow_mod_ne_one

def fullRecordGapValue04104 : Nat := fullRecordGapCenterValue + 92522

theorem fullRecordGapTerm04104_eq_value :
    recordGapCenter + 92522 = fullRecordGapValue04104 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04104_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04104 (fullRecordGapValue04104 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04104_not_prime : ¬(recordGapCenter + 92522).Prime := by
  rw [fullRecordGapTerm04104_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04104, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04104_fast_pow_mod_ne_one

def fullRecordGapValue04105 : Nat := fullRecordGapCenterValue + 92610

theorem fullRecordGapTerm04105_eq_value :
    recordGapCenter + 92610 = fullRecordGapValue04105 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04105_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04105 (fullRecordGapValue04105 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04105_not_prime : ¬(recordGapCenter + 92610).Prime := by
  rw [fullRecordGapTerm04105_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04105, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04105_fast_pow_mod_ne_one

def fullRecordGapValue04106 : Nat := fullRecordGapCenterValue + 92618

theorem fullRecordGapTerm04106_eq_value :
    recordGapCenter + 92618 = fullRecordGapValue04106 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04106_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04106 (fullRecordGapValue04106 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04106_not_prime : ¬(recordGapCenter + 92618).Prime := by
  rw [fullRecordGapTerm04106_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04106, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04106_fast_pow_mod_ne_one

def fullRecordGapValue04107 : Nat := fullRecordGapCenterValue + 92762

theorem fullRecordGapTerm04107_eq_value :
    recordGapCenter + 92762 = fullRecordGapValue04107 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04107_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04107 (fullRecordGapValue04107 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04107_not_prime : ¬(recordGapCenter + 92762).Prime := by
  rw [fullRecordGapTerm04107_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04107, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04107_fast_pow_mod_ne_one

def fullRecordGapValue04108 : Nat := fullRecordGapCenterValue + 92928

theorem fullRecordGapTerm04108_eq_value :
    recordGapCenter + 92928 = fullRecordGapValue04108 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04108_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04108 (fullRecordGapValue04108 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04108_not_prime : ¬(recordGapCenter + 92928).Prime := by
  rw [fullRecordGapTerm04108_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04108, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04108_fast_pow_mod_ne_one

def fullRecordGapValue04109 : Nat := fullRecordGapCenterValue + 92942

theorem fullRecordGapTerm04109_eq_value :
    recordGapCenter + 92942 = fullRecordGapValue04109 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04109_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04109 (fullRecordGapValue04109 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04109_not_prime : ¬(recordGapCenter + 92942).Prime := by
  rw [fullRecordGapTerm04109_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04109, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04109_fast_pow_mod_ne_one

def fullRecordGapValue04110 : Nat := fullRecordGapCenterValue + 92978

theorem fullRecordGapTerm04110_eq_value :
    recordGapCenter + 92978 = fullRecordGapValue04110 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04110_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04110 (fullRecordGapValue04110 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04110_not_prime : ¬(recordGapCenter + 92978).Prime := by
  rw [fullRecordGapTerm04110_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04110, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04110_fast_pow_mod_ne_one

def fullRecordGapValue04111 : Nat := fullRecordGapCenterValue + 93170

theorem fullRecordGapTerm04111_eq_value :
    recordGapCenter + 93170 = fullRecordGapValue04111 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04111_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04111 (fullRecordGapValue04111 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04111_not_prime : ¬(recordGapCenter + 93170).Prime := by
  rw [fullRecordGapTerm04111_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04111, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04111_fast_pow_mod_ne_one

def fullRecordGapValue04112 : Nat := fullRecordGapCenterValue + 93182

theorem fullRecordGapTerm04112_eq_value :
    recordGapCenter + 93182 = fullRecordGapValue04112 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04112_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04112 (fullRecordGapValue04112 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04112_not_prime : ¬(recordGapCenter + 93182).Prime := by
  rw [fullRecordGapTerm04112_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04112, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04112_fast_pow_mod_ne_one

def fullRecordGapValue04113 : Nat := fullRecordGapCenterValue + 93278

theorem fullRecordGapTerm04113_eq_value :
    recordGapCenter + 93278 = fullRecordGapValue04113 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04113_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04113 (fullRecordGapValue04113 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04113_not_prime : ¬(recordGapCenter + 93278).Prime := by
  rw [fullRecordGapTerm04113_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04113, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04113_fast_pow_mod_ne_one

def fullRecordGapValue04114 : Nat := fullRecordGapCenterValue + 93446

theorem fullRecordGapTerm04114_eq_value :
    recordGapCenter + 93446 = fullRecordGapValue04114 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04114_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04114 (fullRecordGapValue04114 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04114_not_prime : ¬(recordGapCenter + 93446).Prime := by
  rw [fullRecordGapTerm04114_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04114, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04114_fast_pow_mod_ne_one

def fullRecordGapValue04115 : Nat := fullRecordGapCenterValue + 93542

theorem fullRecordGapTerm04115_eq_value :
    recordGapCenter + 93542 = fullRecordGapValue04115 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04115_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04115 (fullRecordGapValue04115 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04115_not_prime : ¬(recordGapCenter + 93542).Prime := by
  rw [fullRecordGapTerm04115_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04115, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04115_fast_pow_mod_ne_one

def fullRecordGapValue04116 : Nat := fullRecordGapCenterValue + 93662

theorem fullRecordGapTerm04116_eq_value :
    recordGapCenter + 93662 = fullRecordGapValue04116 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04116_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04116 (fullRecordGapValue04116 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04116_not_prime : ¬(recordGapCenter + 93662).Prime := by
  rw [fullRecordGapTerm04116_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04116, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04116_fast_pow_mod_ne_one

def fullRecordGapValue04117 : Nat := fullRecordGapCenterValue + 93866

theorem fullRecordGapTerm04117_eq_value :
    recordGapCenter + 93866 = fullRecordGapValue04117 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04117_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04117 (fullRecordGapValue04117 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04117_not_prime : ¬(recordGapCenter + 93866).Prime := by
  rw [fullRecordGapTerm04117_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04117, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04117_fast_pow_mod_ne_one

def fullRecordGapValue04118 : Nat := fullRecordGapCenterValue + 94080

theorem fullRecordGapTerm04118_eq_value :
    recordGapCenter + 94080 = fullRecordGapValue04118 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04118_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04118 (fullRecordGapValue04118 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04118_not_prime : ¬(recordGapCenter + 94080).Prime := by
  rw [fullRecordGapTerm04118_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04118, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04118_fast_pow_mod_ne_one

def fullRecordGapValue04119 : Nat := fullRecordGapCenterValue + 94286

theorem fullRecordGapTerm04119_eq_value :
    recordGapCenter + 94286 = fullRecordGapValue04119 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04119_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04119 (fullRecordGapValue04119 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04119_not_prime : ¬(recordGapCenter + 94286).Prime := by
  rw [fullRecordGapTerm04119_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04119, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04119_fast_pow_mod_ne_one

def fullRecordGapValue04120 : Nat := fullRecordGapCenterValue + 94298

theorem fullRecordGapTerm04120_eq_value :
    recordGapCenter + 94298 = fullRecordGapValue04120 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04120_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04120 (fullRecordGapValue04120 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04120_not_prime : ¬(recordGapCenter + 94298).Prime := by
  rw [fullRecordGapTerm04120_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04120, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04120_fast_pow_mod_ne_one

def fullRecordGapValue04121 : Nat := fullRecordGapCenterValue + 94538

theorem fullRecordGapTerm04121_eq_value :
    recordGapCenter + 94538 = fullRecordGapValue04121 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04121_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04121 (fullRecordGapValue04121 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04121_not_prime : ¬(recordGapCenter + 94538).Prime := by
  rw [fullRecordGapTerm04121_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04121, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04121_fast_pow_mod_ne_one

def fullRecordGapValue04122 : Nat := fullRecordGapCenterValue + 94586

theorem fullRecordGapTerm04122_eq_value :
    recordGapCenter + 94586 = fullRecordGapValue04122 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04122_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04122 (fullRecordGapValue04122 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04122_not_prime : ¬(recordGapCenter + 94586).Prime := by
  rw [fullRecordGapTerm04122_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04122, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04122_fast_pow_mod_ne_one

def fullRecordGapValue04123 : Nat := fullRecordGapCenterValue + 95040

theorem fullRecordGapTerm04123_eq_value :
    recordGapCenter + 95040 = fullRecordGapValue04123 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04123_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04123 (fullRecordGapValue04123 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04123_not_prime : ¬(recordGapCenter + 95040).Prime := by
  rw [fullRecordGapTerm04123_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04123, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04123_fast_pow_mod_ne_one

def fullRecordGapValue04124 : Nat := fullRecordGapCenterValue + 95126

theorem fullRecordGapTerm04124_eq_value :
    recordGapCenter + 95126 = fullRecordGapValue04124 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04124_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04124 (fullRecordGapValue04124 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04124_not_prime : ¬(recordGapCenter + 95126).Prime := by
  rw [fullRecordGapTerm04124_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04124, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04124_fast_pow_mod_ne_one

def fullRecordGapValue04125 : Nat := fullRecordGapCenterValue + 95138

theorem fullRecordGapTerm04125_eq_value :
    recordGapCenter + 95138 = fullRecordGapValue04125 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04125_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04125 (fullRecordGapValue04125 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04125_not_prime : ¬(recordGapCenter + 95138).Prime := by
  rw [fullRecordGapTerm04125_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04125, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04125_fast_pow_mod_ne_one

def fullRecordGapValue04126 : Nat := fullRecordGapCenterValue + 95258

theorem fullRecordGapTerm04126_eq_value :
    recordGapCenter + 95258 = fullRecordGapValue04126 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04126_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04126 (fullRecordGapValue04126 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04126_not_prime : ¬(recordGapCenter + 95258).Prime := by
  rw [fullRecordGapTerm04126_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04126, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04126_fast_pow_mod_ne_one

def fullRecordGapValue04127 : Nat := fullRecordGapCenterValue + 95558

theorem fullRecordGapTerm04127_eq_value :
    recordGapCenter + 95558 = fullRecordGapValue04127 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04127_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04127 (fullRecordGapValue04127 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04127_not_prime : ¬(recordGapCenter + 95558).Prime := by
  rw [fullRecordGapTerm04127_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04127, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04127_fast_pow_mod_ne_one

def fullRecordGapValue04128 : Nat := fullRecordGapCenterValue + 95582

theorem fullRecordGapTerm04128_eq_value :
    recordGapCenter + 95582 = fullRecordGapValue04128 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04128_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04128 (fullRecordGapValue04128 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04128_not_prime : ¬(recordGapCenter + 95582).Prime := by
  rw [fullRecordGapTerm04128_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04128, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04128_fast_pow_mod_ne_one

def fullRecordGapValue04129 : Nat := fullRecordGapCenterValue + 96098

theorem fullRecordGapTerm04129_eq_value :
    recordGapCenter + 96098 = fullRecordGapValue04129 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04129_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04129 (fullRecordGapValue04129 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04129_not_prime : ¬(recordGapCenter + 96098).Prime := by
  rw [fullRecordGapTerm04129_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04129, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04129_fast_pow_mod_ne_one

def fullRecordGapValue04130 : Nat := fullRecordGapCenterValue + 96626

theorem fullRecordGapTerm04130_eq_value :
    recordGapCenter + 96626 = fullRecordGapValue04130 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04130_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04130 (fullRecordGapValue04130 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04130_not_prime : ¬(recordGapCenter + 96626).Prime := by
  rw [fullRecordGapTerm04130_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04130, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04130_fast_pow_mod_ne_one

def fullRecordGapValue04131 : Nat := fullRecordGapCenterValue + 96800

theorem fullRecordGapTerm04131_eq_value :
    recordGapCenter + 96800 = fullRecordGapValue04131 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04131_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04131 (fullRecordGapValue04131 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04131_not_prime : ¬(recordGapCenter + 96800).Prime := by
  rw [fullRecordGapTerm04131_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04131, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04131_fast_pow_mod_ne_one

def fullRecordGapValue04132 : Nat := fullRecordGapCenterValue + 96962

theorem fullRecordGapTerm04132_eq_value :
    recordGapCenter + 96962 = fullRecordGapValue04132 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04132_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04132 (fullRecordGapValue04132 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04132_not_prime : ¬(recordGapCenter + 96962).Prime := by
  rw [fullRecordGapTerm04132_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04132, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04132_fast_pow_mod_ne_one

def fullRecordGapValue04133 : Nat := fullRecordGapCenterValue + 97046

theorem fullRecordGapTerm04133_eq_value :
    recordGapCenter + 97046 = fullRecordGapValue04133 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04133_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04133 (fullRecordGapValue04133 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04133_not_prime : ¬(recordGapCenter + 97046).Prime := by
  rw [fullRecordGapTerm04133_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04133, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04133_fast_pow_mod_ne_one

def fullRecordGapValue04134 : Nat := fullRecordGapCenterValue + 97178

theorem fullRecordGapTerm04134_eq_value :
    recordGapCenter + 97178 = fullRecordGapValue04134 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04134_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04134 (fullRecordGapValue04134 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04134_not_prime : ¬(recordGapCenter + 97178).Prime := by
  rw [fullRecordGapTerm04134_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04134, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04134_fast_pow_mod_ne_one

def fullRecordGapValue04135 : Nat := fullRecordGapCenterValue + 97200

theorem fullRecordGapTerm04135_eq_value :
    recordGapCenter + 97200 = fullRecordGapValue04135 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04135_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04135 (fullRecordGapValue04135 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04135_not_prime : ¬(recordGapCenter + 97200).Prime := by
  rw [fullRecordGapTerm04135_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04135, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04135_fast_pow_mod_ne_one

def fullRecordGapValue04136 : Nat := fullRecordGapCenterValue + 97238

theorem fullRecordGapTerm04136_eq_value :
    recordGapCenter + 97238 = fullRecordGapValue04136 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04136_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04136 (fullRecordGapValue04136 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04136_not_prime : ¬(recordGapCenter + 97238).Prime := by
  rw [fullRecordGapTerm04136_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04136, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04136_fast_pow_mod_ne_one

def fullRecordGapValue04137 : Nat := fullRecordGapCenterValue + 97322

theorem fullRecordGapTerm04137_eq_value :
    recordGapCenter + 97322 = fullRecordGapValue04137 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04137_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04137 (fullRecordGapValue04137 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04137_not_prime : ¬(recordGapCenter + 97322).Prime := by
  rw [fullRecordGapTerm04137_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04137, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04137_fast_pow_mod_ne_one

def fullRecordGapValue04138 : Nat := fullRecordGapCenterValue + 97358

theorem fullRecordGapTerm04138_eq_value :
    recordGapCenter + 97358 = fullRecordGapValue04138 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04138_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04138 (fullRecordGapValue04138 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04138_not_prime : ¬(recordGapCenter + 97358).Prime := by
  rw [fullRecordGapTerm04138_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04138, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04138_fast_pow_mod_ne_one

def fullRecordGapValue04139 : Nat := fullRecordGapCenterValue + 97466

theorem fullRecordGapTerm04139_eq_value :
    recordGapCenter + 97466 = fullRecordGapValue04139 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04139_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04139 (fullRecordGapValue04139 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04139_not_prime : ¬(recordGapCenter + 97466).Prime := by
  rw [fullRecordGapTerm04139_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04139, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04139_fast_pow_mod_ne_one

def fullRecordGapValue04140 : Nat := fullRecordGapCenterValue + 97718

theorem fullRecordGapTerm04140_eq_value :
    recordGapCenter + 97718 = fullRecordGapValue04140 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04140_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04140 (fullRecordGapValue04140 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04140_not_prime : ¬(recordGapCenter + 97718).Prime := by
  rw [fullRecordGapTerm04140_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04140, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04140_fast_pow_mod_ne_one

def fullRecordGapValue04141 : Nat := fullRecordGapCenterValue + 97766

theorem fullRecordGapTerm04141_eq_value :
    recordGapCenter + 97766 = fullRecordGapValue04141 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04141_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04141 (fullRecordGapValue04141 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04141_not_prime : ¬(recordGapCenter + 97766).Prime := by
  rw [fullRecordGapTerm04141_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04141, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04141_fast_pow_mod_ne_one

def fullRecordGapValue04142 : Nat := fullRecordGapCenterValue + 97946

theorem fullRecordGapTerm04142_eq_value :
    recordGapCenter + 97946 = fullRecordGapValue04142 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04142_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04142 (fullRecordGapValue04142 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04142_not_prime : ¬(recordGapCenter + 97946).Prime := by
  rw [fullRecordGapTerm04142_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04142, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04142_fast_pow_mod_ne_one

def fullRecordGapValue04143 : Nat := fullRecordGapCenterValue + 98066

theorem fullRecordGapTerm04143_eq_value :
    recordGapCenter + 98066 = fullRecordGapValue04143 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04143_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04143 (fullRecordGapValue04143 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04143_not_prime : ¬(recordGapCenter + 98066).Prime := by
  rw [fullRecordGapTerm04143_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04143, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04143_fast_pow_mod_ne_one

def fullRecordGapValue04144 : Nat := fullRecordGapCenterValue + 98246

theorem fullRecordGapTerm04144_eq_value :
    recordGapCenter + 98246 = fullRecordGapValue04144 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04144_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04144 (fullRecordGapValue04144 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04144_not_prime : ¬(recordGapCenter + 98246).Prime := by
  rw [fullRecordGapTerm04144_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04144, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04144_fast_pow_mod_ne_one

def fullRecordGapValue04145 : Nat := fullRecordGapCenterValue + 98522

theorem fullRecordGapTerm04145_eq_value :
    recordGapCenter + 98522 = fullRecordGapValue04145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04145 (fullRecordGapValue04145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04145_not_prime : ¬(recordGapCenter + 98522).Prime := by
  rw [fullRecordGapTerm04145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04145_fast_pow_mod_ne_one

def fullRecordGapValue04146 : Nat := fullRecordGapCenterValue + 98558

theorem fullRecordGapTerm04146_eq_value :
    recordGapCenter + 98558 = fullRecordGapValue04146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04146 (fullRecordGapValue04146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04146_not_prime : ¬(recordGapCenter + 98558).Prime := by
  rw [fullRecordGapTerm04146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04146_fast_pow_mod_ne_one

def fullRecordGapValue04147 : Nat := fullRecordGapCenterValue + 98786

theorem fullRecordGapTerm04147_eq_value :
    recordGapCenter + 98786 = fullRecordGapValue04147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04147 (fullRecordGapValue04147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04147_not_prime : ¬(recordGapCenter + 98786).Prime := by
  rw [fullRecordGapTerm04147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04147_fast_pow_mod_ne_one

def fullRecordGapValue04148 : Nat := fullRecordGapCenterValue + 98858

theorem fullRecordGapTerm04148_eq_value :
    recordGapCenter + 98858 = fullRecordGapValue04148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04148 (fullRecordGapValue04148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04148_not_prime : ¬(recordGapCenter + 98858).Prime := by
  rw [fullRecordGapTerm04148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04148_fast_pow_mod_ne_one

def fullRecordGapValue04149 : Nat := fullRecordGapCenterValue + 98918

theorem fullRecordGapTerm04149_eq_value :
    recordGapCenter + 98918 = fullRecordGapValue04149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04149 (fullRecordGapValue04149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04149_not_prime : ¬(recordGapCenter + 98918).Prime := by
  rw [fullRecordGapTerm04149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04149_fast_pow_mod_ne_one

def fullRecordGapValue04150 : Nat := fullRecordGapCenterValue + 99206

theorem fullRecordGapTerm04150_eq_value :
    recordGapCenter + 99206 = fullRecordGapValue04150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04150 (fullRecordGapValue04150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04150_not_prime : ¬(recordGapCenter + 99206).Prime := by
  rw [fullRecordGapTerm04150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04150_fast_pow_mod_ne_one

def fullRecordGapValue04151 : Nat := fullRecordGapCenterValue + 99278

theorem fullRecordGapTerm04151_eq_value :
    recordGapCenter + 99278 = fullRecordGapValue04151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04151 (fullRecordGapValue04151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04151_not_prime : ¬(recordGapCenter + 99278).Prime := by
  rw [fullRecordGapTerm04151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04151_fast_pow_mod_ne_one

def fullRecordGapValue04152 : Nat := fullRecordGapCenterValue + 99842

theorem fullRecordGapTerm04152_eq_value :
    recordGapCenter + 99842 = fullRecordGapValue04152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04152 (fullRecordGapValue04152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04152_not_prime : ¬(recordGapCenter + 99842).Prime := by
  rw [fullRecordGapTerm04152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04152_fast_pow_mod_ne_one

def fullRecordGapValue04153 : Nat := fullRecordGapCenterValue + 100046

theorem fullRecordGapTerm04153_eq_value :
    recordGapCenter + 100046 = fullRecordGapValue04153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04153 (fullRecordGapValue04153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04153_not_prime : ¬(recordGapCenter + 100046).Prime := by
  rw [fullRecordGapTerm04153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04153_fast_pow_mod_ne_one

def fullRecordGapValue04154 : Nat := fullRecordGapCenterValue + 100238

theorem fullRecordGapTerm04154_eq_value :
    recordGapCenter + 100238 = fullRecordGapValue04154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04154 (fullRecordGapValue04154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04154_not_prime : ¬(recordGapCenter + 100238).Prime := by
  rw [fullRecordGapTerm04154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04154_fast_pow_mod_ne_one

def fullRecordGapValue04155 : Nat := fullRecordGapCenterValue + 100352

theorem fullRecordGapTerm04155_eq_value :
    recordGapCenter + 100352 = fullRecordGapValue04155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04155 (fullRecordGapValue04155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04155_not_prime : ¬(recordGapCenter + 100352).Prime := by
  rw [fullRecordGapTerm04155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04155_fast_pow_mod_ne_one

def fullRecordGapValue04156 : Nat := fullRecordGapCenterValue + 100658

theorem fullRecordGapTerm04156_eq_value :
    recordGapCenter + 100658 = fullRecordGapValue04156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04156 (fullRecordGapValue04156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04156_not_prime : ¬(recordGapCenter + 100658).Prime := by
  rw [fullRecordGapTerm04156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04156_fast_pow_mod_ne_one

def fullRecordGapValue04157 : Nat := fullRecordGapCenterValue + 101162

theorem fullRecordGapTerm04157_eq_value :
    recordGapCenter + 101162 = fullRecordGapValue04157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04157 (fullRecordGapValue04157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04157_not_prime : ¬(recordGapCenter + 101162).Prime := by
  rw [fullRecordGapTerm04157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04157_fast_pow_mod_ne_one

def fullRecordGapValue04158 : Nat := fullRecordGapCenterValue + 101186

theorem fullRecordGapTerm04158_eq_value :
    recordGapCenter + 101186 = fullRecordGapValue04158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04158 (fullRecordGapValue04158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04158_not_prime : ¬(recordGapCenter + 101186).Prime := by
  rw [fullRecordGapTerm04158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04158_fast_pow_mod_ne_one

def fullRecordGapValue04159 : Nat := fullRecordGapCenterValue + 101342

theorem fullRecordGapTerm04159_eq_value :
    recordGapCenter + 101342 = fullRecordGapValue04159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04159 (fullRecordGapValue04159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04159_not_prime : ¬(recordGapCenter + 101342).Prime := by
  rw [fullRecordGapTerm04159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04159_fast_pow_mod_ne_one

def fullRecordGapValue04160 : Nat := fullRecordGapCenterValue + 101546

theorem fullRecordGapTerm04160_eq_value :
    recordGapCenter + 101546 = fullRecordGapValue04160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04160 (fullRecordGapValue04160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04160_not_prime : ¬(recordGapCenter + 101546).Prime := by
  rw [fullRecordGapTerm04160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04160_fast_pow_mod_ne_one

def fullRecordGapValue04161 : Nat := fullRecordGapCenterValue + 101846

theorem fullRecordGapTerm04161_eq_value :
    recordGapCenter + 101846 = fullRecordGapValue04161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04161 (fullRecordGapValue04161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04161_not_prime : ¬(recordGapCenter + 101846).Prime := by
  rw [fullRecordGapTerm04161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04161_fast_pow_mod_ne_one

def fullRecordGapValue04162 : Nat := fullRecordGapCenterValue + 102482

theorem fullRecordGapTerm04162_eq_value :
    recordGapCenter + 102482 = fullRecordGapValue04162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04162 (fullRecordGapValue04162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04162_not_prime : ¬(recordGapCenter + 102482).Prime := by
  rw [fullRecordGapTerm04162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04162_fast_pow_mod_ne_one

def fullRecordGapValue04163 : Nat := fullRecordGapCenterValue + 102686

theorem fullRecordGapTerm04163_eq_value :
    recordGapCenter + 102686 = fullRecordGapValue04163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04163 (fullRecordGapValue04163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04163_not_prime : ¬(recordGapCenter + 102686).Prime := by
  rw [fullRecordGapTerm04163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04163_fast_pow_mod_ne_one

def fullRecordGapValue04164 : Nat := fullRecordGapCenterValue + 102842

theorem fullRecordGapTerm04164_eq_value :
    recordGapCenter + 102842 = fullRecordGapValue04164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04164 (fullRecordGapValue04164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04164_not_prime : ¬(recordGapCenter + 102842).Prime := by
  rw [fullRecordGapTerm04164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04164_fast_pow_mod_ne_one

def fullRecordGapValue04165 : Nat := fullRecordGapCenterValue + 102900

theorem fullRecordGapTerm04165_eq_value :
    recordGapCenter + 102900 = fullRecordGapValue04165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04165 (fullRecordGapValue04165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04165_not_prime : ¬(recordGapCenter + 102900).Prime := by
  rw [fullRecordGapTerm04165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04165_fast_pow_mod_ne_one

def fullRecordGapValue04166 : Nat := fullRecordGapCenterValue + 103226

theorem fullRecordGapTerm04166_eq_value :
    recordGapCenter + 103226 = fullRecordGapValue04166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04166 (fullRecordGapValue04166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04166_not_prime : ¬(recordGapCenter + 103226).Prime := by
  rw [fullRecordGapTerm04166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04166_fast_pow_mod_ne_one

def fullRecordGapValue04167 : Nat := fullRecordGapCenterValue + 103346

theorem fullRecordGapTerm04167_eq_value :
    recordGapCenter + 103346 = fullRecordGapValue04167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04167 (fullRecordGapValue04167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04167_not_prime : ¬(recordGapCenter + 103346).Prime := by
  rw [fullRecordGapTerm04167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04167_fast_pow_mod_ne_one

def fullRecordGapValue04168 : Nat := fullRecordGapCenterValue + 103538

theorem fullRecordGapTerm04168_eq_value :
    recordGapCenter + 103538 = fullRecordGapValue04168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04168 (fullRecordGapValue04168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04168_not_prime : ¬(recordGapCenter + 103538).Prime := by
  rw [fullRecordGapTerm04168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04168_fast_pow_mod_ne_one

def fullRecordGapValue04169 : Nat := fullRecordGapCenterValue + 103826

theorem fullRecordGapTerm04169_eq_value :
    recordGapCenter + 103826 = fullRecordGapValue04169 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04169_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04169 (fullRecordGapValue04169 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04169_not_prime : ¬(recordGapCenter + 103826).Prime := by
  rw [fullRecordGapTerm04169_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04169, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04169_fast_pow_mod_ne_one

def fullRecordGapValue04170 : Nat := fullRecordGapCenterValue + 103950

theorem fullRecordGapTerm04170_eq_value :
    recordGapCenter + 103950 = fullRecordGapValue04170 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04170_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04170 (fullRecordGapValue04170 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04170_not_prime : ¬(recordGapCenter + 103950).Prime := by
  rw [fullRecordGapTerm04170_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04170, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04170_fast_pow_mod_ne_one

def fullRecordGapValue04171 : Nat := fullRecordGapCenterValue + 103982

theorem fullRecordGapTerm04171_eq_value :
    recordGapCenter + 103982 = fullRecordGapValue04171 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04171_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04171 (fullRecordGapValue04171 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04171_not_prime : ¬(recordGapCenter + 103982).Prime := by
  rw [fullRecordGapTerm04171_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04171, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04171_fast_pow_mod_ne_one

def fullRecordGapValue04172 : Nat := fullRecordGapCenterValue + 104018

theorem fullRecordGapTerm04172_eq_value :
    recordGapCenter + 104018 = fullRecordGapValue04172 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04172_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04172 (fullRecordGapValue04172 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04172_not_prime : ¬(recordGapCenter + 104018).Prime := by
  rw [fullRecordGapTerm04172_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04172, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04172_fast_pow_mod_ne_one

def fullRecordGapValue04173 : Nat := fullRecordGapCenterValue + 104042

theorem fullRecordGapTerm04173_eq_value :
    recordGapCenter + 104042 = fullRecordGapValue04173 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04173_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04173 (fullRecordGapValue04173 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04173_not_prime : ¬(recordGapCenter + 104042).Prime := by
  rw [fullRecordGapTerm04173_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04173, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04173_fast_pow_mod_ne_one

def fullRecordGapValue04174 : Nat := fullRecordGapCenterValue + 104102

theorem fullRecordGapTerm04174_eq_value :
    recordGapCenter + 104102 = fullRecordGapValue04174 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04174_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04174 (fullRecordGapValue04174 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04174_not_prime : ¬(recordGapCenter + 104102).Prime := by
  rw [fullRecordGapTerm04174_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04174, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04174_fast_pow_mod_ne_one

def fullRecordGapValue04175 : Nat := fullRecordGapCenterValue + 104402

theorem fullRecordGapTerm04175_eq_value :
    recordGapCenter + 104402 = fullRecordGapValue04175 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04175_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04175 (fullRecordGapValue04175 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04175_not_prime : ¬(recordGapCenter + 104402).Prime := by
  rw [fullRecordGapTerm04175_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04175, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04175_fast_pow_mod_ne_one

def fullRecordGapValue04176 : Nat := fullRecordGapCenterValue + 104498

theorem fullRecordGapTerm04176_eq_value :
    recordGapCenter + 104498 = fullRecordGapValue04176 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04176_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04176 (fullRecordGapValue04176 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04176_not_prime : ¬(recordGapCenter + 104498).Prime := by
  rw [fullRecordGapTerm04176_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04176, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04176_fast_pow_mod_ne_one

def fullRecordGapValue04177 : Nat := fullRecordGapCenterValue + 104906

theorem fullRecordGapTerm04177_eq_value :
    recordGapCenter + 104906 = fullRecordGapValue04177 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04177_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04177 (fullRecordGapValue04177 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04177_not_prime : ¬(recordGapCenter + 104906).Prime := by
  rw [fullRecordGapTerm04177_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04177, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04177_fast_pow_mod_ne_one

def fullRecordGapValue04178 : Nat := fullRecordGapCenterValue + 105000

theorem fullRecordGapTerm04178_eq_value :
    recordGapCenter + 105000 = fullRecordGapValue04178 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04178_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04178 (fullRecordGapValue04178 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04178_not_prime : ¬(recordGapCenter + 105000).Prime := by
  rw [fullRecordGapTerm04178_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04178, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04178_fast_pow_mod_ne_one

def fullRecordGapValue04179 : Nat := fullRecordGapCenterValue + 105086

theorem fullRecordGapTerm04179_eq_value :
    recordGapCenter + 105086 = fullRecordGapValue04179 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04179_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04179 (fullRecordGapValue04179 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04179_not_prime : ¬(recordGapCenter + 105086).Prime := by
  rw [fullRecordGapTerm04179_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04179, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04179_fast_pow_mod_ne_one

def fullRecordGapValue04180 : Nat := fullRecordGapCenterValue + 105158

theorem fullRecordGapTerm04180_eq_value :
    recordGapCenter + 105158 = fullRecordGapValue04180 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04180_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04180 (fullRecordGapValue04180 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04180_not_prime : ¬(recordGapCenter + 105158).Prime := by
  rw [fullRecordGapTerm04180_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04180, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04180_fast_pow_mod_ne_one

def fullRecordGapValue04181 : Nat := fullRecordGapCenterValue + 105218

theorem fullRecordGapTerm04181_eq_value :
    recordGapCenter + 105218 = fullRecordGapValue04181 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04181_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04181 (fullRecordGapValue04181 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04181_not_prime : ¬(recordGapCenter + 105218).Prime := by
  rw [fullRecordGapTerm04181_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04181, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04181_fast_pow_mod_ne_one

def fullRecordGapValue04182 : Nat := fullRecordGapCenterValue + 105600

theorem fullRecordGapTerm04182_eq_value :
    recordGapCenter + 105600 = fullRecordGapValue04182 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04182_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04182 (fullRecordGapValue04182 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04182_not_prime : ¬(recordGapCenter + 105600).Prime := by
  rw [fullRecordGapTerm04182_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04182, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04182_fast_pow_mod_ne_one

def fullRecordGapValue04183 : Nat := fullRecordGapCenterValue + 105626

theorem fullRecordGapTerm04183_eq_value :
    recordGapCenter + 105626 = fullRecordGapValue04183 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04183_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04183 (fullRecordGapValue04183 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04183_not_prime : ¬(recordGapCenter + 105626).Prime := by
  rw [fullRecordGapTerm04183_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04183, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04183_fast_pow_mod_ne_one

def fullRecordGapValue04184 : Nat := fullRecordGapCenterValue + 105722

theorem fullRecordGapTerm04184_eq_value :
    recordGapCenter + 105722 = fullRecordGapValue04184 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04184_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04184 (fullRecordGapValue04184 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04184_not_prime : ¬(recordGapCenter + 105722).Prime := by
  rw [fullRecordGapTerm04184_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04184, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04184_fast_pow_mod_ne_one

def fullRecordGapValue04185 : Nat := fullRecordGapCenterValue + 105758

theorem fullRecordGapTerm04185_eq_value :
    recordGapCenter + 105758 = fullRecordGapValue04185 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04185_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04185 (fullRecordGapValue04185 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04185_not_prime : ¬(recordGapCenter + 105758).Prime := by
  rw [fullRecordGapTerm04185_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04185, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04185_fast_pow_mod_ne_one

def fullRecordGapValue04186 : Nat := fullRecordGapCenterValue + 105840

theorem fullRecordGapTerm04186_eq_value :
    recordGapCenter + 105840 = fullRecordGapValue04186 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04186_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04186 (fullRecordGapValue04186 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04186_not_prime : ¬(recordGapCenter + 105840).Prime := by
  rw [fullRecordGapTerm04186_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04186, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04186_fast_pow_mod_ne_one

def fullRecordGapValue04187 : Nat := fullRecordGapCenterValue + 106178

theorem fullRecordGapTerm04187_eq_value :
    recordGapCenter + 106178 = fullRecordGapValue04187 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04187_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04187 (fullRecordGapValue04187 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04187_not_prime : ¬(recordGapCenter + 106178).Prime := by
  rw [fullRecordGapTerm04187_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04187, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04187_fast_pow_mod_ne_one

def fullRecordGapValue04188 : Nat := fullRecordGapCenterValue + 106562

theorem fullRecordGapTerm04188_eq_value :
    recordGapCenter + 106562 = fullRecordGapValue04188 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04188_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04188 (fullRecordGapValue04188 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04188_not_prime : ¬(recordGapCenter + 106562).Prime := by
  rw [fullRecordGapTerm04188_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04188, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04188_fast_pow_mod_ne_one

def fullRecordGapValue04189 : Nat := fullRecordGapCenterValue + 106598

theorem fullRecordGapTerm04189_eq_value :
    recordGapCenter + 106598 = fullRecordGapValue04189 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04189_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04189 (fullRecordGapValue04189 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04189_not_prime : ¬(recordGapCenter + 106598).Prime := by
  rw [fullRecordGapTerm04189_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04189, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04189_fast_pow_mod_ne_one

def fullRecordGapValue04190 : Nat := fullRecordGapCenterValue + 106802

theorem fullRecordGapTerm04190_eq_value :
    recordGapCenter + 106802 = fullRecordGapValue04190 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04190_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04190 (fullRecordGapValue04190 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04190_not_prime : ¬(recordGapCenter + 106802).Prime := by
  rw [fullRecordGapTerm04190_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04190, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04190_fast_pow_mod_ne_one

def fullRecordGapValue04191 : Nat := fullRecordGapCenterValue + 106838

theorem fullRecordGapTerm04191_eq_value :
    recordGapCenter + 106838 = fullRecordGapValue04191 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04191_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04191 (fullRecordGapValue04191 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04191_not_prime : ¬(recordGapCenter + 106838).Prime := by
  rw [fullRecordGapTerm04191_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04191, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04191_fast_pow_mod_ne_one

def fullRecordGapValue04192 : Nat := fullRecordGapCenterValue + 106920

theorem fullRecordGapTerm04192_eq_value :
    recordGapCenter + 106920 = fullRecordGapValue04192 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04192_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04192 (fullRecordGapValue04192 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04192_not_prime : ¬(recordGapCenter + 106920).Prime := by
  rw [fullRecordGapTerm04192_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04192, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04192_fast_pow_mod_ne_one

def fullRecordGapValue04193 : Nat := fullRecordGapCenterValue + 107006

theorem fullRecordGapTerm04193_eq_value :
    recordGapCenter + 107006 = fullRecordGapValue04193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04193 (fullRecordGapValue04193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04193_not_prime : ¬(recordGapCenter + 107006).Prime := by
  rw [fullRecordGapTerm04193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04193_fast_pow_mod_ne_one

def fullRecordGapValue04194 : Nat := fullRecordGapCenterValue + 107102

theorem fullRecordGapTerm04194_eq_value :
    recordGapCenter + 107102 = fullRecordGapValue04194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04194 (fullRecordGapValue04194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04194_not_prime : ¬(recordGapCenter + 107102).Prime := by
  rw [fullRecordGapTerm04194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04194_fast_pow_mod_ne_one

def fullRecordGapValue04195 : Nat := fullRecordGapCenterValue + 107138

theorem fullRecordGapTerm04195_eq_value :
    recordGapCenter + 107138 = fullRecordGapValue04195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04195 (fullRecordGapValue04195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04195_not_prime : ¬(recordGapCenter + 107138).Prime := by
  rw [fullRecordGapTerm04195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04195_fast_pow_mod_ne_one

def fullRecordGapValue04196 : Nat := fullRecordGapCenterValue + 107258

theorem fullRecordGapTerm04196_eq_value :
    recordGapCenter + 107258 = fullRecordGapValue04196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04196 (fullRecordGapValue04196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04196_not_prime : ¬(recordGapCenter + 107258).Prime := by
  rw [fullRecordGapTerm04196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04196_fast_pow_mod_ne_one

def fullRecordGapValue04197 : Nat := fullRecordGapCenterValue + 107520

theorem fullRecordGapTerm04197_eq_value :
    recordGapCenter + 107520 = fullRecordGapValue04197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04197 (fullRecordGapValue04197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04197_not_prime : ¬(recordGapCenter + 107520).Prime := by
  rw [fullRecordGapTerm04197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04197_fast_pow_mod_ne_one

def fullRecordGapValue04198 : Nat := fullRecordGapCenterValue + 107798

theorem fullRecordGapTerm04198_eq_value :
    recordGapCenter + 107798 = fullRecordGapValue04198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04198 (fullRecordGapValue04198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04198_not_prime : ¬(recordGapCenter + 107798).Prime := by
  rw [fullRecordGapTerm04198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04198_fast_pow_mod_ne_one

def fullRecordGapValue04199 : Nat := fullRecordGapCenterValue + 107846

theorem fullRecordGapTerm04199_eq_value :
    recordGapCenter + 107846 = fullRecordGapValue04199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04199 (fullRecordGapValue04199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04199_not_prime : ¬(recordGapCenter + 107846).Prime := by
  rw [fullRecordGapTerm04199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04199_fast_pow_mod_ne_one

def fullRecordGapValue04200 : Nat := fullRecordGapCenterValue + 108000

theorem fullRecordGapTerm04200_eq_value :
    recordGapCenter + 108000 = fullRecordGapValue04200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04200 (fullRecordGapValue04200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04200_not_prime : ¬(recordGapCenter + 108000).Prime := by
  rw [fullRecordGapTerm04200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04200_fast_pow_mod_ne_one

def fullRecordGapValue04201 : Nat := fullRecordGapCenterValue + 108182

theorem fullRecordGapTerm04201_eq_value :
    recordGapCenter + 108182 = fullRecordGapValue04201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04201 (fullRecordGapValue04201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04201_not_prime : ¬(recordGapCenter + 108182).Prime := by
  rw [fullRecordGapTerm04201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04201_fast_pow_mod_ne_one

def fullRecordGapValue04202 : Nat := fullRecordGapCenterValue + 108242

theorem fullRecordGapTerm04202_eq_value :
    recordGapCenter + 108242 = fullRecordGapValue04202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04202 (fullRecordGapValue04202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04202_not_prime : ¬(recordGapCenter + 108242).Prime := by
  rw [fullRecordGapTerm04202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04202_fast_pow_mod_ne_one

def fullRecordGapValue04203 : Nat := fullRecordGapCenterValue + 108266

theorem fullRecordGapTerm04203_eq_value :
    recordGapCenter + 108266 = fullRecordGapValue04203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04203 (fullRecordGapValue04203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04203_not_prime : ¬(recordGapCenter + 108266).Prime := by
  rw [fullRecordGapTerm04203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04203_fast_pow_mod_ne_one

def fullRecordGapValue04204 : Nat := fullRecordGapCenterValue + 108278

theorem fullRecordGapTerm04204_eq_value :
    recordGapCenter + 108278 = fullRecordGapValue04204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04204 (fullRecordGapValue04204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04204_not_prime : ¬(recordGapCenter + 108278).Prime := by
  rw [fullRecordGapTerm04204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04204_fast_pow_mod_ne_one

def fullRecordGapValue04205 : Nat := fullRecordGapCenterValue + 108326

theorem fullRecordGapTerm04205_eq_value :
    recordGapCenter + 108326 = fullRecordGapValue04205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04205 (fullRecordGapValue04205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04205_not_prime : ¬(recordGapCenter + 108326).Prime := by
  rw [fullRecordGapTerm04205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04205_fast_pow_mod_ne_one

def fullRecordGapValue04206 : Nat := fullRecordGapCenterValue + 108362

theorem fullRecordGapTerm04206_eq_value :
    recordGapCenter + 108362 = fullRecordGapValue04206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04206 (fullRecordGapValue04206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04206_not_prime : ¬(recordGapCenter + 108362).Prime := by
  rw [fullRecordGapTerm04206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04206_fast_pow_mod_ne_one

def fullRecordGapValue04207 : Nat := fullRecordGapCenterValue + 108638

theorem fullRecordGapTerm04207_eq_value :
    recordGapCenter + 108638 = fullRecordGapValue04207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04207 (fullRecordGapValue04207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04207_not_prime : ¬(recordGapCenter + 108638).Prime := by
  rw [fullRecordGapTerm04207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04207_fast_pow_mod_ne_one

def fullRecordGapValue04208 : Nat := fullRecordGapCenterValue + 108662

theorem fullRecordGapTerm04208_eq_value :
    recordGapCenter + 108662 = fullRecordGapValue04208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04208 (fullRecordGapValue04208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04208_not_prime : ¬(recordGapCenter + 108662).Prime := by
  rw [fullRecordGapTerm04208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04208_fast_pow_mod_ne_one

def fullRecordGapValue04209 : Nat := fullRecordGapCenterValue + 108722

theorem fullRecordGapTerm04209_eq_value :
    recordGapCenter + 108722 = fullRecordGapValue04209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04209 (fullRecordGapValue04209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04209_not_prime : ¬(recordGapCenter + 108722).Prime := by
  rw [fullRecordGapTerm04209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04209_fast_pow_mod_ne_one

def fullRecordGapValue04210 : Nat := fullRecordGapCenterValue + 108938

theorem fullRecordGapTerm04210_eq_value :
    recordGapCenter + 108938 = fullRecordGapValue04210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04210 (fullRecordGapValue04210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04210_not_prime : ¬(recordGapCenter + 108938).Prime := by
  rw [fullRecordGapTerm04210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04210_fast_pow_mod_ne_one

def fullRecordGapValue04211 : Nat := fullRecordGapCenterValue + 108986

theorem fullRecordGapTerm04211_eq_value :
    recordGapCenter + 108986 = fullRecordGapValue04211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04211 (fullRecordGapValue04211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04211_not_prime : ¬(recordGapCenter + 108986).Prime := by
  rw [fullRecordGapTerm04211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04211_fast_pow_mod_ne_one

def fullRecordGapValue04212 : Nat := fullRecordGapCenterValue + 109082

theorem fullRecordGapTerm04212_eq_value :
    recordGapCenter + 109082 = fullRecordGapValue04212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04212 (fullRecordGapValue04212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04212_not_prime : ¬(recordGapCenter + 109082).Prime := by
  rw [fullRecordGapTerm04212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04212_fast_pow_mod_ne_one

def fullRecordGapValue04213 : Nat := fullRecordGapCenterValue + 109118

theorem fullRecordGapTerm04213_eq_value :
    recordGapCenter + 109118 = fullRecordGapValue04213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04213 (fullRecordGapValue04213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04213_not_prime : ¬(recordGapCenter + 109118).Prime := by
  rw [fullRecordGapTerm04213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04213_fast_pow_mod_ne_one

def fullRecordGapValue04214 : Nat := fullRecordGapCenterValue + 109166

theorem fullRecordGapTerm04214_eq_value :
    recordGapCenter + 109166 = fullRecordGapValue04214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04214 (fullRecordGapValue04214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04214_not_prime : ¬(recordGapCenter + 109166).Prime := by
  rw [fullRecordGapTerm04214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04214_fast_pow_mod_ne_one

def fullRecordGapValue04215 : Nat := fullRecordGapCenterValue + 109202

theorem fullRecordGapTerm04215_eq_value :
    recordGapCenter + 109202 = fullRecordGapValue04215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04215 (fullRecordGapValue04215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04215_not_prime : ¬(recordGapCenter + 109202).Prime := by
  rw [fullRecordGapTerm04215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04215_fast_pow_mod_ne_one

def fullRecordGapValue04216 : Nat := fullRecordGapCenterValue + 109350

theorem fullRecordGapTerm04216_eq_value :
    recordGapCenter + 109350 = fullRecordGapValue04216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04216 (fullRecordGapValue04216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04216_not_prime : ¬(recordGapCenter + 109350).Prime := by
  rw [fullRecordGapTerm04216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04216_fast_pow_mod_ne_one

def fullRecordGapValue04217 : Nat := fullRecordGapCenterValue + 109658

theorem fullRecordGapTerm04217_eq_value :
    recordGapCenter + 109658 = fullRecordGapValue04217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04217 (fullRecordGapValue04217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04217_not_prime : ¬(recordGapCenter + 109658).Prime := by
  rw [fullRecordGapTerm04217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04217_fast_pow_mod_ne_one

def fullRecordGapValue04218 : Nat := fullRecordGapCenterValue + 109898

theorem fullRecordGapTerm04218_eq_value :
    recordGapCenter + 109898 = fullRecordGapValue04218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04218 (fullRecordGapValue04218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04218_not_prime : ¬(recordGapCenter + 109898).Prime := by
  rw [fullRecordGapTerm04218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04218_fast_pow_mod_ne_one

def fullRecordGapValue04219 : Nat := fullRecordGapCenterValue + 109946

theorem fullRecordGapTerm04219_eq_value :
    recordGapCenter + 109946 = fullRecordGapValue04219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04219 (fullRecordGapValue04219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04219_not_prime : ¬(recordGapCenter + 109946).Prime := by
  rw [fullRecordGapTerm04219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04219_fast_pow_mod_ne_one

def fullRecordGapValue04220 : Nat := fullRecordGapCenterValue + 110426

theorem fullRecordGapTerm04220_eq_value :
    recordGapCenter + 110426 = fullRecordGapValue04220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04220 (fullRecordGapValue04220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04220_not_prime : ¬(recordGapCenter + 110426).Prime := by
  rw [fullRecordGapTerm04220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04220_fast_pow_mod_ne_one

def fullRecordGapValue04221 : Nat := fullRecordGapCenterValue + 110486

theorem fullRecordGapTerm04221_eq_value :
    recordGapCenter + 110486 = fullRecordGapValue04221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04221 (fullRecordGapValue04221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04221_not_prime : ¬(recordGapCenter + 110486).Prime := by
  rw [fullRecordGapTerm04221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04221_fast_pow_mod_ne_one

def fullRecordGapValue04222 : Nat := fullRecordGapCenterValue + 110498

theorem fullRecordGapTerm04222_eq_value :
    recordGapCenter + 110498 = fullRecordGapValue04222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04222 (fullRecordGapValue04222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04222_not_prime : ¬(recordGapCenter + 110498).Prime := by
  rw [fullRecordGapTerm04222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04222_fast_pow_mod_ne_one

def fullRecordGapValue04223 : Nat := fullRecordGapCenterValue + 110666

theorem fullRecordGapTerm04223_eq_value :
    recordGapCenter + 110666 = fullRecordGapValue04223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04223 (fullRecordGapValue04223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04223_not_prime : ¬(recordGapCenter + 110666).Prime := by
  rw [fullRecordGapTerm04223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04223_fast_pow_mod_ne_one

def fullRecordGapValue04224 : Nat := fullRecordGapCenterValue + 110798

theorem fullRecordGapTerm04224_eq_value :
    recordGapCenter + 110798 = fullRecordGapValue04224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04224 (fullRecordGapValue04224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04224_not_prime : ¬(recordGapCenter + 110798).Prime := by
  rw [fullRecordGapTerm04224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04224_fast_pow_mod_ne_one

def fullRecordGapValue04225 : Nat := fullRecordGapCenterValue + 111266

theorem fullRecordGapTerm04225_eq_value :
    recordGapCenter + 111266 = fullRecordGapValue04225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04225 (fullRecordGapValue04225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04225_not_prime : ¬(recordGapCenter + 111266).Prime := by
  rw [fullRecordGapTerm04225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04225_fast_pow_mod_ne_one

def fullRecordGapValue04226 : Nat := fullRecordGapCenterValue + 111326

theorem fullRecordGapTerm04226_eq_value :
    recordGapCenter + 111326 = fullRecordGapValue04226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04226 (fullRecordGapValue04226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04226_not_prime : ¬(recordGapCenter + 111326).Prime := by
  rw [fullRecordGapTerm04226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04226_fast_pow_mod_ne_one

def fullRecordGapValue04227 : Nat := fullRecordGapCenterValue + 111638

theorem fullRecordGapTerm04227_eq_value :
    recordGapCenter + 111638 = fullRecordGapValue04227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04227 (fullRecordGapValue04227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04227_not_prime : ¬(recordGapCenter + 111638).Prime := by
  rw [fullRecordGapTerm04227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04227_fast_pow_mod_ne_one

def fullRecordGapValue04228 : Nat := fullRecordGapCenterValue + 111686

theorem fullRecordGapTerm04228_eq_value :
    recordGapCenter + 111686 = fullRecordGapValue04228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04228 (fullRecordGapValue04228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04228_not_prime : ¬(recordGapCenter + 111686).Prime := by
  rw [fullRecordGapTerm04228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04228_fast_pow_mod_ne_one

def fullRecordGapValue04229 : Nat := fullRecordGapCenterValue + 112640

theorem fullRecordGapTerm04229_eq_value :
    recordGapCenter + 112640 = fullRecordGapValue04229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04229 (fullRecordGapValue04229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04229_not_prime : ¬(recordGapCenter + 112640).Prime := by
  rw [fullRecordGapTerm04229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04229_fast_pow_mod_ne_one

def fullRecordGapValue04230 : Nat := fullRecordGapCenterValue + 112946

theorem fullRecordGapTerm04230_eq_value :
    recordGapCenter + 112946 = fullRecordGapValue04230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04230 (fullRecordGapValue04230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04230_not_prime : ¬(recordGapCenter + 112946).Prime := by
  rw [fullRecordGapTerm04230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04230_fast_pow_mod_ne_one

def fullRecordGapValue04231 : Nat := fullRecordGapCenterValue + 113006

theorem fullRecordGapTerm04231_eq_value :
    recordGapCenter + 113006 = fullRecordGapValue04231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04231 (fullRecordGapValue04231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04231_not_prime : ¬(recordGapCenter + 113006).Prime := by
  rw [fullRecordGapTerm04231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04231_fast_pow_mod_ne_one

def fullRecordGapValue04232 : Nat := fullRecordGapCenterValue + 113018

theorem fullRecordGapTerm04232_eq_value :
    recordGapCenter + 113018 = fullRecordGapValue04232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04232 (fullRecordGapValue04232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04232_not_prime : ¬(recordGapCenter + 113018).Prime := by
  rw [fullRecordGapTerm04232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04232_fast_pow_mod_ne_one

def fullRecordGapValue04233 : Nat := fullRecordGapCenterValue + 113222

theorem fullRecordGapTerm04233_eq_value :
    recordGapCenter + 113222 = fullRecordGapValue04233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04233 (fullRecordGapValue04233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04233_not_prime : ¬(recordGapCenter + 113222).Prime := by
  rw [fullRecordGapTerm04233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04233_fast_pow_mod_ne_one

def fullRecordGapValue04234 : Nat := fullRecordGapCenterValue + 113402

theorem fullRecordGapTerm04234_eq_value :
    recordGapCenter + 113402 = fullRecordGapValue04234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04234 (fullRecordGapValue04234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04234_not_prime : ¬(recordGapCenter + 113402).Prime := by
  rw [fullRecordGapTerm04234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04234_fast_pow_mod_ne_one

def fullRecordGapValue04235 : Nat := fullRecordGapCenterValue + 113642

theorem fullRecordGapTerm04235_eq_value :
    recordGapCenter + 113642 = fullRecordGapValue04235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04235 (fullRecordGapValue04235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04235_not_prime : ¬(recordGapCenter + 113642).Prime := by
  rw [fullRecordGapTerm04235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04235_fast_pow_mod_ne_one

def fullRecordGapValue04236 : Nat := fullRecordGapCenterValue + 113858

theorem fullRecordGapTerm04236_eq_value :
    recordGapCenter + 113858 = fullRecordGapValue04236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04236 (fullRecordGapValue04236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04236_not_prime : ¬(recordGapCenter + 113858).Prime := by
  rw [fullRecordGapTerm04236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04236_fast_pow_mod_ne_one

def fullRecordGapValue04237 : Nat := fullRecordGapCenterValue + 114326

theorem fullRecordGapTerm04237_eq_value :
    recordGapCenter + 114326 = fullRecordGapValue04237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04237 (fullRecordGapValue04237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04237_not_prime : ¬(recordGapCenter + 114326).Prime := by
  rw [fullRecordGapTerm04237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04237_fast_pow_mod_ne_one

def fullRecordGapValue04238 : Nat := fullRecordGapCenterValue + 114446

theorem fullRecordGapTerm04238_eq_value :
    recordGapCenter + 114446 = fullRecordGapValue04238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04238 (fullRecordGapValue04238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04238_not_prime : ¬(recordGapCenter + 114446).Prime := by
  rw [fullRecordGapTerm04238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04238_fast_pow_mod_ne_one

def fullRecordGapValue04239 : Nat := fullRecordGapCenterValue + 114566

theorem fullRecordGapTerm04239_eq_value :
    recordGapCenter + 114566 = fullRecordGapValue04239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04239 (fullRecordGapValue04239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04239_not_prime : ¬(recordGapCenter + 114566).Prime := by
  rw [fullRecordGapTerm04239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04239_fast_pow_mod_ne_one

def fullRecordGapValue04240 : Nat := fullRecordGapCenterValue + 114698

theorem fullRecordGapTerm04240_eq_value :
    recordGapCenter + 114698 = fullRecordGapValue04240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04240 (fullRecordGapValue04240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04240_not_prime : ¬(recordGapCenter + 114698).Prime := by
  rw [fullRecordGapTerm04240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04240_fast_pow_mod_ne_one

def fullRecordGapValue04241 : Nat := fullRecordGapCenterValue + 115118

theorem fullRecordGapTerm04241_eq_value :
    recordGapCenter + 115118 = fullRecordGapValue04241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04241 (fullRecordGapValue04241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04241_not_prime : ¬(recordGapCenter + 115118).Prime := by
  rw [fullRecordGapTerm04241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04241_fast_pow_mod_ne_one

def fullRecordGapValue04242 : Nat := fullRecordGapCenterValue + 115200

theorem fullRecordGapTerm04242_eq_value :
    recordGapCenter + 115200 = fullRecordGapValue04242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04242 (fullRecordGapValue04242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04242_not_prime : ¬(recordGapCenter + 115200).Prime := by
  rw [fullRecordGapTerm04242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04242_fast_pow_mod_ne_one

def fullRecordGapValue04243 : Nat := fullRecordGapCenterValue + 115418

theorem fullRecordGapTerm04243_eq_value :
    recordGapCenter + 115418 = fullRecordGapValue04243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04243 (fullRecordGapValue04243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04243_not_prime : ¬(recordGapCenter + 115418).Prime := by
  rw [fullRecordGapTerm04243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04243_fast_pow_mod_ne_one

def fullRecordGapValue04244 : Nat := fullRecordGapCenterValue + 115586

theorem fullRecordGapTerm04244_eq_value :
    recordGapCenter + 115586 = fullRecordGapValue04244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04244 (fullRecordGapValue04244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04244_not_prime : ¬(recordGapCenter + 115586).Prime := by
  rw [fullRecordGapTerm04244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04244_fast_pow_mod_ne_one

def fullRecordGapValue04245 : Nat := fullRecordGapCenterValue + 115658

theorem fullRecordGapTerm04245_eq_value :
    recordGapCenter + 115658 = fullRecordGapValue04245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04245 (fullRecordGapValue04245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04245_not_prime : ¬(recordGapCenter + 115658).Prime := by
  rw [fullRecordGapTerm04245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04245_fast_pow_mod_ne_one

def fullRecordGapValue04246 : Nat := fullRecordGapCenterValue + 115802

theorem fullRecordGapTerm04246_eq_value :
    recordGapCenter + 115802 = fullRecordGapValue04246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04246 (fullRecordGapValue04246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04246_not_prime : ¬(recordGapCenter + 115802).Prime := by
  rw [fullRecordGapTerm04246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04246_fast_pow_mod_ne_one

def fullRecordGapValue04247 : Nat := fullRecordGapCenterValue + 115886

theorem fullRecordGapTerm04247_eq_value :
    recordGapCenter + 115886 = fullRecordGapValue04247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04247 (fullRecordGapValue04247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04247_not_prime : ¬(recordGapCenter + 115886).Prime := by
  rw [fullRecordGapTerm04247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04247_fast_pow_mod_ne_one

def fullRecordGapValue04248 : Nat := fullRecordGapCenterValue + 116342

theorem fullRecordGapTerm04248_eq_value :
    recordGapCenter + 116342 = fullRecordGapValue04248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04248 (fullRecordGapValue04248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04248_not_prime : ¬(recordGapCenter + 116342).Prime := by
  rw [fullRecordGapTerm04248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04248_fast_pow_mod_ne_one

def fullRecordGapValue04249 : Nat := fullRecordGapCenterValue + 116462

theorem fullRecordGapTerm04249_eq_value :
    recordGapCenter + 116462 = fullRecordGapValue04249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04249 (fullRecordGapValue04249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04249_not_prime : ¬(recordGapCenter + 116462).Prime := by
  rw [fullRecordGapTerm04249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04249_fast_pow_mod_ne_one

def fullRecordGapValue04250 : Nat := fullRecordGapCenterValue + 116642

theorem fullRecordGapTerm04250_eq_value :
    recordGapCenter + 116642 = fullRecordGapValue04250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04250 (fullRecordGapValue04250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04250_not_prime : ¬(recordGapCenter + 116642).Prime := by
  rw [fullRecordGapTerm04250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04250_fast_pow_mod_ne_one

def fullRecordGapValue04251 : Nat := fullRecordGapCenterValue + 116786

theorem fullRecordGapTerm04251_eq_value :
    recordGapCenter + 116786 = fullRecordGapValue04251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04251 (fullRecordGapValue04251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04251_not_prime : ¬(recordGapCenter + 116786).Prime := by
  rw [fullRecordGapTerm04251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04251_fast_pow_mod_ne_one

def fullRecordGapValue04252 : Nat := fullRecordGapCenterValue + 117206

theorem fullRecordGapTerm04252_eq_value :
    recordGapCenter + 117206 = fullRecordGapValue04252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04252 (fullRecordGapValue04252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04252_not_prime : ¬(recordGapCenter + 117206).Prime := by
  rw [fullRecordGapTerm04252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04252_fast_pow_mod_ne_one

def fullRecordGapValue04253 : Nat := fullRecordGapCenterValue + 117398

theorem fullRecordGapTerm04253_eq_value :
    recordGapCenter + 117398 = fullRecordGapValue04253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04253 (fullRecordGapValue04253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04253_not_prime : ¬(recordGapCenter + 117398).Prime := by
  rw [fullRecordGapTerm04253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04253_fast_pow_mod_ne_one

def fullRecordGapValue04254 : Nat := fullRecordGapCenterValue + 117422

theorem fullRecordGapTerm04254_eq_value :
    recordGapCenter + 117422 = fullRecordGapValue04254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04254 (fullRecordGapValue04254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04254_not_prime : ¬(recordGapCenter + 117422).Prime := by
  rw [fullRecordGapTerm04254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04254_fast_pow_mod_ne_one

def fullRecordGapValue04255 : Nat := fullRecordGapCenterValue + 117482

theorem fullRecordGapTerm04255_eq_value :
    recordGapCenter + 117482 = fullRecordGapValue04255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04255 (fullRecordGapValue04255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04255_not_prime : ¬(recordGapCenter + 117482).Prime := by
  rw [fullRecordGapTerm04255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04255_fast_pow_mod_ne_one

def fullRecordGapValue04256 : Nat := fullRecordGapCenterValue + 117926

theorem fullRecordGapTerm04256_eq_value :
    recordGapCenter + 117926 = fullRecordGapValue04256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04256 (fullRecordGapValue04256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04256_not_prime : ¬(recordGapCenter + 117926).Prime := by
  rw [fullRecordGapTerm04256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04256_fast_pow_mod_ne_one

def fullRecordGapValue04257 : Nat := fullRecordGapCenterValue + 118022

theorem fullRecordGapTerm04257_eq_value :
    recordGapCenter + 118022 = fullRecordGapValue04257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04257 (fullRecordGapValue04257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04257_not_prime : ¬(recordGapCenter + 118022).Prime := by
  rw [fullRecordGapTerm04257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04257_fast_pow_mod_ne_one

def fullRecordGapValue04258 : Nat := fullRecordGapCenterValue + 118238

theorem fullRecordGapTerm04258_eq_value :
    recordGapCenter + 118238 = fullRecordGapValue04258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04258 (fullRecordGapValue04258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04258_not_prime : ¬(recordGapCenter + 118238).Prime := by
  rw [fullRecordGapTerm04258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04258_fast_pow_mod_ne_one

def fullRecordGapValue04259 : Nat := fullRecordGapCenterValue + 118272

theorem fullRecordGapTerm04259_eq_value :
    recordGapCenter + 118272 = fullRecordGapValue04259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04259 (fullRecordGapValue04259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04259_not_prime : ¬(recordGapCenter + 118272).Prime := by
  rw [fullRecordGapTerm04259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04259_fast_pow_mod_ne_one

def fullRecordGapValue04260 : Nat := fullRecordGapCenterValue + 118442

theorem fullRecordGapTerm04260_eq_value :
    recordGapCenter + 118442 = fullRecordGapValue04260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04260 (fullRecordGapValue04260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04260_not_prime : ¬(recordGapCenter + 118442).Prime := by
  rw [fullRecordGapTerm04260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04260_fast_pow_mod_ne_one

def fullRecordGapValue04261 : Nat := fullRecordGapCenterValue + 118580

theorem fullRecordGapTerm04261_eq_value :
    recordGapCenter + 118580 = fullRecordGapValue04261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04261 (fullRecordGapValue04261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04261_not_prime : ¬(recordGapCenter + 118580).Prime := by
  rw [fullRecordGapTerm04261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04261_fast_pow_mod_ne_one

def fullRecordGapValue04262 : Nat := fullRecordGapCenterValue + 118886

theorem fullRecordGapTerm04262_eq_value :
    recordGapCenter + 118886 = fullRecordGapValue04262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04262 (fullRecordGapValue04262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04262_not_prime : ¬(recordGapCenter + 118886).Prime := by
  rw [fullRecordGapTerm04262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04262_fast_pow_mod_ne_one

def fullRecordGapValue04263 : Nat := fullRecordGapCenterValue + 119070

theorem fullRecordGapTerm04263_eq_value :
    recordGapCenter + 119070 = fullRecordGapValue04263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04263 (fullRecordGapValue04263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04263_not_prime : ¬(recordGapCenter + 119070).Prime := by
  rw [fullRecordGapTerm04263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04263_fast_pow_mod_ne_one

def fullRecordGapValue04264 : Nat := fullRecordGapCenterValue + 119162

theorem fullRecordGapTerm04264_eq_value :
    recordGapCenter + 119162 = fullRecordGapValue04264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04264 (fullRecordGapValue04264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04264_not_prime : ¬(recordGapCenter + 119162).Prime := by
  rw [fullRecordGapTerm04264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04264_fast_pow_mod_ne_one

def fullRecordGapValue04265 : Nat := fullRecordGapCenterValue + 119222

theorem fullRecordGapTerm04265_eq_value :
    recordGapCenter + 119222 = fullRecordGapValue04265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04265 (fullRecordGapValue04265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04265_not_prime : ¬(recordGapCenter + 119222).Prime := by
  rw [fullRecordGapTerm04265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04265_fast_pow_mod_ne_one

def fullRecordGapValue04266 : Nat := fullRecordGapCenterValue + 119486

theorem fullRecordGapTerm04266_eq_value :
    recordGapCenter + 119486 = fullRecordGapValue04266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04266 (fullRecordGapValue04266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04266_not_prime : ¬(recordGapCenter + 119486).Prime := by
  rw [fullRecordGapTerm04266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04266_fast_pow_mod_ne_one

def fullRecordGapValue04267 : Nat := fullRecordGapCenterValue + 119582

theorem fullRecordGapTerm04267_eq_value :
    recordGapCenter + 119582 = fullRecordGapValue04267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04267 (fullRecordGapValue04267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04267_not_prime : ¬(recordGapCenter + 119582).Prime := by
  rw [fullRecordGapTerm04267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04267_fast_pow_mod_ne_one

def fullRecordGapValue04268 : Nat := fullRecordGapCenterValue + 119618

theorem fullRecordGapTerm04268_eq_value :
    recordGapCenter + 119618 = fullRecordGapValue04268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04268 (fullRecordGapValue04268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04268_not_prime : ¬(recordGapCenter + 119618).Prime := by
  rw [fullRecordGapTerm04268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04268_fast_pow_mod_ne_one

def fullRecordGapValue04269 : Nat := fullRecordGapCenterValue + 119726

theorem fullRecordGapTerm04269_eq_value :
    recordGapCenter + 119726 = fullRecordGapValue04269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04269 (fullRecordGapValue04269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04269_not_prime : ¬(recordGapCenter + 119726).Prime := by
  rw [fullRecordGapTerm04269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04269_fast_pow_mod_ne_one

def fullRecordGapValue04270 : Nat := fullRecordGapCenterValue + 120026

theorem fullRecordGapTerm04270_eq_value :
    recordGapCenter + 120026 = fullRecordGapValue04270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04270 (fullRecordGapValue04270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04270_not_prime : ¬(recordGapCenter + 120026).Prime := by
  rw [fullRecordGapTerm04270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04270_fast_pow_mod_ne_one

def fullRecordGapValue04271 : Nat := fullRecordGapCenterValue + 120338

theorem fullRecordGapTerm04271_eq_value :
    recordGapCenter + 120338 = fullRecordGapValue04271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04271 (fullRecordGapValue04271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04271_not_prime : ¬(recordGapCenter + 120338).Prime := by
  rw [fullRecordGapTerm04271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04271_fast_pow_mod_ne_one

def fullRecordGapValue04272 : Nat := fullRecordGapCenterValue + 120960

theorem fullRecordGapTerm04272_eq_value :
    recordGapCenter + 120960 = fullRecordGapValue04272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04272 (fullRecordGapValue04272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04272_not_prime : ¬(recordGapCenter + 120960).Prime := by
  rw [fullRecordGapTerm04272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04272_fast_pow_mod_ne_one

def fullRecordGapValue04273 : Nat := fullRecordGapCenterValue + 121202

theorem fullRecordGapTerm04273_eq_value :
    recordGapCenter + 121202 = fullRecordGapValue04273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04273 (fullRecordGapValue04273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04273_not_prime : ¬(recordGapCenter + 121202).Prime := by
  rw [fullRecordGapTerm04273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04273_fast_pow_mod_ne_one

def fullRecordGapValue04274 : Nat := fullRecordGapCenterValue + 121262

theorem fullRecordGapTerm04274_eq_value :
    recordGapCenter + 121262 = fullRecordGapValue04274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04274 (fullRecordGapValue04274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04274_not_prime : ¬(recordGapCenter + 121262).Prime := by
  rw [fullRecordGapTerm04274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04274_fast_pow_mod_ne_one

def fullRecordGapValue04275 : Nat := fullRecordGapCenterValue + 121298

theorem fullRecordGapTerm04275_eq_value :
    recordGapCenter + 121298 = fullRecordGapValue04275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04275 (fullRecordGapValue04275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04275_not_prime : ¬(recordGapCenter + 121298).Prime := by
  rw [fullRecordGapTerm04275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04275_fast_pow_mod_ne_one

def fullRecordGapValue04276 : Nat := fullRecordGapCenterValue + 121466

theorem fullRecordGapTerm04276_eq_value :
    recordGapCenter + 121466 = fullRecordGapValue04276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04276 (fullRecordGapValue04276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04276_not_prime : ¬(recordGapCenter + 121466).Prime := by
  rw [fullRecordGapTerm04276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04276_fast_pow_mod_ne_one

def fullRecordGapValue04277 : Nat := fullRecordGapCenterValue + 121718

theorem fullRecordGapTerm04277_eq_value :
    recordGapCenter + 121718 = fullRecordGapValue04277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04277 (fullRecordGapValue04277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04277_not_prime : ¬(recordGapCenter + 121718).Prime := by
  rw [fullRecordGapTerm04277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04277_fast_pow_mod_ne_one

def fullRecordGapValue04278 : Nat := fullRecordGapCenterValue + 121826

theorem fullRecordGapTerm04278_eq_value :
    recordGapCenter + 121826 = fullRecordGapValue04278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04278 (fullRecordGapValue04278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04278_not_prime : ¬(recordGapCenter + 121826).Prime := by
  rw [fullRecordGapTerm04278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04278_fast_pow_mod_ne_one

def fullRecordGapValue04279 : Nat := fullRecordGapCenterValue + 121968

theorem fullRecordGapTerm04279_eq_value :
    recordGapCenter + 121968 = fullRecordGapValue04279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04279 (fullRecordGapValue04279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04279_not_prime : ¬(recordGapCenter + 121968).Prime := by
  rw [fullRecordGapTerm04279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04279_fast_pow_mod_ne_one

def fullRecordGapValue04280 : Nat := fullRecordGapCenterValue + 122102

theorem fullRecordGapTerm04280_eq_value :
    recordGapCenter + 122102 = fullRecordGapValue04280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04280 (fullRecordGapValue04280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04280_not_prime : ¬(recordGapCenter + 122102).Prime := by
  rw [fullRecordGapTerm04280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04280_fast_pow_mod_ne_one

def fullRecordGapValue04281 : Nat := fullRecordGapCenterValue + 122306

theorem fullRecordGapTerm04281_eq_value :
    recordGapCenter + 122306 = fullRecordGapValue04281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04281 (fullRecordGapValue04281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04281_not_prime : ¬(recordGapCenter + 122306).Prime := by
  rw [fullRecordGapTerm04281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04281_fast_pow_mod_ne_one

def fullRecordGapValue04282 : Nat := fullRecordGapCenterValue + 122462

theorem fullRecordGapTerm04282_eq_value :
    recordGapCenter + 122462 = fullRecordGapValue04282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04282 (fullRecordGapValue04282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04282_not_prime : ¬(recordGapCenter + 122462).Prime := by
  rw [fullRecordGapTerm04282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04282_fast_pow_mod_ne_one

def fullRecordGapValue04283 : Nat := fullRecordGapCenterValue + 122882

theorem fullRecordGapTerm04283_eq_value :
    recordGapCenter + 122882 = fullRecordGapValue04283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04283 (fullRecordGapValue04283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04283_not_prime : ¬(recordGapCenter + 122882).Prime := by
  rw [fullRecordGapTerm04283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04283_fast_pow_mod_ne_one

def fullRecordGapValue04284 : Nat := fullRecordGapCenterValue + 123200

theorem fullRecordGapTerm04284_eq_value :
    recordGapCenter + 123200 = fullRecordGapValue04284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04284 (fullRecordGapValue04284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04284_not_prime : ¬(recordGapCenter + 123200).Prime := by
  rw [fullRecordGapTerm04284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04284_fast_pow_mod_ne_one

def fullRecordGapValue04285 : Nat := fullRecordGapCenterValue + 123362

theorem fullRecordGapTerm04285_eq_value :
    recordGapCenter + 123362 = fullRecordGapValue04285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04285 (fullRecordGapValue04285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04285_not_prime : ¬(recordGapCenter + 123362).Prime := by
  rw [fullRecordGapTerm04285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04285_fast_pow_mod_ne_one

def fullRecordGapValue04286 : Nat := fullRecordGapCenterValue + 123446

theorem fullRecordGapTerm04286_eq_value :
    recordGapCenter + 123446 = fullRecordGapValue04286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04286 (fullRecordGapValue04286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04286_not_prime : ¬(recordGapCenter + 123446).Prime := by
  rw [fullRecordGapTerm04286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04286_fast_pow_mod_ne_one

def fullRecordGapValue04287 : Nat := fullRecordGapCenterValue + 123638

theorem fullRecordGapTerm04287_eq_value :
    recordGapCenter + 123638 = fullRecordGapValue04287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04287 (fullRecordGapValue04287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04287_not_prime : ¬(recordGapCenter + 123638).Prime := by
  rw [fullRecordGapTerm04287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04287_fast_pow_mod_ne_one

def fullRecordGapValue04288 : Nat := fullRecordGapCenterValue + 123686

theorem fullRecordGapTerm04288_eq_value :
    recordGapCenter + 123686 = fullRecordGapValue04288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04288 (fullRecordGapValue04288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04288_not_prime : ¬(recordGapCenter + 123686).Prime := by
  rw [fullRecordGapTerm04288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04288_fast_pow_mod_ne_one

def fullRecordGapValue04289 : Nat := fullRecordGapCenterValue + 123722

theorem fullRecordGapTerm04289_eq_value :
    recordGapCenter + 123722 = fullRecordGapValue04289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04289 (fullRecordGapValue04289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04289_not_prime : ¬(recordGapCenter + 123722).Prime := by
  rw [fullRecordGapTerm04289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04289_fast_pow_mod_ne_one

def fullRecordGapValue04290 : Nat := fullRecordGapCenterValue + 123750

theorem fullRecordGapTerm04290_eq_value :
    recordGapCenter + 123750 = fullRecordGapValue04290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04290 (fullRecordGapValue04290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04290_not_prime : ¬(recordGapCenter + 123750).Prime := by
  rw [fullRecordGapTerm04290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04290_fast_pow_mod_ne_one

def fullRecordGapValue04291 : Nat := fullRecordGapCenterValue + 123866

theorem fullRecordGapTerm04291_eq_value :
    recordGapCenter + 123866 = fullRecordGapValue04291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04291 (fullRecordGapValue04291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04291_not_prime : ¬(recordGapCenter + 123866).Prime := by
  rw [fullRecordGapTerm04291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04291_fast_pow_mod_ne_one

def fullRecordGapValue04292 : Nat := fullRecordGapCenterValue + 124022

theorem fullRecordGapTerm04292_eq_value :
    recordGapCenter + 124022 = fullRecordGapValue04292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04292 (fullRecordGapValue04292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04292_not_prime : ¬(recordGapCenter + 124022).Prime := by
  rw [fullRecordGapTerm04292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04292_fast_pow_mod_ne_one

def fullRecordGapValue04293 : Nat := fullRecordGapCenterValue + 124416

theorem fullRecordGapTerm04293_eq_value :
    recordGapCenter + 124416 = fullRecordGapValue04293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04293 (fullRecordGapValue04293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04293_not_prime : ¬(recordGapCenter + 124416).Prime := by
  rw [fullRecordGapTerm04293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04293_fast_pow_mod_ne_one

def fullRecordGapValue04294 : Nat := fullRecordGapCenterValue + 124740

theorem fullRecordGapTerm04294_eq_value :
    recordGapCenter + 124740 = fullRecordGapValue04294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04294 (fullRecordGapValue04294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04294_not_prime : ¬(recordGapCenter + 124740).Prime := by
  rw [fullRecordGapTerm04294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04294_fast_pow_mod_ne_one

def fullRecordGapValue04295 : Nat := fullRecordGapCenterValue + 124766

theorem fullRecordGapTerm04295_eq_value :
    recordGapCenter + 124766 = fullRecordGapValue04295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04295 (fullRecordGapValue04295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04295_not_prime : ¬(recordGapCenter + 124766).Prime := by
  rw [fullRecordGapTerm04295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04295_fast_pow_mod_ne_one

def fullRecordGapValue04296 : Nat := fullRecordGapCenterValue + 125078

theorem fullRecordGapTerm04296_eq_value :
    recordGapCenter + 125078 = fullRecordGapValue04296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04296 (fullRecordGapValue04296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04296_not_prime : ¬(recordGapCenter + 125078).Prime := by
  rw [fullRecordGapTerm04296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04296_fast_pow_mod_ne_one

def fullRecordGapValue04297 : Nat := fullRecordGapCenterValue + 125402

theorem fullRecordGapTerm04297_eq_value :
    recordGapCenter + 125402 = fullRecordGapValue04297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04297 (fullRecordGapValue04297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04297_not_prime : ¬(recordGapCenter + 125402).Prime := by
  rw [fullRecordGapTerm04297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04297_fast_pow_mod_ne_one

def fullRecordGapValue04298 : Nat := fullRecordGapCenterValue + 125486

theorem fullRecordGapTerm04298_eq_value :
    recordGapCenter + 125486 = fullRecordGapValue04298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04298 (fullRecordGapValue04298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04298_not_prime : ¬(recordGapCenter + 125486).Prime := by
  rw [fullRecordGapTerm04298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04298_fast_pow_mod_ne_one

def fullRecordGapValue04299 : Nat := fullRecordGapCenterValue + 125546

theorem fullRecordGapTerm04299_eq_value :
    recordGapCenter + 125546 = fullRecordGapValue04299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04299 (fullRecordGapValue04299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04299_not_prime : ¬(recordGapCenter + 125546).Prime := by
  rw [fullRecordGapTerm04299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04299_fast_pow_mod_ne_one

def fullRecordGapValue04300 : Nat := fullRecordGapCenterValue + 125582

theorem fullRecordGapTerm04300_eq_value :
    recordGapCenter + 125582 = fullRecordGapValue04300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04300 (fullRecordGapValue04300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04300_not_prime : ¬(recordGapCenter + 125582).Prime := by
  rw [fullRecordGapTerm04300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04300_fast_pow_mod_ne_one

def fullRecordGapValue04301 : Nat := fullRecordGapCenterValue + 125738

theorem fullRecordGapTerm04301_eq_value :
    recordGapCenter + 125738 = fullRecordGapValue04301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04301 (fullRecordGapValue04301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04301_not_prime : ¬(recordGapCenter + 125738).Prime := by
  rw [fullRecordGapTerm04301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04301_fast_pow_mod_ne_one

def fullRecordGapValue04302 : Nat := fullRecordGapCenterValue + 125966

theorem fullRecordGapTerm04302_eq_value :
    recordGapCenter + 125966 = fullRecordGapValue04302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04302 (fullRecordGapValue04302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04302_not_prime : ¬(recordGapCenter + 125966).Prime := by
  rw [fullRecordGapTerm04302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04302_fast_pow_mod_ne_one

def fullRecordGapValue04303 : Nat := fullRecordGapCenterValue + 126158

theorem fullRecordGapTerm04303_eq_value :
    recordGapCenter + 126158 = fullRecordGapValue04303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04303 (fullRecordGapValue04303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04303_not_prime : ¬(recordGapCenter + 126158).Prime := by
  rw [fullRecordGapTerm04303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04303_fast_pow_mod_ne_one

def fullRecordGapValue04304 : Nat := fullRecordGapCenterValue + 126662

theorem fullRecordGapTerm04304_eq_value :
    recordGapCenter + 126662 = fullRecordGapValue04304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04304 (fullRecordGapValue04304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04304_not_prime : ¬(recordGapCenter + 126662).Prime := by
  rw [fullRecordGapTerm04304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04304_fast_pow_mod_ne_one

def fullRecordGapValue04305 : Nat := fullRecordGapCenterValue + 126722

theorem fullRecordGapTerm04305_eq_value :
    recordGapCenter + 126722 = fullRecordGapValue04305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04305 (fullRecordGapValue04305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04305_not_prime : ¬(recordGapCenter + 126722).Prime := by
  rw [fullRecordGapTerm04305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04305_fast_pow_mod_ne_one

def fullRecordGapValue04306 : Nat := fullRecordGapCenterValue + 126842

theorem fullRecordGapTerm04306_eq_value :
    recordGapCenter + 126842 = fullRecordGapValue04306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04306 (fullRecordGapValue04306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04306_not_prime : ¬(recordGapCenter + 126842).Prime := by
  rw [fullRecordGapTerm04306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04306_fast_pow_mod_ne_one

def fullRecordGapValue04307 : Nat := fullRecordGapCenterValue + 126878

theorem fullRecordGapTerm04307_eq_value :
    recordGapCenter + 126878 = fullRecordGapValue04307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04307 (fullRecordGapValue04307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04307_not_prime : ¬(recordGapCenter + 126878).Prime := by
  rw [fullRecordGapTerm04307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04307_fast_pow_mod_ne_one

def fullRecordGapValue04308 : Nat := fullRecordGapCenterValue + 127008

theorem fullRecordGapTerm04308_eq_value :
    recordGapCenter + 127008 = fullRecordGapValue04308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04308 (fullRecordGapValue04308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04308_not_prime : ¬(recordGapCenter + 127008).Prime := by
  rw [fullRecordGapTerm04308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04308_fast_pow_mod_ne_one

def fullRecordGapValue04309 : Nat := fullRecordGapCenterValue + 127082

theorem fullRecordGapTerm04309_eq_value :
    recordGapCenter + 127082 = fullRecordGapValue04309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04309 (fullRecordGapValue04309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04309_not_prime : ¬(recordGapCenter + 127082).Prime := by
  rw [fullRecordGapTerm04309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04309_fast_pow_mod_ne_one

def fullRecordGapValue04310 : Nat := fullRecordGapCenterValue + 127118

theorem fullRecordGapTerm04310_eq_value :
    recordGapCenter + 127118 = fullRecordGapValue04310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04310 (fullRecordGapValue04310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04310_not_prime : ¬(recordGapCenter + 127118).Prime := by
  rw [fullRecordGapTerm04310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04310_fast_pow_mod_ne_one

def fullRecordGapValue04311 : Nat := fullRecordGapCenterValue + 127202

theorem fullRecordGapTerm04311_eq_value :
    recordGapCenter + 127202 = fullRecordGapValue04311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04311 (fullRecordGapValue04311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04311_not_prime : ¬(recordGapCenter + 127202).Prime := by
  rw [fullRecordGapTerm04311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04311_fast_pow_mod_ne_one

def fullRecordGapValue04312 : Nat := fullRecordGapCenterValue + 127776

theorem fullRecordGapTerm04312_eq_value :
    recordGapCenter + 127776 = fullRecordGapValue04312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04312 (fullRecordGapValue04312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04312_not_prime : ¬(recordGapCenter + 127776).Prime := by
  rw [fullRecordGapTerm04312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04312_fast_pow_mod_ne_one

def fullRecordGapValue04313 : Nat := fullRecordGapCenterValue + 127898

theorem fullRecordGapTerm04313_eq_value :
    recordGapCenter + 127898 = fullRecordGapValue04313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04313 (fullRecordGapValue04313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04313_not_prime : ¬(recordGapCenter + 127898).Prime := by
  rw [fullRecordGapTerm04313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04313_fast_pow_mod_ne_one

def fullRecordGapValue04314 : Nat := fullRecordGapCenterValue + 128306

theorem fullRecordGapTerm04314_eq_value :
    recordGapCenter + 128306 = fullRecordGapValue04314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04314 (fullRecordGapValue04314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04314_not_prime : ¬(recordGapCenter + 128306).Prime := by
  rw [fullRecordGapTerm04314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04314_fast_pow_mod_ne_one

def fullRecordGapValue04315 : Nat := fullRecordGapCenterValue + 128462

theorem fullRecordGapTerm04315_eq_value :
    recordGapCenter + 128462 = fullRecordGapValue04315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04315 (fullRecordGapValue04315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04315_not_prime : ¬(recordGapCenter + 128462).Prime := by
  rw [fullRecordGapTerm04315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04315_fast_pow_mod_ne_one

def fullRecordGapValue04316 : Nat := fullRecordGapCenterValue + 128606

theorem fullRecordGapTerm04316_eq_value :
    recordGapCenter + 128606 = fullRecordGapValue04316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04316 (fullRecordGapValue04316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04316_not_prime : ¬(recordGapCenter + 128606).Prime := by
  rw [fullRecordGapTerm04316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04316_fast_pow_mod_ne_one

def fullRecordGapValue04317 : Nat := fullRecordGapCenterValue + 128798

theorem fullRecordGapTerm04317_eq_value :
    recordGapCenter + 128798 = fullRecordGapValue04317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04317 (fullRecordGapValue04317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04317_not_prime : ¬(recordGapCenter + 128798).Prime := by
  rw [fullRecordGapTerm04317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04317_fast_pow_mod_ne_one

def fullRecordGapValue04318 : Nat := fullRecordGapCenterValue + 129266

theorem fullRecordGapTerm04318_eq_value :
    recordGapCenter + 129266 = fullRecordGapValue04318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04318 (fullRecordGapValue04318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04318_not_prime : ¬(recordGapCenter + 129266).Prime := by
  rw [fullRecordGapTerm04318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04318_fast_pow_mod_ne_one

def fullRecordGapValue04319 : Nat := fullRecordGapCenterValue + 129326

theorem fullRecordGapTerm04319_eq_value :
    recordGapCenter + 129326 = fullRecordGapValue04319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04319 (fullRecordGapValue04319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04319_not_prime : ¬(recordGapCenter + 129326).Prime := by
  rw [fullRecordGapTerm04319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04319_fast_pow_mod_ne_one

def fullRecordGapValue04320 : Nat := fullRecordGapCenterValue + 129360

theorem fullRecordGapTerm04320_eq_value :
    recordGapCenter + 129360 = fullRecordGapValue04320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04320 (fullRecordGapValue04320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04320_not_prime : ¬(recordGapCenter + 129360).Prime := by
  rw [fullRecordGapTerm04320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04320_fast_pow_mod_ne_one

def fullRecordGapValue04321 : Nat := fullRecordGapCenterValue + 129386

theorem fullRecordGapTerm04321_eq_value :
    recordGapCenter + 129386 = fullRecordGapValue04321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04321 (fullRecordGapValue04321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04321_not_prime : ¬(recordGapCenter + 129386).Prime := by
  rw [fullRecordGapTerm04321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04321_fast_pow_mod_ne_one

def fullRecordGapValue04322 : Nat := fullRecordGapCenterValue + 129566

theorem fullRecordGapTerm04322_eq_value :
    recordGapCenter + 129566 = fullRecordGapValue04322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04322 (fullRecordGapValue04322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04322_not_prime : ¬(recordGapCenter + 129566).Prime := by
  rw [fullRecordGapTerm04322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04322_fast_pow_mod_ne_one

def fullRecordGapValue04323 : Nat := fullRecordGapCenterValue + 129782

theorem fullRecordGapTerm04323_eq_value :
    recordGapCenter + 129782 = fullRecordGapValue04323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04323 (fullRecordGapValue04323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04323_not_prime : ¬(recordGapCenter + 129782).Prime := by
  rw [fullRecordGapTerm04323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04323_fast_pow_mod_ne_one

def fullRecordGapValue04324 : Nat := fullRecordGapCenterValue + 130022

theorem fullRecordGapTerm04324_eq_value :
    recordGapCenter + 130022 = fullRecordGapValue04324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04324 (fullRecordGapValue04324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04324_not_prime : ¬(recordGapCenter + 130022).Prime := by
  rw [fullRecordGapTerm04324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04324_fast_pow_mod_ne_one

def fullRecordGapValue04325 : Nat := fullRecordGapCenterValue + 130106

theorem fullRecordGapTerm04325_eq_value :
    recordGapCenter + 130106 = fullRecordGapValue04325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04325 (fullRecordGapValue04325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04325_not_prime : ¬(recordGapCenter + 130106).Prime := by
  rw [fullRecordGapTerm04325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04325_fast_pow_mod_ne_one

def fullRecordGapValue04326 : Nat := fullRecordGapCenterValue + 130142

theorem fullRecordGapTerm04326_eq_value :
    recordGapCenter + 130142 = fullRecordGapValue04326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04326 (fullRecordGapValue04326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04326_not_prime : ¬(recordGapCenter + 130142).Prime := by
  rw [fullRecordGapTerm04326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04326_fast_pow_mod_ne_one

def fullRecordGapValue04327 : Nat := fullRecordGapCenterValue + 130238

theorem fullRecordGapTerm04327_eq_value :
    recordGapCenter + 130238 = fullRecordGapValue04327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04327 (fullRecordGapValue04327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04327_not_prime : ¬(recordGapCenter + 130238).Prime := by
  rw [fullRecordGapTerm04327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04327_fast_pow_mod_ne_one

def fullRecordGapValue04328 : Nat := fullRecordGapCenterValue + 130406

theorem fullRecordGapTerm04328_eq_value :
    recordGapCenter + 130406 = fullRecordGapValue04328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04328 (fullRecordGapValue04328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04328_not_prime : ¬(recordGapCenter + 130406).Prime := by
  rw [fullRecordGapTerm04328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04328_fast_pow_mod_ne_one

def fullRecordGapValue04329 : Nat := fullRecordGapCenterValue + 130538

theorem fullRecordGapTerm04329_eq_value :
    recordGapCenter + 130538 = fullRecordGapValue04329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04329 (fullRecordGapValue04329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04329_not_prime : ¬(recordGapCenter + 130538).Prime := by
  rw [fullRecordGapTerm04329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04329_fast_pow_mod_ne_one

def fullRecordGapValue04330 : Nat := fullRecordGapCenterValue + 130646

theorem fullRecordGapTerm04330_eq_value :
    recordGapCenter + 130646 = fullRecordGapValue04330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04330 (fullRecordGapValue04330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04330_not_prime : ¬(recordGapCenter + 130646).Prime := by
  rw [fullRecordGapTerm04330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04330_fast_pow_mod_ne_one

def fullRecordGapValue04331 : Nat := fullRecordGapCenterValue + 130706

theorem fullRecordGapTerm04331_eq_value :
    recordGapCenter + 130706 = fullRecordGapValue04331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04331 (fullRecordGapValue04331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04331_not_prime : ¬(recordGapCenter + 130706).Prime := by
  rw [fullRecordGapTerm04331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04331_fast_pow_mod_ne_one

def fullRecordGapValue04332 : Nat := fullRecordGapCenterValue + 130826

theorem fullRecordGapTerm04332_eq_value :
    recordGapCenter + 130826 = fullRecordGapValue04332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04332 (fullRecordGapValue04332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04332_not_prime : ¬(recordGapCenter + 130826).Prime := by
  rw [fullRecordGapTerm04332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04332_fast_pow_mod_ne_one

def fullRecordGapValue04333 : Nat := fullRecordGapCenterValue + 131198

theorem fullRecordGapTerm04333_eq_value :
    recordGapCenter + 131198 = fullRecordGapValue04333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04333 (fullRecordGapValue04333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04333_not_prime : ¬(recordGapCenter + 131198).Prime := by
  rw [fullRecordGapTerm04333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04333_fast_pow_mod_ne_one

def fullRecordGapValue04334 : Nat := fullRecordGapCenterValue + 131220

theorem fullRecordGapTerm04334_eq_value :
    recordGapCenter + 131220 = fullRecordGapValue04334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04334 (fullRecordGapValue04334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04334_not_prime : ¬(recordGapCenter + 131220).Prime := by
  rw [fullRecordGapTerm04334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04334_fast_pow_mod_ne_one

def fullRecordGapValue04335 : Nat := fullRecordGapCenterValue + 131678

theorem fullRecordGapTerm04335_eq_value :
    recordGapCenter + 131678 = fullRecordGapValue04335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04335 (fullRecordGapValue04335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04335_not_prime : ¬(recordGapCenter + 131678).Prime := by
  rw [fullRecordGapTerm04335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04335_fast_pow_mod_ne_one

def fullRecordGapValue04336 : Nat := fullRecordGapCenterValue + 131702

theorem fullRecordGapTerm04336_eq_value :
    recordGapCenter + 131702 = fullRecordGapValue04336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04336 (fullRecordGapValue04336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04336_not_prime : ¬(recordGapCenter + 131702).Prime := by
  rw [fullRecordGapTerm04336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04336_fast_pow_mod_ne_one

def fullRecordGapValue04337 : Nat := fullRecordGapCenterValue + 131966

theorem fullRecordGapTerm04337_eq_value :
    recordGapCenter + 131966 = fullRecordGapValue04337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04337 (fullRecordGapValue04337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04337_not_prime : ¬(recordGapCenter + 131966).Prime := by
  rw [fullRecordGapTerm04337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04337_fast_pow_mod_ne_one

def fullRecordGapValue04338 : Nat := fullRecordGapCenterValue + 132338

theorem fullRecordGapTerm04338_eq_value :
    recordGapCenter + 132338 = fullRecordGapValue04338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04338 (fullRecordGapValue04338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04338_not_prime : ¬(recordGapCenter + 132338).Prime := by
  rw [fullRecordGapTerm04338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04338_fast_pow_mod_ne_one

def fullRecordGapValue04339 : Nat := fullRecordGapCenterValue + 132602

theorem fullRecordGapTerm04339_eq_value :
    recordGapCenter + 132602 = fullRecordGapValue04339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04339 (fullRecordGapValue04339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04339_not_prime : ¬(recordGapCenter + 132602).Prime := by
  rw [fullRecordGapTerm04339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04339_fast_pow_mod_ne_one

def fullRecordGapValue04340 : Nat := fullRecordGapCenterValue + 132686

theorem fullRecordGapTerm04340_eq_value :
    recordGapCenter + 132686 = fullRecordGapValue04340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04340 (fullRecordGapValue04340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04340_not_prime : ¬(recordGapCenter + 132686).Prime := by
  rw [fullRecordGapTerm04340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04340_fast_pow_mod_ne_one

def fullRecordGapValue04341 : Nat := fullRecordGapCenterValue + 132746

theorem fullRecordGapTerm04341_eq_value :
    recordGapCenter + 132746 = fullRecordGapValue04341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04341 (fullRecordGapValue04341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04341_not_prime : ¬(recordGapCenter + 132746).Prime := by
  rw [fullRecordGapTerm04341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04341_fast_pow_mod_ne_one

def fullRecordGapValue04342 : Nat := fullRecordGapCenterValue + 132926

theorem fullRecordGapTerm04342_eq_value :
    recordGapCenter + 132926 = fullRecordGapValue04342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04342 (fullRecordGapValue04342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04342_not_prime : ¬(recordGapCenter + 132926).Prime := by
  rw [fullRecordGapTerm04342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04342_fast_pow_mod_ne_one

def fullRecordGapValue04343 : Nat := fullRecordGapCenterValue + 132998

theorem fullRecordGapTerm04343_eq_value :
    recordGapCenter + 132998 = fullRecordGapValue04343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04343 (fullRecordGapValue04343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04343_not_prime : ¬(recordGapCenter + 132998).Prime := by
  rw [fullRecordGapTerm04343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04343_fast_pow_mod_ne_one

def fullRecordGapValue04344 : Nat := fullRecordGapCenterValue + 133056

theorem fullRecordGapTerm04344_eq_value :
    recordGapCenter + 133056 = fullRecordGapValue04344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04344 (fullRecordGapValue04344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04344_not_prime : ¬(recordGapCenter + 133056).Prime := by
  rw [fullRecordGapTerm04344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04344_fast_pow_mod_ne_one

def fullRecordGapValue04345 : Nat := fullRecordGapCenterValue + 133058

theorem fullRecordGapTerm04345_eq_value :
    recordGapCenter + 133058 = fullRecordGapValue04345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04345 (fullRecordGapValue04345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04345_not_prime : ¬(recordGapCenter + 133058).Prime := by
  rw [fullRecordGapTerm04345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04345_fast_pow_mod_ne_one

def fullRecordGapValue04346 : Nat := fullRecordGapCenterValue + 133106

theorem fullRecordGapTerm04346_eq_value :
    recordGapCenter + 133106 = fullRecordGapValue04346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04346 (fullRecordGapValue04346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04346_not_prime : ¬(recordGapCenter + 133106).Prime := by
  rw [fullRecordGapTerm04346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04346_fast_pow_mod_ne_one

def fullRecordGapValue04347 : Nat := fullRecordGapCenterValue + 133466

theorem fullRecordGapTerm04347_eq_value :
    recordGapCenter + 133466 = fullRecordGapValue04347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04347 (fullRecordGapValue04347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04347_not_prime : ¬(recordGapCenter + 133466).Prime := by
  rw [fullRecordGapTerm04347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04347_fast_pow_mod_ne_one

def fullRecordGapValue04348 : Nat := fullRecordGapCenterValue + 133478

theorem fullRecordGapTerm04348_eq_value :
    recordGapCenter + 133478 = fullRecordGapValue04348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04348 (fullRecordGapValue04348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04348_not_prime : ¬(recordGapCenter + 133478).Prime := by
  rw [fullRecordGapTerm04348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04348_fast_pow_mod_ne_one

def fullRecordGapValue04349 : Nat := fullRecordGapCenterValue + 133526

theorem fullRecordGapTerm04349_eq_value :
    recordGapCenter + 133526 = fullRecordGapValue04349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04349 (fullRecordGapValue04349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04349_not_prime : ¬(recordGapCenter + 133526).Prime := by
  rw [fullRecordGapTerm04349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04349_fast_pow_mod_ne_one

def fullRecordGapValue04350 : Nat := fullRecordGapCenterValue + 133682

theorem fullRecordGapTerm04350_eq_value :
    recordGapCenter + 133682 = fullRecordGapValue04350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04350 (fullRecordGapValue04350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04350_not_prime : ¬(recordGapCenter + 133682).Prime := by
  rw [fullRecordGapTerm04350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04350_fast_pow_mod_ne_one

def fullRecordGapValue04351 : Nat := fullRecordGapCenterValue + 134258

theorem fullRecordGapTerm04351_eq_value :
    recordGapCenter + 134258 = fullRecordGapValue04351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04351 (fullRecordGapValue04351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04351_not_prime : ¬(recordGapCenter + 134258).Prime := by
  rw [fullRecordGapTerm04351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04351_fast_pow_mod_ne_one

def fullRecordGapValue04352 : Nat := fullRecordGapCenterValue + 134750

theorem fullRecordGapTerm04352_eq_value :
    recordGapCenter + 134750 = fullRecordGapValue04352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04352 (fullRecordGapValue04352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04352_not_prime : ¬(recordGapCenter + 134750).Prime := by
  rw [fullRecordGapTerm04352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04352_fast_pow_mod_ne_one

end PrimeFactorUnimodality
