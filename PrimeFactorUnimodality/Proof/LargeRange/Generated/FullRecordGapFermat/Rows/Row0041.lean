import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue10241 : Nat := fullRecordGapCenterValue + 617172

theorem fullRecordGapTerm10241_eq_value :
    recordGapCenter + 617172 = fullRecordGapValue10241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10241 (fullRecordGapValue10241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10241_not_prime : ¬(recordGapCenter + 617172).Prime := by
  rw [fullRecordGapTerm10241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10241_fast_pow_mod_ne_one

def fullRecordGapValue10242 : Nat := fullRecordGapCenterValue + 617246

theorem fullRecordGapTerm10242_eq_value :
    recordGapCenter + 617246 = fullRecordGapValue10242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10242 (fullRecordGapValue10242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10242_not_prime : ¬(recordGapCenter + 617246).Prime := by
  rw [fullRecordGapTerm10242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10242_fast_pow_mod_ne_one

def fullRecordGapValue10243 : Nat := fullRecordGapCenterValue + 617400

theorem fullRecordGapTerm10243_eq_value :
    recordGapCenter + 617400 = fullRecordGapValue10243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10243 (fullRecordGapValue10243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10243_not_prime : ¬(recordGapCenter + 617400).Prime := by
  rw [fullRecordGapTerm10243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10243_fast_pow_mod_ne_one

def fullRecordGapValue10244 : Nat := fullRecordGapCenterValue + 617402

theorem fullRecordGapTerm10244_eq_value :
    recordGapCenter + 617402 = fullRecordGapValue10244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10244 (fullRecordGapValue10244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10244_not_prime : ¬(recordGapCenter + 617402).Prime := by
  rw [fullRecordGapTerm10244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10244_fast_pow_mod_ne_one

def fullRecordGapValue10245 : Nat := fullRecordGapCenterValue + 617510

theorem fullRecordGapTerm10245_eq_value :
    recordGapCenter + 617510 = fullRecordGapValue10245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10245 (fullRecordGapValue10245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10245_not_prime : ¬(recordGapCenter + 617510).Prime := by
  rw [fullRecordGapTerm10245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10245_fast_pow_mod_ne_one

def fullRecordGapValue10246 : Nat := fullRecordGapCenterValue + 617522

theorem fullRecordGapTerm10246_eq_value :
    recordGapCenter + 617522 = fullRecordGapValue10246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10246 (fullRecordGapValue10246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10246_not_prime : ¬(recordGapCenter + 617522).Prime := by
  rw [fullRecordGapTerm10246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10246_fast_pow_mod_ne_one

def fullRecordGapValue10247 : Nat := fullRecordGapCenterValue + 617570

theorem fullRecordGapTerm10247_eq_value :
    recordGapCenter + 617570 = fullRecordGapValue10247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10247 (fullRecordGapValue10247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10247_not_prime : ¬(recordGapCenter + 617570).Prime := by
  rw [fullRecordGapTerm10247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10247_fast_pow_mod_ne_one

def fullRecordGapValue10248 : Nat := fullRecordGapCenterValue + 617618

theorem fullRecordGapTerm10248_eq_value :
    recordGapCenter + 617618 = fullRecordGapValue10248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10248 (fullRecordGapValue10248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10248_not_prime : ¬(recordGapCenter + 617618).Prime := by
  rw [fullRecordGapTerm10248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10248_fast_pow_mod_ne_one

def fullRecordGapValue10249 : Nat := fullRecordGapCenterValue + 617636

theorem fullRecordGapTerm10249_eq_value :
    recordGapCenter + 617636 = fullRecordGapValue10249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10249 (fullRecordGapValue10249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10249_not_prime : ¬(recordGapCenter + 617636).Prime := by
  rw [fullRecordGapTerm10249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10249_fast_pow_mod_ne_one

def fullRecordGapValue10250 : Nat := fullRecordGapCenterValue + 617666

theorem fullRecordGapTerm10250_eq_value :
    recordGapCenter + 617666 = fullRecordGapValue10250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10250 (fullRecordGapValue10250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10250_not_prime : ¬(recordGapCenter + 617666).Prime := by
  rw [fullRecordGapTerm10250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10250_fast_pow_mod_ne_one

def fullRecordGapValue10251 : Nat := fullRecordGapCenterValue + 617676

theorem fullRecordGapTerm10251_eq_value :
    recordGapCenter + 617676 = fullRecordGapValue10251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10251 (fullRecordGapValue10251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10251_not_prime : ¬(recordGapCenter + 617676).Prime := by
  rw [fullRecordGapTerm10251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10251_fast_pow_mod_ne_one

def fullRecordGapValue10252 : Nat := fullRecordGapCenterValue + 617718

theorem fullRecordGapTerm10252_eq_value :
    recordGapCenter + 617718 = fullRecordGapValue10252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10252 (fullRecordGapValue10252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10252_not_prime : ¬(recordGapCenter + 617718).Prime := by
  rw [fullRecordGapTerm10252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10252_fast_pow_mod_ne_one

def fullRecordGapValue10253 : Nat := fullRecordGapCenterValue + 617772

theorem fullRecordGapTerm10253_eq_value :
    recordGapCenter + 617772 = fullRecordGapValue10253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10253 (fullRecordGapValue10253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10253_not_prime : ¬(recordGapCenter + 617772).Prime := by
  rw [fullRecordGapTerm10253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10253_fast_pow_mod_ne_one

def fullRecordGapValue10254 : Nat := fullRecordGapCenterValue + 617858

theorem fullRecordGapTerm10254_eq_value :
    recordGapCenter + 617858 = fullRecordGapValue10254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10254 (fullRecordGapValue10254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10254_not_prime : ¬(recordGapCenter + 617858).Prime := by
  rw [fullRecordGapTerm10254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10254_fast_pow_mod_ne_one

def fullRecordGapValue10255 : Nat := fullRecordGapCenterValue + 617898

theorem fullRecordGapTerm10255_eq_value :
    recordGapCenter + 617898 = fullRecordGapValue10255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10255 (fullRecordGapValue10255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10255_not_prime : ¬(recordGapCenter + 617898).Prime := by
  rw [fullRecordGapTerm10255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10255_fast_pow_mod_ne_one

def fullRecordGapValue10256 : Nat := fullRecordGapCenterValue + 617972

theorem fullRecordGapTerm10256_eq_value :
    recordGapCenter + 617972 = fullRecordGapValue10256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10256 (fullRecordGapValue10256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10256_not_prime : ¬(recordGapCenter + 617972).Prime := by
  rw [fullRecordGapTerm10256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10256_fast_pow_mod_ne_one

def fullRecordGapValue10257 : Nat := fullRecordGapCenterValue + 617978

theorem fullRecordGapTerm10257_eq_value :
    recordGapCenter + 617978 = fullRecordGapValue10257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10257 (fullRecordGapValue10257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10257_not_prime : ¬(recordGapCenter + 617978).Prime := by
  rw [fullRecordGapTerm10257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10257_fast_pow_mod_ne_one

def fullRecordGapValue10258 : Nat := fullRecordGapCenterValue + 618038

theorem fullRecordGapTerm10258_eq_value :
    recordGapCenter + 618038 = fullRecordGapValue10258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10258 (fullRecordGapValue10258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10258_not_prime : ¬(recordGapCenter + 618038).Prime := by
  rw [fullRecordGapTerm10258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10258_fast_pow_mod_ne_one

def fullRecordGapValue10259 : Nat := fullRecordGapCenterValue + 618158

theorem fullRecordGapTerm10259_eq_value :
    recordGapCenter + 618158 = fullRecordGapValue10259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10259 (fullRecordGapValue10259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10259_not_prime : ¬(recordGapCenter + 618158).Prime := by
  rw [fullRecordGapTerm10259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10259_fast_pow_mod_ne_one

def fullRecordGapValue10260 : Nat := fullRecordGapCenterValue + 618182

theorem fullRecordGapTerm10260_eq_value :
    recordGapCenter + 618182 = fullRecordGapValue10260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10260 (fullRecordGapValue10260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10260_not_prime : ¬(recordGapCenter + 618182).Prime := by
  rw [fullRecordGapTerm10260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10260_fast_pow_mod_ne_one

def fullRecordGapValue10261 : Nat := fullRecordGapCenterValue + 618258

theorem fullRecordGapTerm10261_eq_value :
    recordGapCenter + 618258 = fullRecordGapValue10261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10261 (fullRecordGapValue10261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10261_not_prime : ¬(recordGapCenter + 618258).Prime := by
  rw [fullRecordGapTerm10261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10261_fast_pow_mod_ne_one

def fullRecordGapValue10262 : Nat := fullRecordGapCenterValue + 618356

theorem fullRecordGapTerm10262_eq_value :
    recordGapCenter + 618356 = fullRecordGapValue10262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10262 (fullRecordGapValue10262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10262_not_prime : ¬(recordGapCenter + 618356).Prime := by
  rw [fullRecordGapTerm10262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10262_fast_pow_mod_ne_one

def fullRecordGapValue10263 : Nat := fullRecordGapCenterValue + 618468

theorem fullRecordGapTerm10263_eq_value :
    recordGapCenter + 618468 = fullRecordGapValue10263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10263 (fullRecordGapValue10263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10263_not_prime : ¬(recordGapCenter + 618468).Prime := by
  rw [fullRecordGapTerm10263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10263_fast_pow_mod_ne_one

def fullRecordGapValue10264 : Nat := fullRecordGapCenterValue + 618506

theorem fullRecordGapTerm10264_eq_value :
    recordGapCenter + 618506 = fullRecordGapValue10264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10264 (fullRecordGapValue10264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10264_not_prime : ¬(recordGapCenter + 618506).Prime := by
  rw [fullRecordGapTerm10264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10264_fast_pow_mod_ne_one

def fullRecordGapValue10265 : Nat := fullRecordGapCenterValue + 618558

theorem fullRecordGapTerm10265_eq_value :
    recordGapCenter + 618558 = fullRecordGapValue10265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10265 (fullRecordGapValue10265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10265_not_prime : ¬(recordGapCenter + 618558).Prime := by
  rw [fullRecordGapTerm10265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10265_fast_pow_mod_ne_one

def fullRecordGapValue10266 : Nat := fullRecordGapCenterValue + 618572

theorem fullRecordGapTerm10266_eq_value :
    recordGapCenter + 618572 = fullRecordGapValue10266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10266 (fullRecordGapValue10266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10266_not_prime : ¬(recordGapCenter + 618572).Prime := by
  rw [fullRecordGapTerm10266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10266_fast_pow_mod_ne_one

def fullRecordGapValue10267 : Nat := fullRecordGapCenterValue + 618626

theorem fullRecordGapTerm10267_eq_value :
    recordGapCenter + 618626 = fullRecordGapValue10267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10267 (fullRecordGapValue10267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10267_not_prime : ¬(recordGapCenter + 618626).Prime := by
  rw [fullRecordGapTerm10267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10267_fast_pow_mod_ne_one

def fullRecordGapValue10268 : Nat := fullRecordGapCenterValue + 618668

theorem fullRecordGapTerm10268_eq_value :
    recordGapCenter + 618668 = fullRecordGapValue10268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10268 (fullRecordGapValue10268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10268_not_prime : ¬(recordGapCenter + 618668).Prime := by
  rw [fullRecordGapTerm10268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10268_fast_pow_mod_ne_one

def fullRecordGapValue10269 : Nat := fullRecordGapCenterValue + 618738

theorem fullRecordGapTerm10269_eq_value :
    recordGapCenter + 618738 = fullRecordGapValue10269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10269 (fullRecordGapValue10269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10269_not_prime : ¬(recordGapCenter + 618738).Prime := by
  rw [fullRecordGapTerm10269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10269_fast_pow_mod_ne_one

def fullRecordGapValue10270 : Nat := fullRecordGapCenterValue + 618756

theorem fullRecordGapTerm10270_eq_value :
    recordGapCenter + 618756 = fullRecordGapValue10270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10270 (fullRecordGapValue10270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10270_not_prime : ¬(recordGapCenter + 618756).Prime := by
  rw [fullRecordGapTerm10270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10270_fast_pow_mod_ne_one

def fullRecordGapValue10271 : Nat := fullRecordGapCenterValue + 618776

theorem fullRecordGapTerm10271_eq_value :
    recordGapCenter + 618776 = fullRecordGapValue10271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10271 (fullRecordGapValue10271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10271_not_prime : ¬(recordGapCenter + 618776).Prime := by
  rw [fullRecordGapTerm10271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10271_fast_pow_mod_ne_one

def fullRecordGapValue10272 : Nat := fullRecordGapCenterValue + 618846

theorem fullRecordGapTerm10272_eq_value :
    recordGapCenter + 618846 = fullRecordGapValue10272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10272 (fullRecordGapValue10272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10272_not_prime : ¬(recordGapCenter + 618846).Prime := by
  rw [fullRecordGapTerm10272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10272_fast_pow_mod_ne_one

def fullRecordGapValue10273 : Nat := fullRecordGapCenterValue + 618866

theorem fullRecordGapTerm10273_eq_value :
    recordGapCenter + 618866 = fullRecordGapValue10273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10273 (fullRecordGapValue10273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10273_not_prime : ¬(recordGapCenter + 618866).Prime := by
  rw [fullRecordGapTerm10273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10273_fast_pow_mod_ne_one

def fullRecordGapValue10274 : Nat := fullRecordGapCenterValue + 618872

theorem fullRecordGapTerm10274_eq_value :
    recordGapCenter + 618872 = fullRecordGapValue10274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10274 (fullRecordGapValue10274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10274_not_prime : ¬(recordGapCenter + 618872).Prime := by
  rw [fullRecordGapTerm10274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10274_fast_pow_mod_ne_one

def fullRecordGapValue10275 : Nat := fullRecordGapCenterValue + 618938

theorem fullRecordGapTerm10275_eq_value :
    recordGapCenter + 618938 = fullRecordGapValue10275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10275 (fullRecordGapValue10275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10275_not_prime : ¬(recordGapCenter + 618938).Prime := by
  rw [fullRecordGapTerm10275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10275_fast_pow_mod_ne_one

def fullRecordGapValue10276 : Nat := fullRecordGapCenterValue + 619046

theorem fullRecordGapTerm10276_eq_value :
    recordGapCenter + 619046 = fullRecordGapValue10276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10276 (fullRecordGapValue10276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10276_not_prime : ¬(recordGapCenter + 619046).Prime := by
  rw [fullRecordGapTerm10276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10276_fast_pow_mod_ne_one

def fullRecordGapValue10277 : Nat := fullRecordGapCenterValue + 619116

theorem fullRecordGapTerm10277_eq_value :
    recordGapCenter + 619116 = fullRecordGapValue10277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10277 (fullRecordGapValue10277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10277_not_prime : ¬(recordGapCenter + 619116).Prime := by
  rw [fullRecordGapTerm10277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10277_fast_pow_mod_ne_one

def fullRecordGapValue10278 : Nat := fullRecordGapCenterValue + 619118

theorem fullRecordGapTerm10278_eq_value :
    recordGapCenter + 619118 = fullRecordGapValue10278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10278 (fullRecordGapValue10278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10278_not_prime : ¬(recordGapCenter + 619118).Prime := by
  rw [fullRecordGapTerm10278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10278_fast_pow_mod_ne_one

def fullRecordGapValue10279 : Nat := fullRecordGapCenterValue + 619148

theorem fullRecordGapTerm10279_eq_value :
    recordGapCenter + 619148 = fullRecordGapValue10279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10279 (fullRecordGapValue10279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10279_not_prime : ¬(recordGapCenter + 619148).Prime := by
  rw [fullRecordGapTerm10279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10279_fast_pow_mod_ne_one

def fullRecordGapValue10280 : Nat := fullRecordGapCenterValue + 619196

theorem fullRecordGapTerm10280_eq_value :
    recordGapCenter + 619196 = fullRecordGapValue10280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10280 (fullRecordGapValue10280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10280_not_prime : ¬(recordGapCenter + 619196).Prime := by
  rw [fullRecordGapTerm10280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10280_fast_pow_mod_ne_one

def fullRecordGapValue10281 : Nat := fullRecordGapCenterValue + 619356

theorem fullRecordGapTerm10281_eq_value :
    recordGapCenter + 619356 = fullRecordGapValue10281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10281 (fullRecordGapValue10281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10281_not_prime : ¬(recordGapCenter + 619356).Prime := by
  rw [fullRecordGapTerm10281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10281_fast_pow_mod_ne_one

def fullRecordGapValue10282 : Nat := fullRecordGapCenterValue + 619448

theorem fullRecordGapTerm10282_eq_value :
    recordGapCenter + 619448 = fullRecordGapValue10282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10282 (fullRecordGapValue10282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10282_not_prime : ¬(recordGapCenter + 619448).Prime := by
  rw [fullRecordGapTerm10282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10282_fast_pow_mod_ne_one

def fullRecordGapValue10283 : Nat := fullRecordGapCenterValue + 619490

theorem fullRecordGapTerm10283_eq_value :
    recordGapCenter + 619490 = fullRecordGapValue10283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10283 (fullRecordGapValue10283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10283_not_prime : ¬(recordGapCenter + 619490).Prime := by
  rw [fullRecordGapTerm10283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10283_fast_pow_mod_ne_one

def fullRecordGapValue10284 : Nat := fullRecordGapCenterValue + 619532

theorem fullRecordGapTerm10284_eq_value :
    recordGapCenter + 619532 = fullRecordGapValue10284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10284 (fullRecordGapValue10284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10284_not_prime : ¬(recordGapCenter + 619532).Prime := by
  rw [fullRecordGapTerm10284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10284_fast_pow_mod_ne_one

def fullRecordGapValue10285 : Nat := fullRecordGapCenterValue + 619598

theorem fullRecordGapTerm10285_eq_value :
    recordGapCenter + 619598 = fullRecordGapValue10285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10285 (fullRecordGapValue10285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10285_not_prime : ¬(recordGapCenter + 619598).Prime := by
  rw [fullRecordGapTerm10285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10285_fast_pow_mod_ne_one

def fullRecordGapValue10286 : Nat := fullRecordGapCenterValue + 619610

theorem fullRecordGapTerm10286_eq_value :
    recordGapCenter + 619610 = fullRecordGapValue10286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10286 (fullRecordGapValue10286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10286_not_prime : ¬(recordGapCenter + 619610).Prime := by
  rw [fullRecordGapTerm10286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10286_fast_pow_mod_ne_one

def fullRecordGapValue10287 : Nat := fullRecordGapCenterValue + 619790

theorem fullRecordGapTerm10287_eq_value :
    recordGapCenter + 619790 = fullRecordGapValue10287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10287 (fullRecordGapValue10287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10287_not_prime : ¬(recordGapCenter + 619790).Prime := by
  rw [fullRecordGapTerm10287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10287_fast_pow_mod_ne_one

def fullRecordGapValue10288 : Nat := fullRecordGapCenterValue + 619862

theorem fullRecordGapTerm10288_eq_value :
    recordGapCenter + 619862 = fullRecordGapValue10288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10288 (fullRecordGapValue10288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10288_not_prime : ¬(recordGapCenter + 619862).Prime := by
  rw [fullRecordGapTerm10288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10288_fast_pow_mod_ne_one

def fullRecordGapValue10289 : Nat := fullRecordGapCenterValue + 620012

theorem fullRecordGapTerm10289_eq_value :
    recordGapCenter + 620012 = fullRecordGapValue10289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10289 (fullRecordGapValue10289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10289_not_prime : ¬(recordGapCenter + 620012).Prime := by
  rw [fullRecordGapTerm10289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10289_fast_pow_mod_ne_one

def fullRecordGapValue10290 : Nat := fullRecordGapCenterValue + 620036

theorem fullRecordGapTerm10290_eq_value :
    recordGapCenter + 620036 = fullRecordGapValue10290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10290 (fullRecordGapValue10290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10290_not_prime : ¬(recordGapCenter + 620036).Prime := by
  rw [fullRecordGapTerm10290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10290_fast_pow_mod_ne_one

def fullRecordGapValue10291 : Nat := fullRecordGapCenterValue + 620102

theorem fullRecordGapTerm10291_eq_value :
    recordGapCenter + 620102 = fullRecordGapValue10291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10291 (fullRecordGapValue10291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10291_not_prime : ¬(recordGapCenter + 620102).Prime := by
  rw [fullRecordGapTerm10291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10291_fast_pow_mod_ne_one

def fullRecordGapValue10292 : Nat := fullRecordGapCenterValue + 620142

theorem fullRecordGapTerm10292_eq_value :
    recordGapCenter + 620142 = fullRecordGapValue10292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10292 (fullRecordGapValue10292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10292_not_prime : ¬(recordGapCenter + 620142).Prime := by
  rw [fullRecordGapTerm10292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10292_fast_pow_mod_ne_one

def fullRecordGapValue10293 : Nat := fullRecordGapCenterValue + 620148

theorem fullRecordGapTerm10293_eq_value :
    recordGapCenter + 620148 = fullRecordGapValue10293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10293 (fullRecordGapValue10293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10293_not_prime : ¬(recordGapCenter + 620148).Prime := by
  rw [fullRecordGapTerm10293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10293_fast_pow_mod_ne_one

def fullRecordGapValue10294 : Nat := fullRecordGapCenterValue + 620216

theorem fullRecordGapTerm10294_eq_value :
    recordGapCenter + 620216 = fullRecordGapValue10294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10294 (fullRecordGapValue10294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10294_not_prime : ¬(recordGapCenter + 620216).Prime := by
  rw [fullRecordGapTerm10294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10294_fast_pow_mod_ne_one

def fullRecordGapValue10295 : Nat := fullRecordGapCenterValue + 620322

theorem fullRecordGapTerm10295_eq_value :
    recordGapCenter + 620322 = fullRecordGapValue10295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10295 (fullRecordGapValue10295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10295_not_prime : ¬(recordGapCenter + 620322).Prime := by
  rw [fullRecordGapTerm10295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10295_fast_pow_mod_ne_one

def fullRecordGapValue10296 : Nat := fullRecordGapCenterValue + 620348

theorem fullRecordGapTerm10296_eq_value :
    recordGapCenter + 620348 = fullRecordGapValue10296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10296 (fullRecordGapValue10296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10296_not_prime : ¬(recordGapCenter + 620348).Prime := by
  rw [fullRecordGapTerm10296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10296_fast_pow_mod_ne_one

def fullRecordGapValue10297 : Nat := fullRecordGapCenterValue + 620390

theorem fullRecordGapTerm10297_eq_value :
    recordGapCenter + 620390 = fullRecordGapValue10297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10297 (fullRecordGapValue10297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10297_not_prime : ¬(recordGapCenter + 620390).Prime := by
  rw [fullRecordGapTerm10297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10297_fast_pow_mod_ne_one

def fullRecordGapValue10298 : Nat := fullRecordGapCenterValue + 620408

theorem fullRecordGapTerm10298_eq_value :
    recordGapCenter + 620408 = fullRecordGapValue10298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10298 (fullRecordGapValue10298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10298_not_prime : ¬(recordGapCenter + 620408).Prime := by
  rw [fullRecordGapTerm10298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10298_fast_pow_mod_ne_one

def fullRecordGapValue10299 : Nat := fullRecordGapCenterValue + 620456

theorem fullRecordGapTerm10299_eq_value :
    recordGapCenter + 620456 = fullRecordGapValue10299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10299 (fullRecordGapValue10299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10299_not_prime : ¬(recordGapCenter + 620456).Prime := by
  rw [fullRecordGapTerm10299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10299_fast_pow_mod_ne_one

def fullRecordGapValue10300 : Nat := fullRecordGapCenterValue + 620538

theorem fullRecordGapTerm10300_eq_value :
    recordGapCenter + 620538 = fullRecordGapValue10300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10300 (fullRecordGapValue10300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10300_not_prime : ¬(recordGapCenter + 620538).Prime := by
  rw [fullRecordGapTerm10300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10300_fast_pow_mod_ne_one

def fullRecordGapValue10301 : Nat := fullRecordGapCenterValue + 620628

theorem fullRecordGapTerm10301_eq_value :
    recordGapCenter + 620628 = fullRecordGapValue10301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10301 (fullRecordGapValue10301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10301_not_prime : ¬(recordGapCenter + 620628).Prime := by
  rw [fullRecordGapTerm10301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10301_fast_pow_mod_ne_one

def fullRecordGapValue10302 : Nat := fullRecordGapCenterValue + 620742

theorem fullRecordGapTerm10302_eq_value :
    recordGapCenter + 620742 = fullRecordGapValue10302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10302 (fullRecordGapValue10302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10302_not_prime : ¬(recordGapCenter + 620742).Prime := by
  rw [fullRecordGapTerm10302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10302_fast_pow_mod_ne_one

def fullRecordGapValue10303 : Nat := fullRecordGapCenterValue + 620810

theorem fullRecordGapTerm10303_eq_value :
    recordGapCenter + 620810 = fullRecordGapValue10303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10303 (fullRecordGapValue10303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10303_not_prime : ¬(recordGapCenter + 620810).Prime := by
  rw [fullRecordGapTerm10303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10303_fast_pow_mod_ne_one

def fullRecordGapValue10304 : Nat := fullRecordGapCenterValue + 620898

theorem fullRecordGapTerm10304_eq_value :
    recordGapCenter + 620898 = fullRecordGapValue10304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10304 (fullRecordGapValue10304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10304_not_prime : ¬(recordGapCenter + 620898).Prime := by
  rw [fullRecordGapTerm10304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10304_fast_pow_mod_ne_one

def fullRecordGapValue10305 : Nat := fullRecordGapCenterValue + 620928

theorem fullRecordGapTerm10305_eq_value :
    recordGapCenter + 620928 = fullRecordGapValue10305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10305 (fullRecordGapValue10305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10305_not_prime : ¬(recordGapCenter + 620928).Prime := by
  rw [fullRecordGapTerm10305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10305_fast_pow_mod_ne_one

def fullRecordGapValue10306 : Nat := fullRecordGapCenterValue + 620988

theorem fullRecordGapTerm10306_eq_value :
    recordGapCenter + 620988 = fullRecordGapValue10306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10306 (fullRecordGapValue10306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10306_not_prime : ¬(recordGapCenter + 620988).Prime := by
  rw [fullRecordGapTerm10306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10306_fast_pow_mod_ne_one

def fullRecordGapValue10307 : Nat := fullRecordGapCenterValue + 621128

theorem fullRecordGapTerm10307_eq_value :
    recordGapCenter + 621128 = fullRecordGapValue10307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10307 (fullRecordGapValue10307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10307_not_prime : ¬(recordGapCenter + 621128).Prime := by
  rw [fullRecordGapTerm10307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10307_fast_pow_mod_ne_one

def fullRecordGapValue10308 : Nat := fullRecordGapCenterValue + 621176

theorem fullRecordGapTerm10308_eq_value :
    recordGapCenter + 621176 = fullRecordGapValue10308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10308 (fullRecordGapValue10308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10308_not_prime : ¬(recordGapCenter + 621176).Prime := by
  rw [fullRecordGapTerm10308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10308_fast_pow_mod_ne_one

def fullRecordGapValue10309 : Nat := fullRecordGapCenterValue + 621182

theorem fullRecordGapTerm10309_eq_value :
    recordGapCenter + 621182 = fullRecordGapValue10309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10309 (fullRecordGapValue10309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10309_not_prime : ¬(recordGapCenter + 621182).Prime := by
  rw [fullRecordGapTerm10309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10309_fast_pow_mod_ne_one

def fullRecordGapValue10310 : Nat := fullRecordGapCenterValue + 621272

theorem fullRecordGapTerm10310_eq_value :
    recordGapCenter + 621272 = fullRecordGapValue10310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10310 (fullRecordGapValue10310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10310_not_prime : ¬(recordGapCenter + 621272).Prime := by
  rw [fullRecordGapTerm10310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10310_fast_pow_mod_ne_one

def fullRecordGapValue10311 : Nat := fullRecordGapCenterValue + 621290

theorem fullRecordGapTerm10311_eq_value :
    recordGapCenter + 621290 = fullRecordGapValue10311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10311 (fullRecordGapValue10311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10311_not_prime : ¬(recordGapCenter + 621290).Prime := by
  rw [fullRecordGapTerm10311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10311_fast_pow_mod_ne_one

def fullRecordGapValue10312 : Nat := fullRecordGapCenterValue + 621332

theorem fullRecordGapTerm10312_eq_value :
    recordGapCenter + 621332 = fullRecordGapValue10312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10312 (fullRecordGapValue10312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10312_not_prime : ¬(recordGapCenter + 621332).Prime := by
  rw [fullRecordGapTerm10312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10312_fast_pow_mod_ne_one

def fullRecordGapValue10313 : Nat := fullRecordGapCenterValue + 621366

theorem fullRecordGapTerm10313_eq_value :
    recordGapCenter + 621366 = fullRecordGapValue10313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10313 (fullRecordGapValue10313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10313_not_prime : ¬(recordGapCenter + 621366).Prime := by
  rw [fullRecordGapTerm10313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10313_fast_pow_mod_ne_one

def fullRecordGapValue10314 : Nat := fullRecordGapCenterValue + 621482

theorem fullRecordGapTerm10314_eq_value :
    recordGapCenter + 621482 = fullRecordGapValue10314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10314 (fullRecordGapValue10314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10314_not_prime : ¬(recordGapCenter + 621482).Prime := by
  rw [fullRecordGapTerm10314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10314_fast_pow_mod_ne_one

def fullRecordGapValue10315 : Nat := fullRecordGapCenterValue + 621542

theorem fullRecordGapTerm10315_eq_value :
    recordGapCenter + 621542 = fullRecordGapValue10315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10315 (fullRecordGapValue10315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10315_not_prime : ¬(recordGapCenter + 621542).Prime := by
  rw [fullRecordGapTerm10315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10315_fast_pow_mod_ne_one

def fullRecordGapValue10316 : Nat := fullRecordGapCenterValue + 621596

theorem fullRecordGapTerm10316_eq_value :
    recordGapCenter + 621596 = fullRecordGapValue10316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10316 (fullRecordGapValue10316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10316_not_prime : ¬(recordGapCenter + 621596).Prime := by
  rw [fullRecordGapTerm10316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10316_fast_pow_mod_ne_one

def fullRecordGapValue10317 : Nat := fullRecordGapCenterValue + 621602

theorem fullRecordGapTerm10317_eq_value :
    recordGapCenter + 621602 = fullRecordGapValue10317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10317 (fullRecordGapValue10317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10317_not_prime : ¬(recordGapCenter + 621602).Prime := by
  rw [fullRecordGapTerm10317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10317_fast_pow_mod_ne_one

def fullRecordGapValue10318 : Nat := fullRecordGapCenterValue + 621710

theorem fullRecordGapTerm10318_eq_value :
    recordGapCenter + 621710 = fullRecordGapValue10318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10318 (fullRecordGapValue10318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10318_not_prime : ¬(recordGapCenter + 621710).Prime := by
  rw [fullRecordGapTerm10318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10318_fast_pow_mod_ne_one

def fullRecordGapValue10319 : Nat := fullRecordGapCenterValue + 621722

theorem fullRecordGapTerm10319_eq_value :
    recordGapCenter + 621722 = fullRecordGapValue10319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10319 (fullRecordGapValue10319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10319_not_prime : ¬(recordGapCenter + 621722).Prime := by
  rw [fullRecordGapTerm10319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10319_fast_pow_mod_ne_one

def fullRecordGapValue10320 : Nat := fullRecordGapCenterValue + 621812

theorem fullRecordGapTerm10320_eq_value :
    recordGapCenter + 621812 = fullRecordGapValue10320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10320 (fullRecordGapValue10320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10320_not_prime : ¬(recordGapCenter + 621812).Prime := by
  rw [fullRecordGapTerm10320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10320_fast_pow_mod_ne_one

def fullRecordGapValue10321 : Nat := fullRecordGapCenterValue + 621938

theorem fullRecordGapTerm10321_eq_value :
    recordGapCenter + 621938 = fullRecordGapValue10321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10321 (fullRecordGapValue10321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10321_not_prime : ¬(recordGapCenter + 621938).Prime := by
  rw [fullRecordGapTerm10321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10321_fast_pow_mod_ne_one

def fullRecordGapValue10322 : Nat := fullRecordGapCenterValue + 621948

theorem fullRecordGapTerm10322_eq_value :
    recordGapCenter + 621948 = fullRecordGapValue10322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10322 (fullRecordGapValue10322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10322_not_prime : ¬(recordGapCenter + 621948).Prime := by
  rw [fullRecordGapTerm10322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10322_fast_pow_mod_ne_one

def fullRecordGapValue10323 : Nat := fullRecordGapCenterValue + 622010

theorem fullRecordGapTerm10323_eq_value :
    recordGapCenter + 622010 = fullRecordGapValue10323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10323 (fullRecordGapValue10323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10323_not_prime : ¬(recordGapCenter + 622010).Prime := by
  rw [fullRecordGapTerm10323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10323_fast_pow_mod_ne_one

def fullRecordGapValue10324 : Nat := fullRecordGapCenterValue + 622080

theorem fullRecordGapTerm10324_eq_value :
    recordGapCenter + 622080 = fullRecordGapValue10324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10324 (fullRecordGapValue10324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10324_not_prime : ¬(recordGapCenter + 622080).Prime := by
  rw [fullRecordGapTerm10324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10324_fast_pow_mod_ne_one

def fullRecordGapValue10325 : Nat := fullRecordGapCenterValue + 622308

theorem fullRecordGapTerm10325_eq_value :
    recordGapCenter + 622308 = fullRecordGapValue10325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10325 (fullRecordGapValue10325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10325_not_prime : ¬(recordGapCenter + 622308).Prime := by
  rw [fullRecordGapTerm10325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10325_fast_pow_mod_ne_one

def fullRecordGapValue10326 : Nat := fullRecordGapCenterValue + 622316

theorem fullRecordGapTerm10326_eq_value :
    recordGapCenter + 622316 = fullRecordGapValue10326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10326 (fullRecordGapValue10326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10326_not_prime : ¬(recordGapCenter + 622316).Prime := by
  rw [fullRecordGapTerm10326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10326_fast_pow_mod_ne_one

def fullRecordGapValue10327 : Nat := fullRecordGapCenterValue + 622406

theorem fullRecordGapTerm10327_eq_value :
    recordGapCenter + 622406 = fullRecordGapValue10327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10327 (fullRecordGapValue10327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10327_not_prime : ¬(recordGapCenter + 622406).Prime := by
  rw [fullRecordGapTerm10327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10327_fast_pow_mod_ne_one

def fullRecordGapValue10328 : Nat := fullRecordGapCenterValue + 622598

theorem fullRecordGapTerm10328_eq_value :
    recordGapCenter + 622598 = fullRecordGapValue10328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10328 (fullRecordGapValue10328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10328_not_prime : ¬(recordGapCenter + 622598).Prime := by
  rw [fullRecordGapTerm10328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10328_fast_pow_mod_ne_one

def fullRecordGapValue10329 : Nat := fullRecordGapCenterValue + 622652

theorem fullRecordGapTerm10329_eq_value :
    recordGapCenter + 622652 = fullRecordGapValue10329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10329 (fullRecordGapValue10329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10329_not_prime : ¬(recordGapCenter + 622652).Prime := by
  rw [fullRecordGapTerm10329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10329_fast_pow_mod_ne_one

def fullRecordGapValue10330 : Nat := fullRecordGapCenterValue + 622682

theorem fullRecordGapTerm10330_eq_value :
    recordGapCenter + 622682 = fullRecordGapValue10330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10330 (fullRecordGapValue10330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10330_not_prime : ¬(recordGapCenter + 622682).Prime := by
  rw [fullRecordGapTerm10330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10330_fast_pow_mod_ne_one

def fullRecordGapValue10331 : Nat := fullRecordGapCenterValue + 622730

theorem fullRecordGapTerm10331_eq_value :
    recordGapCenter + 622730 = fullRecordGapValue10331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10331 (fullRecordGapValue10331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10331_not_prime : ¬(recordGapCenter + 622730).Prime := by
  rw [fullRecordGapTerm10331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10331_fast_pow_mod_ne_one

def fullRecordGapValue10332 : Nat := fullRecordGapCenterValue + 622742

theorem fullRecordGapTerm10332_eq_value :
    recordGapCenter + 622742 = fullRecordGapValue10332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10332 (fullRecordGapValue10332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10332_not_prime : ¬(recordGapCenter + 622742).Prime := by
  rw [fullRecordGapTerm10332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10332_fast_pow_mod_ne_one

def fullRecordGapValue10333 : Nat := fullRecordGapCenterValue + 622806

theorem fullRecordGapTerm10333_eq_value :
    recordGapCenter + 622806 = fullRecordGapValue10333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10333 (fullRecordGapValue10333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10333_not_prime : ¬(recordGapCenter + 622806).Prime := by
  rw [fullRecordGapTerm10333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10333_fast_pow_mod_ne_one

def fullRecordGapValue10334 : Nat := fullRecordGapCenterValue + 622878

theorem fullRecordGapTerm10334_eq_value :
    recordGapCenter + 622878 = fullRecordGapValue10334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10334 (fullRecordGapValue10334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10334_not_prime : ¬(recordGapCenter + 622878).Prime := by
  rw [fullRecordGapTerm10334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10334_fast_pow_mod_ne_one

def fullRecordGapValue10335 : Nat := fullRecordGapCenterValue + 622956

theorem fullRecordGapTerm10335_eq_value :
    recordGapCenter + 622956 = fullRecordGapValue10335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10335 (fullRecordGapValue10335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10335_not_prime : ¬(recordGapCenter + 622956).Prime := by
  rw [fullRecordGapTerm10335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10335_fast_pow_mod_ne_one

def fullRecordGapValue10336 : Nat := fullRecordGapCenterValue + 622958

theorem fullRecordGapTerm10336_eq_value :
    recordGapCenter + 622958 = fullRecordGapValue10336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10336 (fullRecordGapValue10336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10336_not_prime : ¬(recordGapCenter + 622958).Prime := by
  rw [fullRecordGapTerm10336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10336_fast_pow_mod_ne_one

def fullRecordGapValue10337 : Nat := fullRecordGapCenterValue + 623148

theorem fullRecordGapTerm10337_eq_value :
    recordGapCenter + 623148 = fullRecordGapValue10337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10337 (fullRecordGapValue10337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10337_not_prime : ¬(recordGapCenter + 623148).Prime := by
  rw [fullRecordGapTerm10337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10337_fast_pow_mod_ne_one

def fullRecordGapValue10338 : Nat := fullRecordGapCenterValue + 623270

theorem fullRecordGapTerm10338_eq_value :
    recordGapCenter + 623270 = fullRecordGapValue10338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10338 (fullRecordGapValue10338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10338_not_prime : ¬(recordGapCenter + 623270).Prime := by
  rw [fullRecordGapTerm10338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10338_fast_pow_mod_ne_one

def fullRecordGapValue10339 : Nat := fullRecordGapCenterValue + 623306

theorem fullRecordGapTerm10339_eq_value :
    recordGapCenter + 623306 = fullRecordGapValue10339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10339 (fullRecordGapValue10339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10339_not_prime : ¬(recordGapCenter + 623306).Prime := by
  rw [fullRecordGapTerm10339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10339_fast_pow_mod_ne_one

def fullRecordGapValue10340 : Nat := fullRecordGapCenterValue + 623478

theorem fullRecordGapTerm10340_eq_value :
    recordGapCenter + 623478 = fullRecordGapValue10340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10340 (fullRecordGapValue10340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10340_not_prime : ¬(recordGapCenter + 623478).Prime := by
  rw [fullRecordGapTerm10340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10340_fast_pow_mod_ne_one

def fullRecordGapValue10341 : Nat := fullRecordGapCenterValue + 623486

theorem fullRecordGapTerm10341_eq_value :
    recordGapCenter + 623486 = fullRecordGapValue10341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10341 (fullRecordGapValue10341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10341_not_prime : ¬(recordGapCenter + 623486).Prime := by
  rw [fullRecordGapTerm10341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10341_fast_pow_mod_ne_one

def fullRecordGapValue10342 : Nat := fullRecordGapCenterValue + 623606

theorem fullRecordGapTerm10342_eq_value :
    recordGapCenter + 623606 = fullRecordGapValue10342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10342 (fullRecordGapValue10342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10342_not_prime : ¬(recordGapCenter + 623606).Prime := by
  rw [fullRecordGapTerm10342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10342_fast_pow_mod_ne_one

def fullRecordGapValue10343 : Nat := fullRecordGapCenterValue + 623676

theorem fullRecordGapTerm10343_eq_value :
    recordGapCenter + 623676 = fullRecordGapValue10343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10343 (fullRecordGapValue10343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10343_not_prime : ¬(recordGapCenter + 623676).Prime := by
  rw [fullRecordGapTerm10343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10343_fast_pow_mod_ne_one

def fullRecordGapValue10344 : Nat := fullRecordGapCenterValue + 623700

theorem fullRecordGapTerm10344_eq_value :
    recordGapCenter + 623700 = fullRecordGapValue10344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10344 (fullRecordGapValue10344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10344_not_prime : ¬(recordGapCenter + 623700).Prime := by
  rw [fullRecordGapTerm10344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10344_fast_pow_mod_ne_one

def fullRecordGapValue10345 : Nat := fullRecordGapCenterValue + 623738

theorem fullRecordGapTerm10345_eq_value :
    recordGapCenter + 623738 = fullRecordGapValue10345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10345 (fullRecordGapValue10345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10345_not_prime : ¬(recordGapCenter + 623738).Prime := by
  rw [fullRecordGapTerm10345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10345_fast_pow_mod_ne_one

def fullRecordGapValue10346 : Nat := fullRecordGapCenterValue + 623882

theorem fullRecordGapTerm10346_eq_value :
    recordGapCenter + 623882 = fullRecordGapValue10346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10346 (fullRecordGapValue10346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10346_not_prime : ¬(recordGapCenter + 623882).Prime := by
  rw [fullRecordGapTerm10346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10346_fast_pow_mod_ne_one

def fullRecordGapValue10347 : Nat := fullRecordGapCenterValue + 623886

theorem fullRecordGapTerm10347_eq_value :
    recordGapCenter + 623886 = fullRecordGapValue10347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10347 (fullRecordGapValue10347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10347_not_prime : ¬(recordGapCenter + 623886).Prime := by
  rw [fullRecordGapTerm10347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10347_fast_pow_mod_ne_one

def fullRecordGapValue10348 : Nat := fullRecordGapCenterValue + 623892

theorem fullRecordGapTerm10348_eq_value :
    recordGapCenter + 623892 = fullRecordGapValue10348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10348 (fullRecordGapValue10348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10348_not_prime : ¬(recordGapCenter + 623892).Prime := by
  rw [fullRecordGapTerm10348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10348_fast_pow_mod_ne_one

def fullRecordGapValue10349 : Nat := fullRecordGapCenterValue + 623946

theorem fullRecordGapTerm10349_eq_value :
    recordGapCenter + 623946 = fullRecordGapValue10349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10349 (fullRecordGapValue10349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10349_not_prime : ¬(recordGapCenter + 623946).Prime := by
  rw [fullRecordGapTerm10349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10349_fast_pow_mod_ne_one

def fullRecordGapValue10350 : Nat := fullRecordGapCenterValue + 624018

theorem fullRecordGapTerm10350_eq_value :
    recordGapCenter + 624018 = fullRecordGapValue10350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10350 (fullRecordGapValue10350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10350_not_prime : ¬(recordGapCenter + 624018).Prime := by
  rw [fullRecordGapTerm10350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10350_fast_pow_mod_ne_one

def fullRecordGapValue10351 : Nat := fullRecordGapCenterValue + 624062

theorem fullRecordGapTerm10351_eq_value :
    recordGapCenter + 624062 = fullRecordGapValue10351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10351 (fullRecordGapValue10351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10351_not_prime : ¬(recordGapCenter + 624062).Prime := by
  rw [fullRecordGapTerm10351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10351_fast_pow_mod_ne_one

def fullRecordGapValue10352 : Nat := fullRecordGapCenterValue + 624248

theorem fullRecordGapTerm10352_eq_value :
    recordGapCenter + 624248 = fullRecordGapValue10352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10352 (fullRecordGapValue10352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10352_not_prime : ¬(recordGapCenter + 624248).Prime := by
  rw [fullRecordGapTerm10352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10352_fast_pow_mod_ne_one

def fullRecordGapValue10353 : Nat := fullRecordGapCenterValue + 624282

theorem fullRecordGapTerm10353_eq_value :
    recordGapCenter + 624282 = fullRecordGapValue10353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10353 (fullRecordGapValue10353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10353_not_prime : ¬(recordGapCenter + 624282).Prime := by
  rw [fullRecordGapTerm10353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10353_fast_pow_mod_ne_one

def fullRecordGapValue10354 : Nat := fullRecordGapCenterValue + 624318

theorem fullRecordGapTerm10354_eq_value :
    recordGapCenter + 624318 = fullRecordGapValue10354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10354 (fullRecordGapValue10354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10354_not_prime : ¬(recordGapCenter + 624318).Prime := by
  rw [fullRecordGapTerm10354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10354_fast_pow_mod_ne_one

def fullRecordGapValue10355 : Nat := fullRecordGapCenterValue + 624458

theorem fullRecordGapTerm10355_eq_value :
    recordGapCenter + 624458 = fullRecordGapValue10355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10355 (fullRecordGapValue10355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10355_not_prime : ¬(recordGapCenter + 624458).Prime := by
  rw [fullRecordGapTerm10355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10355_fast_pow_mod_ne_one

def fullRecordGapValue10356 : Nat := fullRecordGapCenterValue + 624482

theorem fullRecordGapTerm10356_eq_value :
    recordGapCenter + 624482 = fullRecordGapValue10356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10356 (fullRecordGapValue10356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10356_not_prime : ¬(recordGapCenter + 624482).Prime := by
  rw [fullRecordGapTerm10356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10356_fast_pow_mod_ne_one

def fullRecordGapValue10357 : Nat := fullRecordGapCenterValue + 624506

theorem fullRecordGapTerm10357_eq_value :
    recordGapCenter + 624506 = fullRecordGapValue10357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10357 (fullRecordGapValue10357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10357_not_prime : ¬(recordGapCenter + 624506).Prime := by
  rw [fullRecordGapTerm10357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10357_fast_pow_mod_ne_one

def fullRecordGapValue10358 : Nat := fullRecordGapCenterValue + 624522

theorem fullRecordGapTerm10358_eq_value :
    recordGapCenter + 624522 = fullRecordGapValue10358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10358 (fullRecordGapValue10358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10358_not_prime : ¬(recordGapCenter + 624522).Prime := by
  rw [fullRecordGapTerm10358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10358_fast_pow_mod_ne_one

def fullRecordGapValue10359 : Nat := fullRecordGapCenterValue + 624578

theorem fullRecordGapTerm10359_eq_value :
    recordGapCenter + 624578 = fullRecordGapValue10359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10359 (fullRecordGapValue10359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10359_not_prime : ¬(recordGapCenter + 624578).Prime := by
  rw [fullRecordGapTerm10359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10359_fast_pow_mod_ne_one

def fullRecordGapValue10360 : Nat := fullRecordGapCenterValue + 624662

theorem fullRecordGapTerm10360_eq_value :
    recordGapCenter + 624662 = fullRecordGapValue10360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10360 (fullRecordGapValue10360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10360_not_prime : ¬(recordGapCenter + 624662).Prime := by
  rw [fullRecordGapTerm10360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10360_fast_pow_mod_ne_one

def fullRecordGapValue10361 : Nat := fullRecordGapCenterValue + 624678

theorem fullRecordGapTerm10361_eq_value :
    recordGapCenter + 624678 = fullRecordGapValue10361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10361 (fullRecordGapValue10361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10361_not_prime : ¬(recordGapCenter + 624678).Prime := by
  rw [fullRecordGapTerm10361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10361_fast_pow_mod_ne_one

def fullRecordGapValue10362 : Nat := fullRecordGapCenterValue + 624698

theorem fullRecordGapTerm10362_eq_value :
    recordGapCenter + 624698 = fullRecordGapValue10362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10362 (fullRecordGapValue10362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10362_not_prime : ¬(recordGapCenter + 624698).Prime := by
  rw [fullRecordGapTerm10362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10362_fast_pow_mod_ne_one

def fullRecordGapValue10363 : Nat := fullRecordGapCenterValue + 624738

theorem fullRecordGapTerm10363_eq_value :
    recordGapCenter + 624738 = fullRecordGapValue10363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10363 (fullRecordGapValue10363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10363_not_prime : ¬(recordGapCenter + 624738).Prime := by
  rw [fullRecordGapTerm10363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10363_fast_pow_mod_ne_one

def fullRecordGapValue10364 : Nat := fullRecordGapCenterValue + 624968

theorem fullRecordGapTerm10364_eq_value :
    recordGapCenter + 624968 = fullRecordGapValue10364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10364 (fullRecordGapValue10364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10364_not_prime : ¬(recordGapCenter + 624968).Prime := by
  rw [fullRecordGapTerm10364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10364_fast_pow_mod_ne_one

def fullRecordGapValue10365 : Nat := fullRecordGapCenterValue + 625028

theorem fullRecordGapTerm10365_eq_value :
    recordGapCenter + 625028 = fullRecordGapValue10365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10365 (fullRecordGapValue10365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10365_not_prime : ¬(recordGapCenter + 625028).Prime := by
  rw [fullRecordGapTerm10365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10365_fast_pow_mod_ne_one

def fullRecordGapValue10366 : Nat := fullRecordGapCenterValue + 625112

theorem fullRecordGapTerm10366_eq_value :
    recordGapCenter + 625112 = fullRecordGapValue10366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10366 (fullRecordGapValue10366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10366_not_prime : ¬(recordGapCenter + 625112).Prime := by
  rw [fullRecordGapTerm10366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10366_fast_pow_mod_ne_one

def fullRecordGapValue10367 : Nat := fullRecordGapCenterValue + 625202

theorem fullRecordGapTerm10367_eq_value :
    recordGapCenter + 625202 = fullRecordGapValue10367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10367 (fullRecordGapValue10367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10367_not_prime : ¬(recordGapCenter + 625202).Prime := by
  rw [fullRecordGapTerm10367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10367_fast_pow_mod_ne_one

def fullRecordGapValue10368 : Nat := fullRecordGapCenterValue + 625256

theorem fullRecordGapTerm10368_eq_value :
    recordGapCenter + 625256 = fullRecordGapValue10368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10368 (fullRecordGapValue10368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10368_not_prime : ¬(recordGapCenter + 625256).Prime := by
  rw [fullRecordGapTerm10368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10368_fast_pow_mod_ne_one

def fullRecordGapValue10369 : Nat := fullRecordGapCenterValue + 625286

theorem fullRecordGapTerm10369_eq_value :
    recordGapCenter + 625286 = fullRecordGapValue10369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10369 (fullRecordGapValue10369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10369_not_prime : ¬(recordGapCenter + 625286).Prime := by
  rw [fullRecordGapTerm10369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10369_fast_pow_mod_ne_one

def fullRecordGapValue10370 : Nat := fullRecordGapCenterValue + 625388

theorem fullRecordGapTerm10370_eq_value :
    recordGapCenter + 625388 = fullRecordGapValue10370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10370 (fullRecordGapValue10370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10370_not_prime : ¬(recordGapCenter + 625388).Prime := by
  rw [fullRecordGapTerm10370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10370_fast_pow_mod_ne_one

def fullRecordGapValue10371 : Nat := fullRecordGapCenterValue + 625398

theorem fullRecordGapTerm10371_eq_value :
    recordGapCenter + 625398 = fullRecordGapValue10371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10371 (fullRecordGapValue10371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10371_not_prime : ¬(recordGapCenter + 625398).Prime := by
  rw [fullRecordGapTerm10371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10371_fast_pow_mod_ne_one

def fullRecordGapValue10372 : Nat := fullRecordGapCenterValue + 625406

theorem fullRecordGapTerm10372_eq_value :
    recordGapCenter + 625406 = fullRecordGapValue10372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10372 (fullRecordGapValue10372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10372_not_prime : ¬(recordGapCenter + 625406).Prime := by
  rw [fullRecordGapTerm10372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10372_fast_pow_mod_ne_one

def fullRecordGapValue10373 : Nat := fullRecordGapCenterValue + 625490

theorem fullRecordGapTerm10373_eq_value :
    recordGapCenter + 625490 = fullRecordGapValue10373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10373 (fullRecordGapValue10373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10373_not_prime : ¬(recordGapCenter + 625490).Prime := by
  rw [fullRecordGapTerm10373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10373_fast_pow_mod_ne_one

def fullRecordGapValue10374 : Nat := fullRecordGapCenterValue + 625598

theorem fullRecordGapTerm10374_eq_value :
    recordGapCenter + 625598 = fullRecordGapValue10374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10374 (fullRecordGapValue10374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10374_not_prime : ¬(recordGapCenter + 625598).Prime := by
  rw [fullRecordGapTerm10374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10374_fast_pow_mod_ne_one

def fullRecordGapValue10375 : Nat := fullRecordGapCenterValue + 625682

theorem fullRecordGapTerm10375_eq_value :
    recordGapCenter + 625682 = fullRecordGapValue10375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10375 (fullRecordGapValue10375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10375_not_prime : ¬(recordGapCenter + 625682).Prime := by
  rw [fullRecordGapTerm10375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10375_fast_pow_mod_ne_one

def fullRecordGapValue10376 : Nat := fullRecordGapCenterValue + 625686

theorem fullRecordGapTerm10376_eq_value :
    recordGapCenter + 625686 = fullRecordGapValue10376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10376 (fullRecordGapValue10376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10376_not_prime : ¬(recordGapCenter + 625686).Prime := by
  rw [fullRecordGapTerm10376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10376_fast_pow_mod_ne_one

def fullRecordGapValue10377 : Nat := fullRecordGapCenterValue + 625832

theorem fullRecordGapTerm10377_eq_value :
    recordGapCenter + 625832 = fullRecordGapValue10377 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10377_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10377 (fullRecordGapValue10377 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10377_not_prime : ¬(recordGapCenter + 625832).Prime := by
  rw [fullRecordGapTerm10377_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10377, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10377_fast_pow_mod_ne_one

def fullRecordGapValue10378 : Nat := fullRecordGapCenterValue + 625866

theorem fullRecordGapTerm10378_eq_value :
    recordGapCenter + 625866 = fullRecordGapValue10378 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10378_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10378 (fullRecordGapValue10378 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10378_not_prime : ¬(recordGapCenter + 625866).Prime := by
  rw [fullRecordGapTerm10378_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10378, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10378_fast_pow_mod_ne_one

def fullRecordGapValue10379 : Nat := fullRecordGapCenterValue + 625868

theorem fullRecordGapTerm10379_eq_value :
    recordGapCenter + 625868 = fullRecordGapValue10379 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10379_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10379 (fullRecordGapValue10379 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10379_not_prime : ¬(recordGapCenter + 625868).Prime := by
  rw [fullRecordGapTerm10379_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10379, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10379_fast_pow_mod_ne_one

def fullRecordGapValue10380 : Nat := fullRecordGapCenterValue + 625910

theorem fullRecordGapTerm10380_eq_value :
    recordGapCenter + 625910 = fullRecordGapValue10380 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10380_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10380 (fullRecordGapValue10380 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10380_not_prime : ¬(recordGapCenter + 625910).Prime := by
  rw [fullRecordGapTerm10380_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10380, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10380_fast_pow_mod_ne_one

def fullRecordGapValue10381 : Nat := fullRecordGapCenterValue + 625958

theorem fullRecordGapTerm10381_eq_value :
    recordGapCenter + 625958 = fullRecordGapValue10381 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10381_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10381 (fullRecordGapValue10381 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10381_not_prime : ¬(recordGapCenter + 625958).Prime := by
  rw [fullRecordGapTerm10381_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10381, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10381_fast_pow_mod_ne_one

def fullRecordGapValue10382 : Nat := fullRecordGapCenterValue + 626018

theorem fullRecordGapTerm10382_eq_value :
    recordGapCenter + 626018 = fullRecordGapValue10382 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10382_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10382 (fullRecordGapValue10382 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10382_not_prime : ¬(recordGapCenter + 626018).Prime := by
  rw [fullRecordGapTerm10382_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10382, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10382_fast_pow_mod_ne_one

def fullRecordGapValue10383 : Nat := fullRecordGapCenterValue + 626162

theorem fullRecordGapTerm10383_eq_value :
    recordGapCenter + 626162 = fullRecordGapValue10383 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10383_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10383 (fullRecordGapValue10383 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10383_not_prime : ¬(recordGapCenter + 626162).Prime := by
  rw [fullRecordGapTerm10383_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10383, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10383_fast_pow_mod_ne_one

def fullRecordGapValue10384 : Nat := fullRecordGapCenterValue + 626196

theorem fullRecordGapTerm10384_eq_value :
    recordGapCenter + 626196 = fullRecordGapValue10384 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10384_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10384 (fullRecordGapValue10384 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10384_not_prime : ¬(recordGapCenter + 626196).Prime := by
  rw [fullRecordGapTerm10384_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10384, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10384_fast_pow_mod_ne_one

def fullRecordGapValue10385 : Nat := fullRecordGapCenterValue + 626286

theorem fullRecordGapTerm10385_eq_value :
    recordGapCenter + 626286 = fullRecordGapValue10385 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10385_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10385 (fullRecordGapValue10385 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10385_not_prime : ¬(recordGapCenter + 626286).Prime := by
  rw [fullRecordGapTerm10385_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10385, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10385_fast_pow_mod_ne_one

def fullRecordGapValue10386 : Nat := fullRecordGapCenterValue + 626298

theorem fullRecordGapTerm10386_eq_value :
    recordGapCenter + 626298 = fullRecordGapValue10386 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10386_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10386 (fullRecordGapValue10386 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10386_not_prime : ¬(recordGapCenter + 626298).Prime := by
  rw [fullRecordGapTerm10386_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10386, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10386_fast_pow_mod_ne_one

def fullRecordGapValue10387 : Nat := fullRecordGapCenterValue + 626306

theorem fullRecordGapTerm10387_eq_value :
    recordGapCenter + 626306 = fullRecordGapValue10387 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10387_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10387 (fullRecordGapValue10387 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10387_not_prime : ¬(recordGapCenter + 626306).Prime := by
  rw [fullRecordGapTerm10387_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10387, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10387_fast_pow_mod_ne_one

def fullRecordGapValue10388 : Nat := fullRecordGapCenterValue + 626330

theorem fullRecordGapTerm10388_eq_value :
    recordGapCenter + 626330 = fullRecordGapValue10388 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10388_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10388 (fullRecordGapValue10388 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10388_not_prime : ¬(recordGapCenter + 626330).Prime := by
  rw [fullRecordGapTerm10388_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10388, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10388_fast_pow_mod_ne_one

def fullRecordGapValue10389 : Nat := fullRecordGapCenterValue + 626390

theorem fullRecordGapTerm10389_eq_value :
    recordGapCenter + 626390 = fullRecordGapValue10389 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10389_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10389 (fullRecordGapValue10389 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10389_not_prime : ¬(recordGapCenter + 626390).Prime := by
  rw [fullRecordGapTerm10389_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10389, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10389_fast_pow_mod_ne_one

def fullRecordGapValue10390 : Nat := fullRecordGapCenterValue + 626412

theorem fullRecordGapTerm10390_eq_value :
    recordGapCenter + 626412 = fullRecordGapValue10390 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10390_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10390 (fullRecordGapValue10390 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10390_not_prime : ¬(recordGapCenter + 626412).Prime := by
  rw [fullRecordGapTerm10390_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10390, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10390_fast_pow_mod_ne_one

def fullRecordGapValue10391 : Nat := fullRecordGapCenterValue + 626498

theorem fullRecordGapTerm10391_eq_value :
    recordGapCenter + 626498 = fullRecordGapValue10391 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10391_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10391 (fullRecordGapValue10391 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10391_not_prime : ¬(recordGapCenter + 626498).Prime := by
  rw [fullRecordGapTerm10391_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10391, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10391_fast_pow_mod_ne_one

def fullRecordGapValue10392 : Nat := fullRecordGapCenterValue + 626636

theorem fullRecordGapTerm10392_eq_value :
    recordGapCenter + 626636 = fullRecordGapValue10392 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10392_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10392 (fullRecordGapValue10392 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10392_not_prime : ¬(recordGapCenter + 626636).Prime := by
  rw [fullRecordGapTerm10392_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10392, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10392_fast_pow_mod_ne_one

def fullRecordGapValue10393 : Nat := fullRecordGapCenterValue + 626676

theorem fullRecordGapTerm10393_eq_value :
    recordGapCenter + 626676 = fullRecordGapValue10393 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10393_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10393 (fullRecordGapValue10393 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10393_not_prime : ¬(recordGapCenter + 626676).Prime := by
  rw [fullRecordGapTerm10393_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10393, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10393_fast_pow_mod_ne_one

def fullRecordGapValue10394 : Nat := fullRecordGapCenterValue + 626708

theorem fullRecordGapTerm10394_eq_value :
    recordGapCenter + 626708 = fullRecordGapValue10394 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10394_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10394 (fullRecordGapValue10394 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10394_not_prime : ¬(recordGapCenter + 626708).Prime := by
  rw [fullRecordGapTerm10394_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10394, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10394_fast_pow_mod_ne_one

def fullRecordGapValue10395 : Nat := fullRecordGapCenterValue + 626822

theorem fullRecordGapTerm10395_eq_value :
    recordGapCenter + 626822 = fullRecordGapValue10395 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10395_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10395 (fullRecordGapValue10395 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10395_not_prime : ¬(recordGapCenter + 626822).Prime := by
  rw [fullRecordGapTerm10395_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10395, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10395_fast_pow_mod_ne_one

def fullRecordGapValue10396 : Nat := fullRecordGapCenterValue + 626838

theorem fullRecordGapTerm10396_eq_value :
    recordGapCenter + 626838 = fullRecordGapValue10396 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10396_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10396 (fullRecordGapValue10396 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10396_not_prime : ¬(recordGapCenter + 626838).Prime := by
  rw [fullRecordGapTerm10396_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10396, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10396_fast_pow_mod_ne_one

def fullRecordGapValue10397 : Nat := fullRecordGapCenterValue + 626942

theorem fullRecordGapTerm10397_eq_value :
    recordGapCenter + 626942 = fullRecordGapValue10397 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10397_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10397 (fullRecordGapValue10397 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10397_not_prime : ¬(recordGapCenter + 626942).Prime := by
  rw [fullRecordGapTerm10397_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10397, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10397_fast_pow_mod_ne_one

def fullRecordGapValue10398 : Nat := fullRecordGapCenterValue + 627086

theorem fullRecordGapTerm10398_eq_value :
    recordGapCenter + 627086 = fullRecordGapValue10398 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10398_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10398 (fullRecordGapValue10398 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10398_not_prime : ¬(recordGapCenter + 627086).Prime := by
  rw [fullRecordGapTerm10398_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10398, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10398_fast_pow_mod_ne_one

def fullRecordGapValue10399 : Nat := fullRecordGapCenterValue + 627158

theorem fullRecordGapTerm10399_eq_value :
    recordGapCenter + 627158 = fullRecordGapValue10399 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10399_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10399 (fullRecordGapValue10399 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10399_not_prime : ¬(recordGapCenter + 627158).Prime := by
  rw [fullRecordGapTerm10399_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10399, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10399_fast_pow_mod_ne_one

def fullRecordGapValue10400 : Nat := fullRecordGapCenterValue + 627200

theorem fullRecordGapTerm10400_eq_value :
    recordGapCenter + 627200 = fullRecordGapValue10400 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10400_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10400 (fullRecordGapValue10400 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10400_not_prime : ¬(recordGapCenter + 627200).Prime := by
  rw [fullRecordGapTerm10400_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10400, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10400_fast_pow_mod_ne_one

def fullRecordGapValue10401 : Nat := fullRecordGapCenterValue + 627258

theorem fullRecordGapTerm10401_eq_value :
    recordGapCenter + 627258 = fullRecordGapValue10401 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10401_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10401 (fullRecordGapValue10401 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10401_not_prime : ¬(recordGapCenter + 627258).Prime := by
  rw [fullRecordGapTerm10401_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10401, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10401_fast_pow_mod_ne_one

def fullRecordGapValue10402 : Nat := fullRecordGapCenterValue + 627306

theorem fullRecordGapTerm10402_eq_value :
    recordGapCenter + 627306 = fullRecordGapValue10402 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10402_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10402 (fullRecordGapValue10402 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10402_not_prime : ¬(recordGapCenter + 627306).Prime := by
  rw [fullRecordGapTerm10402_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10402, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10402_fast_pow_mod_ne_one

def fullRecordGapValue10403 : Nat := fullRecordGapCenterValue + 627366

theorem fullRecordGapTerm10403_eq_value :
    recordGapCenter + 627366 = fullRecordGapValue10403 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10403_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10403 (fullRecordGapValue10403 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10403_not_prime : ¬(recordGapCenter + 627366).Prime := by
  rw [fullRecordGapTerm10403_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10403, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10403_fast_pow_mod_ne_one

def fullRecordGapValue10404 : Nat := fullRecordGapCenterValue + 627468

theorem fullRecordGapTerm10404_eq_value :
    recordGapCenter + 627468 = fullRecordGapValue10404 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10404_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10404 (fullRecordGapValue10404 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10404_not_prime : ¬(recordGapCenter + 627468).Prime := by
  rw [fullRecordGapTerm10404_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10404, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10404_fast_pow_mod_ne_one

def fullRecordGapValue10405 : Nat := fullRecordGapCenterValue + 627582

theorem fullRecordGapTerm10405_eq_value :
    recordGapCenter + 627582 = fullRecordGapValue10405 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10405_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10405 (fullRecordGapValue10405 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10405_not_prime : ¬(recordGapCenter + 627582).Prime := by
  rw [fullRecordGapTerm10405_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10405, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10405_fast_pow_mod_ne_one

def fullRecordGapValue10406 : Nat := fullRecordGapCenterValue + 627756

theorem fullRecordGapTerm10406_eq_value :
    recordGapCenter + 627756 = fullRecordGapValue10406 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10406_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10406 (fullRecordGapValue10406 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10406_not_prime : ¬(recordGapCenter + 627756).Prime := by
  rw [fullRecordGapTerm10406_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10406, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10406_fast_pow_mod_ne_one

def fullRecordGapValue10407 : Nat := fullRecordGapCenterValue + 627758

theorem fullRecordGapTerm10407_eq_value :
    recordGapCenter + 627758 = fullRecordGapValue10407 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10407_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10407 (fullRecordGapValue10407 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10407_not_prime : ¬(recordGapCenter + 627758).Prime := by
  rw [fullRecordGapTerm10407_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10407, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10407_fast_pow_mod_ne_one

def fullRecordGapValue10408 : Nat := fullRecordGapCenterValue + 627842

theorem fullRecordGapTerm10408_eq_value :
    recordGapCenter + 627842 = fullRecordGapValue10408 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10408_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10408 (fullRecordGapValue10408 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10408_not_prime : ¬(recordGapCenter + 627842).Prime := by
  rw [fullRecordGapTerm10408_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10408, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10408_fast_pow_mod_ne_one

def fullRecordGapValue10409 : Nat := fullRecordGapCenterValue + 627866

theorem fullRecordGapTerm10409_eq_value :
    recordGapCenter + 627866 = fullRecordGapValue10409 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10409_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10409 (fullRecordGapValue10409 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10409_not_prime : ¬(recordGapCenter + 627866).Prime := by
  rw [fullRecordGapTerm10409_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10409, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10409_fast_pow_mod_ne_one

def fullRecordGapValue10410 : Nat := fullRecordGapCenterValue + 628076

theorem fullRecordGapTerm10410_eq_value :
    recordGapCenter + 628076 = fullRecordGapValue10410 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10410_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10410 (fullRecordGapValue10410 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10410_not_prime : ¬(recordGapCenter + 628076).Prime := by
  rw [fullRecordGapTerm10410_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10410, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10410_fast_pow_mod_ne_one

def fullRecordGapValue10411 : Nat := fullRecordGapCenterValue + 628086

theorem fullRecordGapTerm10411_eq_value :
    recordGapCenter + 628086 = fullRecordGapValue10411 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10411_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10411 (fullRecordGapValue10411 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10411_not_prime : ¬(recordGapCenter + 628086).Prime := by
  rw [fullRecordGapTerm10411_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10411, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10411_fast_pow_mod_ne_one

def fullRecordGapValue10412 : Nat := fullRecordGapCenterValue + 628190

theorem fullRecordGapTerm10412_eq_value :
    recordGapCenter + 628190 = fullRecordGapValue10412 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10412_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10412 (fullRecordGapValue10412 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10412_not_prime : ¬(recordGapCenter + 628190).Prime := by
  rw [fullRecordGapTerm10412_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10412, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10412_fast_pow_mod_ne_one

def fullRecordGapValue10413 : Nat := fullRecordGapCenterValue + 628302

theorem fullRecordGapTerm10413_eq_value :
    recordGapCenter + 628302 = fullRecordGapValue10413 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10413_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10413 (fullRecordGapValue10413 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10413_not_prime : ¬(recordGapCenter + 628302).Prime := by
  rw [fullRecordGapTerm10413_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10413, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10413_fast_pow_mod_ne_one

def fullRecordGapValue10414 : Nat := fullRecordGapCenterValue + 628322

theorem fullRecordGapTerm10414_eq_value :
    recordGapCenter + 628322 = fullRecordGapValue10414 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10414_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10414 (fullRecordGapValue10414 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10414_not_prime : ¬(recordGapCenter + 628322).Prime := by
  rw [fullRecordGapTerm10414_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10414, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10414_fast_pow_mod_ne_one

def fullRecordGapValue10415 : Nat := fullRecordGapCenterValue + 628346

theorem fullRecordGapTerm10415_eq_value :
    recordGapCenter + 628346 = fullRecordGapValue10415 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10415_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10415 (fullRecordGapValue10415 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10415_not_prime : ¬(recordGapCenter + 628346).Prime := by
  rw [fullRecordGapTerm10415_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10415, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10415_fast_pow_mod_ne_one

def fullRecordGapValue10416 : Nat := fullRecordGapCenterValue + 628412

theorem fullRecordGapTerm10416_eq_value :
    recordGapCenter + 628412 = fullRecordGapValue10416 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10416_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10416 (fullRecordGapValue10416 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10416_not_prime : ¬(recordGapCenter + 628412).Prime := by
  rw [fullRecordGapTerm10416_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10416, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10416_fast_pow_mod_ne_one

def fullRecordGapValue10417 : Nat := fullRecordGapCenterValue + 628418

theorem fullRecordGapTerm10417_eq_value :
    recordGapCenter + 628418 = fullRecordGapValue10417 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10417_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10417 (fullRecordGapValue10417 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10417_not_prime : ¬(recordGapCenter + 628418).Prime := by
  rw [fullRecordGapTerm10417_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10417, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10417_fast_pow_mod_ne_one

def fullRecordGapValue10418 : Nat := fullRecordGapCenterValue + 628478

theorem fullRecordGapTerm10418_eq_value :
    recordGapCenter + 628478 = fullRecordGapValue10418 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10418_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10418 (fullRecordGapValue10418 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10418_not_prime : ¬(recordGapCenter + 628478).Prime := by
  rw [fullRecordGapTerm10418_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10418, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10418_fast_pow_mod_ne_one

def fullRecordGapValue10419 : Nat := fullRecordGapCenterValue + 628526

theorem fullRecordGapTerm10419_eq_value :
    recordGapCenter + 628526 = fullRecordGapValue10419 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10419_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10419 (fullRecordGapValue10419 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10419_not_prime : ¬(recordGapCenter + 628526).Prime := by
  rw [fullRecordGapTerm10419_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10419, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10419_fast_pow_mod_ne_one

def fullRecordGapValue10420 : Nat := fullRecordGapCenterValue + 628532

theorem fullRecordGapTerm10420_eq_value :
    recordGapCenter + 628532 = fullRecordGapValue10420 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10420_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10420 (fullRecordGapValue10420 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10420_not_prime : ¬(recordGapCenter + 628532).Prime := by
  rw [fullRecordGapTerm10420_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10420, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10420_fast_pow_mod_ne_one

def fullRecordGapValue10421 : Nat := fullRecordGapCenterValue + 628566

theorem fullRecordGapTerm10421_eq_value :
    recordGapCenter + 628566 = fullRecordGapValue10421 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10421_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10421 (fullRecordGapValue10421 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10421_not_prime : ¬(recordGapCenter + 628566).Prime := by
  rw [fullRecordGapTerm10421_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10421, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10421_fast_pow_mod_ne_one

def fullRecordGapValue10422 : Nat := fullRecordGapCenterValue + 628568

theorem fullRecordGapTerm10422_eq_value :
    recordGapCenter + 628568 = fullRecordGapValue10422 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10422_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10422 (fullRecordGapValue10422 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10422_not_prime : ¬(recordGapCenter + 628568).Prime := by
  rw [fullRecordGapTerm10422_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10422, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10422_fast_pow_mod_ne_one

def fullRecordGapValue10423 : Nat := fullRecordGapCenterValue + 628598

theorem fullRecordGapTerm10423_eq_value :
    recordGapCenter + 628598 = fullRecordGapValue10423 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10423_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10423 (fullRecordGapValue10423 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10423_not_prime : ¬(recordGapCenter + 628598).Prime := by
  rw [fullRecordGapTerm10423_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10423, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10423_fast_pow_mod_ne_one

def fullRecordGapValue10424 : Nat := fullRecordGapCenterValue + 628638

theorem fullRecordGapTerm10424_eq_value :
    recordGapCenter + 628638 = fullRecordGapValue10424 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10424_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10424 (fullRecordGapValue10424 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10424_not_prime : ¬(recordGapCenter + 628638).Prime := by
  rw [fullRecordGapTerm10424_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10424, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10424_fast_pow_mod_ne_one

def fullRecordGapValue10425 : Nat := fullRecordGapCenterValue + 628652

theorem fullRecordGapTerm10425_eq_value :
    recordGapCenter + 628652 = fullRecordGapValue10425 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10425_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10425 (fullRecordGapValue10425 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10425_not_prime : ¬(recordGapCenter + 628652).Prime := by
  rw [fullRecordGapTerm10425_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10425, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10425_fast_pow_mod_ne_one

def fullRecordGapValue10426 : Nat := fullRecordGapCenterValue + 628730

theorem fullRecordGapTerm10426_eq_value :
    recordGapCenter + 628730 = fullRecordGapValue10426 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10426_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10426 (fullRecordGapValue10426 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10426_not_prime : ¬(recordGapCenter + 628730).Prime := by
  rw [fullRecordGapTerm10426_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10426, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10426_fast_pow_mod_ne_one

def fullRecordGapValue10427 : Nat := fullRecordGapCenterValue + 628806

theorem fullRecordGapTerm10427_eq_value :
    recordGapCenter + 628806 = fullRecordGapValue10427 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10427_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10427 (fullRecordGapValue10427 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10427_not_prime : ¬(recordGapCenter + 628806).Prime := by
  rw [fullRecordGapTerm10427_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10427, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10427_fast_pow_mod_ne_one

def fullRecordGapValue10428 : Nat := fullRecordGapCenterValue + 628818

theorem fullRecordGapTerm10428_eq_value :
    recordGapCenter + 628818 = fullRecordGapValue10428 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10428_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10428 (fullRecordGapValue10428 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10428_not_prime : ¬(recordGapCenter + 628818).Prime := by
  rw [fullRecordGapTerm10428_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10428, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10428_fast_pow_mod_ne_one

def fullRecordGapValue10429 : Nat := fullRecordGapCenterValue + 628856

theorem fullRecordGapTerm10429_eq_value :
    recordGapCenter + 628856 = fullRecordGapValue10429 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10429_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10429 (fullRecordGapValue10429 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10429_not_prime : ¬(recordGapCenter + 628856).Prime := by
  rw [fullRecordGapTerm10429_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10429, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10429_fast_pow_mod_ne_one

def fullRecordGapValue10430 : Nat := fullRecordGapCenterValue + 628916

theorem fullRecordGapTerm10430_eq_value :
    recordGapCenter + 628916 = fullRecordGapValue10430 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10430_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10430 (fullRecordGapValue10430 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10430_not_prime : ¬(recordGapCenter + 628916).Prime := by
  rw [fullRecordGapTerm10430_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10430, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10430_fast_pow_mod_ne_one

def fullRecordGapValue10431 : Nat := fullRecordGapCenterValue + 628982

theorem fullRecordGapTerm10431_eq_value :
    recordGapCenter + 628982 = fullRecordGapValue10431 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10431_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10431 (fullRecordGapValue10431 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10431_not_prime : ¬(recordGapCenter + 628982).Prime := by
  rw [fullRecordGapTerm10431_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10431, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10431_fast_pow_mod_ne_one

def fullRecordGapValue10432 : Nat := fullRecordGapCenterValue + 628988

theorem fullRecordGapTerm10432_eq_value :
    recordGapCenter + 628988 = fullRecordGapValue10432 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10432_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10432 (fullRecordGapValue10432 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10432_not_prime : ¬(recordGapCenter + 628988).Prime := by
  rw [fullRecordGapTerm10432_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10432, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10432_fast_pow_mod_ne_one

def fullRecordGapValue10433 : Nat := fullRecordGapCenterValue + 629106

theorem fullRecordGapTerm10433_eq_value :
    recordGapCenter + 629106 = fullRecordGapValue10433 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10433_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10433 (fullRecordGapValue10433 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10433_not_prime : ¬(recordGapCenter + 629106).Prime := by
  rw [fullRecordGapTerm10433_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10433, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10433_fast_pow_mod_ne_one

def fullRecordGapValue10434 : Nat := fullRecordGapCenterValue + 629192

theorem fullRecordGapTerm10434_eq_value :
    recordGapCenter + 629192 = fullRecordGapValue10434 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10434_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10434 (fullRecordGapValue10434 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10434_not_prime : ¬(recordGapCenter + 629192).Prime := by
  rw [fullRecordGapTerm10434_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10434, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10434_fast_pow_mod_ne_one

def fullRecordGapValue10435 : Nat := fullRecordGapCenterValue + 629228

theorem fullRecordGapTerm10435_eq_value :
    recordGapCenter + 629228 = fullRecordGapValue10435 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10435_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10435 (fullRecordGapValue10435 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10435_not_prime : ¬(recordGapCenter + 629228).Prime := by
  rw [fullRecordGapTerm10435_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10435, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10435_fast_pow_mod_ne_one

def fullRecordGapValue10436 : Nat := fullRecordGapCenterValue + 629246

theorem fullRecordGapTerm10436_eq_value :
    recordGapCenter + 629246 = fullRecordGapValue10436 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10436_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10436 (fullRecordGapValue10436 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10436_not_prime : ¬(recordGapCenter + 629246).Prime := by
  rw [fullRecordGapTerm10436_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10436, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10436_fast_pow_mod_ne_one

def fullRecordGapValue10437 : Nat := fullRecordGapCenterValue + 629270

theorem fullRecordGapTerm10437_eq_value :
    recordGapCenter + 629270 = fullRecordGapValue10437 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10437_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10437 (fullRecordGapValue10437 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10437_not_prime : ¬(recordGapCenter + 629270).Prime := by
  rw [fullRecordGapTerm10437_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10437, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10437_fast_pow_mod_ne_one

def fullRecordGapValue10438 : Nat := fullRecordGapCenterValue + 629282

theorem fullRecordGapTerm10438_eq_value :
    recordGapCenter + 629282 = fullRecordGapValue10438 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10438_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10438 (fullRecordGapValue10438 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10438_not_prime : ¬(recordGapCenter + 629282).Prime := by
  rw [fullRecordGapTerm10438_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10438, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10438_fast_pow_mod_ne_one

def fullRecordGapValue10439 : Nat := fullRecordGapCenterValue + 629342

theorem fullRecordGapTerm10439_eq_value :
    recordGapCenter + 629342 = fullRecordGapValue10439 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10439_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10439 (fullRecordGapValue10439 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10439_not_prime : ¬(recordGapCenter + 629342).Prime := by
  rw [fullRecordGapTerm10439_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10439, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10439_fast_pow_mod_ne_one

def fullRecordGapValue10440 : Nat := fullRecordGapCenterValue + 629346

theorem fullRecordGapTerm10440_eq_value :
    recordGapCenter + 629346 = fullRecordGapValue10440 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10440_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10440 (fullRecordGapValue10440 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10440_not_prime : ¬(recordGapCenter + 629346).Prime := by
  rw [fullRecordGapTerm10440_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10440, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10440_fast_pow_mod_ne_one

def fullRecordGapValue10441 : Nat := fullRecordGapCenterValue + 629426

theorem fullRecordGapTerm10441_eq_value :
    recordGapCenter + 629426 = fullRecordGapValue10441 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10441_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10441 (fullRecordGapValue10441 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10441_not_prime : ¬(recordGapCenter + 629426).Prime := by
  rw [fullRecordGapTerm10441_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10441, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10441_fast_pow_mod_ne_one

def fullRecordGapValue10442 : Nat := fullRecordGapCenterValue + 629436

theorem fullRecordGapTerm10442_eq_value :
    recordGapCenter + 629436 = fullRecordGapValue10442 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10442_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10442 (fullRecordGapValue10442 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10442_not_prime : ¬(recordGapCenter + 629436).Prime := by
  rw [fullRecordGapTerm10442_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10442, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10442_fast_pow_mod_ne_one

def fullRecordGapValue10443 : Nat := fullRecordGapCenterValue + 629522

theorem fullRecordGapTerm10443_eq_value :
    recordGapCenter + 629522 = fullRecordGapValue10443 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10443_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10443 (fullRecordGapValue10443 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10443_not_prime : ¬(recordGapCenter + 629522).Prime := by
  rw [fullRecordGapTerm10443_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10443, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10443_fast_pow_mod_ne_one

def fullRecordGapValue10444 : Nat := fullRecordGapCenterValue + 629528

theorem fullRecordGapTerm10444_eq_value :
    recordGapCenter + 629528 = fullRecordGapValue10444 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10444_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10444 (fullRecordGapValue10444 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10444_not_prime : ¬(recordGapCenter + 629528).Prime := by
  rw [fullRecordGapTerm10444_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10444, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10444_fast_pow_mod_ne_one

def fullRecordGapValue10445 : Nat := fullRecordGapCenterValue + 629598

theorem fullRecordGapTerm10445_eq_value :
    recordGapCenter + 629598 = fullRecordGapValue10445 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10445_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10445 (fullRecordGapValue10445 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10445_not_prime : ¬(recordGapCenter + 629598).Prime := by
  rw [fullRecordGapTerm10445_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10445, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10445_fast_pow_mod_ne_one

def fullRecordGapValue10446 : Nat := fullRecordGapCenterValue + 629708

theorem fullRecordGapTerm10446_eq_value :
    recordGapCenter + 629708 = fullRecordGapValue10446 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10446_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10446 (fullRecordGapValue10446 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10446_not_prime : ¬(recordGapCenter + 629708).Prime := by
  rw [fullRecordGapTerm10446_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10446, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10446_fast_pow_mod_ne_one

def fullRecordGapValue10447 : Nat := fullRecordGapCenterValue + 629732

theorem fullRecordGapTerm10447_eq_value :
    recordGapCenter + 629732 = fullRecordGapValue10447 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10447_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10447 (fullRecordGapValue10447 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10447_not_prime : ¬(recordGapCenter + 629732).Prime := by
  rw [fullRecordGapTerm10447_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10447, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10447_fast_pow_mod_ne_one

def fullRecordGapValue10448 : Nat := fullRecordGapCenterValue + 629826

theorem fullRecordGapTerm10448_eq_value :
    recordGapCenter + 629826 = fullRecordGapValue10448 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10448_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10448 (fullRecordGapValue10448 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10448_not_prime : ¬(recordGapCenter + 629826).Prime := by
  rw [fullRecordGapTerm10448_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10448, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10448_fast_pow_mod_ne_one

def fullRecordGapValue10449 : Nat := fullRecordGapCenterValue + 629828

theorem fullRecordGapTerm10449_eq_value :
    recordGapCenter + 629828 = fullRecordGapValue10449 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10449_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10449 (fullRecordGapValue10449 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10449_not_prime : ¬(recordGapCenter + 629828).Prime := by
  rw [fullRecordGapTerm10449_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10449, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10449_fast_pow_mod_ne_one

def fullRecordGapValue10450 : Nat := fullRecordGapCenterValue + 629868

theorem fullRecordGapTerm10450_eq_value :
    recordGapCenter + 629868 = fullRecordGapValue10450 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10450_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10450 (fullRecordGapValue10450 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10450_not_prime : ¬(recordGapCenter + 629868).Prime := by
  rw [fullRecordGapTerm10450_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10450, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10450_fast_pow_mod_ne_one

def fullRecordGapValue10451 : Nat := fullRecordGapCenterValue + 629870

theorem fullRecordGapTerm10451_eq_value :
    recordGapCenter + 629870 = fullRecordGapValue10451 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10451_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10451 (fullRecordGapValue10451 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10451_not_prime : ¬(recordGapCenter + 629870).Prime := by
  rw [fullRecordGapTerm10451_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10451, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10451_fast_pow_mod_ne_one

def fullRecordGapValue10452 : Nat := fullRecordGapCenterValue + 630138

theorem fullRecordGapTerm10452_eq_value :
    recordGapCenter + 630138 = fullRecordGapValue10452 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10452_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10452 (fullRecordGapValue10452 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10452_not_prime : ¬(recordGapCenter + 630138).Prime := by
  rw [fullRecordGapTerm10452_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10452, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10452_fast_pow_mod_ne_one

def fullRecordGapValue10453 : Nat := fullRecordGapCenterValue + 630182

theorem fullRecordGapTerm10453_eq_value :
    recordGapCenter + 630182 = fullRecordGapValue10453 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10453_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10453 (fullRecordGapValue10453 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10453_not_prime : ¬(recordGapCenter + 630182).Prime := by
  rw [fullRecordGapTerm10453_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10453, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10453_fast_pow_mod_ne_one

def fullRecordGapValue10454 : Nat := fullRecordGapCenterValue + 630248

theorem fullRecordGapTerm10454_eq_value :
    recordGapCenter + 630248 = fullRecordGapValue10454 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10454_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10454 (fullRecordGapValue10454 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10454_not_prime : ¬(recordGapCenter + 630248).Prime := by
  rw [fullRecordGapTerm10454_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10454, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10454_fast_pow_mod_ne_one

def fullRecordGapValue10455 : Nat := fullRecordGapCenterValue + 630290

theorem fullRecordGapTerm10455_eq_value :
    recordGapCenter + 630290 = fullRecordGapValue10455 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10455_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10455 (fullRecordGapValue10455 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10455_not_prime : ¬(recordGapCenter + 630290).Prime := by
  rw [fullRecordGapTerm10455_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10455, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10455_fast_pow_mod_ne_one

def fullRecordGapValue10456 : Nat := fullRecordGapCenterValue + 630492

theorem fullRecordGapTerm10456_eq_value :
    recordGapCenter + 630492 = fullRecordGapValue10456 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10456_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10456 (fullRecordGapValue10456 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10456_not_prime : ¬(recordGapCenter + 630492).Prime := by
  rw [fullRecordGapTerm10456_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10456, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10456_fast_pow_mod_ne_one

def fullRecordGapValue10457 : Nat := fullRecordGapCenterValue + 630548

theorem fullRecordGapTerm10457_eq_value :
    recordGapCenter + 630548 = fullRecordGapValue10457 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10457_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10457 (fullRecordGapValue10457 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10457_not_prime : ¬(recordGapCenter + 630548).Prime := by
  rw [fullRecordGapTerm10457_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10457, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10457_fast_pow_mod_ne_one

def fullRecordGapValue10458 : Nat := fullRecordGapCenterValue + 630668

theorem fullRecordGapTerm10458_eq_value :
    recordGapCenter + 630668 = fullRecordGapValue10458 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10458_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10458 (fullRecordGapValue10458 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10458_not_prime : ¬(recordGapCenter + 630668).Prime := by
  rw [fullRecordGapTerm10458_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10458, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10458_fast_pow_mod_ne_one

def fullRecordGapValue10459 : Nat := fullRecordGapCenterValue + 630698

theorem fullRecordGapTerm10459_eq_value :
    recordGapCenter + 630698 = fullRecordGapValue10459 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10459_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10459 (fullRecordGapValue10459 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10459_not_prime : ¬(recordGapCenter + 630698).Prime := by
  rw [fullRecordGapTerm10459_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10459, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10459_fast_pow_mod_ne_one

def fullRecordGapValue10460 : Nat := fullRecordGapCenterValue + 630716

theorem fullRecordGapTerm10460_eq_value :
    recordGapCenter + 630716 = fullRecordGapValue10460 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10460_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10460 (fullRecordGapValue10460 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10460_not_prime : ¬(recordGapCenter + 630716).Prime := by
  rw [fullRecordGapTerm10460_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10460, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10460_fast_pow_mod_ne_one

def fullRecordGapValue10461 : Nat := fullRecordGapCenterValue + 630822

theorem fullRecordGapTerm10461_eq_value :
    recordGapCenter + 630822 = fullRecordGapValue10461 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10461_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10461 (fullRecordGapValue10461 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10461_not_prime : ¬(recordGapCenter + 630822).Prime := by
  rw [fullRecordGapTerm10461_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10461, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10461_fast_pow_mod_ne_one

def fullRecordGapValue10462 : Nat := fullRecordGapCenterValue + 630842

theorem fullRecordGapTerm10462_eq_value :
    recordGapCenter + 630842 = fullRecordGapValue10462 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10462_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10462 (fullRecordGapValue10462 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10462_not_prime : ¬(recordGapCenter + 630842).Prime := by
  rw [fullRecordGapTerm10462_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10462, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10462_fast_pow_mod_ne_one

def fullRecordGapValue10463 : Nat := fullRecordGapCenterValue + 630852

theorem fullRecordGapTerm10463_eq_value :
    recordGapCenter + 630852 = fullRecordGapValue10463 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10463_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10463 (fullRecordGapValue10463 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10463_not_prime : ¬(recordGapCenter + 630852).Prime := by
  rw [fullRecordGapTerm10463_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10463, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10463_fast_pow_mod_ne_one

def fullRecordGapValue10464 : Nat := fullRecordGapCenterValue + 630858

theorem fullRecordGapTerm10464_eq_value :
    recordGapCenter + 630858 = fullRecordGapValue10464 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10464_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10464 (fullRecordGapValue10464 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10464_not_prime : ¬(recordGapCenter + 630858).Prime := by
  rw [fullRecordGapTerm10464_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10464, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10464_fast_pow_mod_ne_one

def fullRecordGapValue10465 : Nat := fullRecordGapCenterValue + 630932

theorem fullRecordGapTerm10465_eq_value :
    recordGapCenter + 630932 = fullRecordGapValue10465 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10465_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10465 (fullRecordGapValue10465 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10465_not_prime : ¬(recordGapCenter + 630932).Prime := by
  rw [fullRecordGapTerm10465_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10465, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10465_fast_pow_mod_ne_one

def fullRecordGapValue10466 : Nat := fullRecordGapCenterValue + 630948

theorem fullRecordGapTerm10466_eq_value :
    recordGapCenter + 630948 = fullRecordGapValue10466 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10466_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10466 (fullRecordGapValue10466 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10466_not_prime : ¬(recordGapCenter + 630948).Prime := by
  rw [fullRecordGapTerm10466_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10466, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10466_fast_pow_mod_ne_one

def fullRecordGapValue10467 : Nat := fullRecordGapCenterValue + 631038

theorem fullRecordGapTerm10467_eq_value :
    recordGapCenter + 631038 = fullRecordGapValue10467 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10467_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10467 (fullRecordGapValue10467 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10467_not_prime : ¬(recordGapCenter + 631038).Prime := by
  rw [fullRecordGapTerm10467_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10467, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10467_fast_pow_mod_ne_one

def fullRecordGapValue10468 : Nat := fullRecordGapCenterValue + 631076

theorem fullRecordGapTerm10468_eq_value :
    recordGapCenter + 631076 = fullRecordGapValue10468 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10468_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10468 (fullRecordGapValue10468 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10468_not_prime : ¬(recordGapCenter + 631076).Prime := by
  rw [fullRecordGapTerm10468_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10468, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10468_fast_pow_mod_ne_one

def fullRecordGapValue10469 : Nat := fullRecordGapCenterValue + 631130

theorem fullRecordGapTerm10469_eq_value :
    recordGapCenter + 631130 = fullRecordGapValue10469 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10469_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10469 (fullRecordGapValue10469 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10469_not_prime : ¬(recordGapCenter + 631130).Prime := by
  rw [fullRecordGapTerm10469_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10469, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10469_fast_pow_mod_ne_one

def fullRecordGapValue10470 : Nat := fullRecordGapCenterValue + 631172

theorem fullRecordGapTerm10470_eq_value :
    recordGapCenter + 631172 = fullRecordGapValue10470 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10470_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10470 (fullRecordGapValue10470 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10470_not_prime : ¬(recordGapCenter + 631172).Prime := by
  rw [fullRecordGapTerm10470_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10470, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10470_fast_pow_mod_ne_one

def fullRecordGapValue10471 : Nat := fullRecordGapCenterValue + 631178

theorem fullRecordGapTerm10471_eq_value :
    recordGapCenter + 631178 = fullRecordGapValue10471 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10471_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10471 (fullRecordGapValue10471 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10471_not_prime : ¬(recordGapCenter + 631178).Prime := by
  rw [fullRecordGapTerm10471_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10471, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10471_fast_pow_mod_ne_one

def fullRecordGapValue10472 : Nat := fullRecordGapCenterValue + 631208

theorem fullRecordGapTerm10472_eq_value :
    recordGapCenter + 631208 = fullRecordGapValue10472 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10472_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10472 (fullRecordGapValue10472 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10472_not_prime : ¬(recordGapCenter + 631208).Prime := by
  rw [fullRecordGapTerm10472_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10472, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10472_fast_pow_mod_ne_one

def fullRecordGapValue10473 : Nat := fullRecordGapCenterValue + 631310

theorem fullRecordGapTerm10473_eq_value :
    recordGapCenter + 631310 = fullRecordGapValue10473 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10473_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10473 (fullRecordGapValue10473 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10473_not_prime : ¬(recordGapCenter + 631310).Prime := by
  rw [fullRecordGapTerm10473_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10473, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10473_fast_pow_mod_ne_one

def fullRecordGapValue10474 : Nat := fullRecordGapCenterValue + 631362

theorem fullRecordGapTerm10474_eq_value :
    recordGapCenter + 631362 = fullRecordGapValue10474 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10474_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10474 (fullRecordGapValue10474 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10474_not_prime : ¬(recordGapCenter + 631362).Prime := by
  rw [fullRecordGapTerm10474_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10474, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10474_fast_pow_mod_ne_one

def fullRecordGapValue10475 : Nat := fullRecordGapCenterValue + 631478

theorem fullRecordGapTerm10475_eq_value :
    recordGapCenter + 631478 = fullRecordGapValue10475 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10475_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10475 (fullRecordGapValue10475 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10475_not_prime : ¬(recordGapCenter + 631478).Prime := by
  rw [fullRecordGapTerm10475_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10475, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10475_fast_pow_mod_ne_one

def fullRecordGapValue10476 : Nat := fullRecordGapCenterValue + 631508

theorem fullRecordGapTerm10476_eq_value :
    recordGapCenter + 631508 = fullRecordGapValue10476 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10476_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10476 (fullRecordGapValue10476 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10476_not_prime : ¬(recordGapCenter + 631508).Prime := by
  rw [fullRecordGapTerm10476_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10476, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10476_fast_pow_mod_ne_one

def fullRecordGapValue10477 : Nat := fullRecordGapCenterValue + 631662

theorem fullRecordGapTerm10477_eq_value :
    recordGapCenter + 631662 = fullRecordGapValue10477 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10477_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10477 (fullRecordGapValue10477 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10477_not_prime : ¬(recordGapCenter + 631662).Prime := by
  rw [fullRecordGapTerm10477_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10477, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10477_fast_pow_mod_ne_one

def fullRecordGapValue10478 : Nat := fullRecordGapCenterValue + 631668

theorem fullRecordGapTerm10478_eq_value :
    recordGapCenter + 631668 = fullRecordGapValue10478 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10478_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10478 (fullRecordGapValue10478 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10478_not_prime : ¬(recordGapCenter + 631668).Prime := by
  rw [fullRecordGapTerm10478_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10478, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10478_fast_pow_mod_ne_one

def fullRecordGapValue10479 : Nat := fullRecordGapCenterValue + 631778

theorem fullRecordGapTerm10479_eq_value :
    recordGapCenter + 631778 = fullRecordGapValue10479 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10479_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10479 (fullRecordGapValue10479 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10479_not_prime : ¬(recordGapCenter + 631778).Prime := by
  rw [fullRecordGapTerm10479_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10479, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10479_fast_pow_mod_ne_one

def fullRecordGapValue10480 : Nat := fullRecordGapCenterValue + 631832

theorem fullRecordGapTerm10480_eq_value :
    recordGapCenter + 631832 = fullRecordGapValue10480 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10480_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10480 (fullRecordGapValue10480 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10480_not_prime : ¬(recordGapCenter + 631832).Prime := by
  rw [fullRecordGapTerm10480_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10480, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10480_fast_pow_mod_ne_one

def fullRecordGapValue10481 : Nat := fullRecordGapCenterValue + 632006

theorem fullRecordGapTerm10481_eq_value :
    recordGapCenter + 632006 = fullRecordGapValue10481 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10481_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10481 (fullRecordGapValue10481 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10481_not_prime : ¬(recordGapCenter + 632006).Prime := by
  rw [fullRecordGapTerm10481_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10481, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10481_fast_pow_mod_ne_one

def fullRecordGapValue10482 : Nat := fullRecordGapCenterValue + 632046

theorem fullRecordGapTerm10482_eq_value :
    recordGapCenter + 632046 = fullRecordGapValue10482 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10482_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10482 (fullRecordGapValue10482 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10482_not_prime : ¬(recordGapCenter + 632046).Prime := by
  rw [fullRecordGapTerm10482_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10482, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10482_fast_pow_mod_ne_one

def fullRecordGapValue10483 : Nat := fullRecordGapCenterValue + 632292

theorem fullRecordGapTerm10483_eq_value :
    recordGapCenter + 632292 = fullRecordGapValue10483 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10483_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10483 (fullRecordGapValue10483 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10483_not_prime : ¬(recordGapCenter + 632292).Prime := by
  rw [fullRecordGapTerm10483_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10483, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10483_fast_pow_mod_ne_one

def fullRecordGapValue10484 : Nat := fullRecordGapCenterValue + 632486

theorem fullRecordGapTerm10484_eq_value :
    recordGapCenter + 632486 = fullRecordGapValue10484 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10484_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10484 (fullRecordGapValue10484 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10484_not_prime : ¬(recordGapCenter + 632486).Prime := by
  rw [fullRecordGapTerm10484_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10484, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10484_fast_pow_mod_ne_one

def fullRecordGapValue10485 : Nat := fullRecordGapCenterValue + 632508

theorem fullRecordGapTerm10485_eq_value :
    recordGapCenter + 632508 = fullRecordGapValue10485 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10485_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10485 (fullRecordGapValue10485 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10485_not_prime : ¬(recordGapCenter + 632508).Prime := by
  rw [fullRecordGapTerm10485_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10485, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10485_fast_pow_mod_ne_one

def fullRecordGapValue10486 : Nat := fullRecordGapCenterValue + 632532

theorem fullRecordGapTerm10486_eq_value :
    recordGapCenter + 632532 = fullRecordGapValue10486 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10486_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10486 (fullRecordGapValue10486 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10486_not_prime : ¬(recordGapCenter + 632532).Prime := by
  rw [fullRecordGapTerm10486_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10486, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10486_fast_pow_mod_ne_one

def fullRecordGapValue10487 : Nat := fullRecordGapCenterValue + 632642

theorem fullRecordGapTerm10487_eq_value :
    recordGapCenter + 632642 = fullRecordGapValue10487 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10487_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10487 (fullRecordGapValue10487 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10487_not_prime : ¬(recordGapCenter + 632642).Prime := by
  rw [fullRecordGapTerm10487_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10487, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10487_fast_pow_mod_ne_one

def fullRecordGapValue10488 : Nat := fullRecordGapCenterValue + 632846

theorem fullRecordGapTerm10488_eq_value :
    recordGapCenter + 632846 = fullRecordGapValue10488 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10488_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10488 (fullRecordGapValue10488 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10488_not_prime : ¬(recordGapCenter + 632846).Prime := by
  rw [fullRecordGapTerm10488_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10488, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10488_fast_pow_mod_ne_one

def fullRecordGapValue10489 : Nat := fullRecordGapCenterValue + 632906

theorem fullRecordGapTerm10489_eq_value :
    recordGapCenter + 632906 = fullRecordGapValue10489 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10489_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10489 (fullRecordGapValue10489 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10489_not_prime : ¬(recordGapCenter + 632906).Prime := by
  rw [fullRecordGapTerm10489_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10489, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10489_fast_pow_mod_ne_one

def fullRecordGapValue10490 : Nat := fullRecordGapCenterValue + 633102

theorem fullRecordGapTerm10490_eq_value :
    recordGapCenter + 633102 = fullRecordGapValue10490 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10490_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10490 (fullRecordGapValue10490 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10490_not_prime : ¬(recordGapCenter + 633102).Prime := by
  rw [fullRecordGapTerm10490_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10490, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10490_fast_pow_mod_ne_one

def fullRecordGapValue10491 : Nat := fullRecordGapCenterValue + 633110

theorem fullRecordGapTerm10491_eq_value :
    recordGapCenter + 633110 = fullRecordGapValue10491 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10491_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10491 (fullRecordGapValue10491 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10491_not_prime : ¬(recordGapCenter + 633110).Prime := by
  rw [fullRecordGapTerm10491_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10491, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10491_fast_pow_mod_ne_one

def fullRecordGapValue10492 : Nat := fullRecordGapCenterValue + 633242

theorem fullRecordGapTerm10492_eq_value :
    recordGapCenter + 633242 = fullRecordGapValue10492 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10492_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10492 (fullRecordGapValue10492 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10492_not_prime : ¬(recordGapCenter + 633242).Prime := by
  rw [fullRecordGapTerm10492_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10492, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10492_fast_pow_mod_ne_one

def fullRecordGapValue10493 : Nat := fullRecordGapCenterValue + 633246

theorem fullRecordGapTerm10493_eq_value :
    recordGapCenter + 633246 = fullRecordGapValue10493 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10493_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10493 (fullRecordGapValue10493 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10493_not_prime : ¬(recordGapCenter + 633246).Prime := by
  rw [fullRecordGapTerm10493_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10493, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10493_fast_pow_mod_ne_one

def fullRecordGapValue10494 : Nat := fullRecordGapCenterValue + 633272

theorem fullRecordGapTerm10494_eq_value :
    recordGapCenter + 633272 = fullRecordGapValue10494 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10494_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10494 (fullRecordGapValue10494 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10494_not_prime : ¬(recordGapCenter + 633272).Prime := by
  rw [fullRecordGapTerm10494_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10494, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10494_fast_pow_mod_ne_one

def fullRecordGapValue10495 : Nat := fullRecordGapCenterValue + 633326

theorem fullRecordGapTerm10495_eq_value :
    recordGapCenter + 633326 = fullRecordGapValue10495 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10495_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10495 (fullRecordGapValue10495 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10495_not_prime : ¬(recordGapCenter + 633326).Prime := by
  rw [fullRecordGapTerm10495_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10495, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10495_fast_pow_mod_ne_one

def fullRecordGapValue10496 : Nat := fullRecordGapCenterValue + 633458

theorem fullRecordGapTerm10496_eq_value :
    recordGapCenter + 633458 = fullRecordGapValue10496 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10496_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10496 (fullRecordGapValue10496 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10496_not_prime : ¬(recordGapCenter + 633458).Prime := by
  rw [fullRecordGapTerm10496_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10496, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10496_fast_pow_mod_ne_one

end PrimeFactorUnimodality
