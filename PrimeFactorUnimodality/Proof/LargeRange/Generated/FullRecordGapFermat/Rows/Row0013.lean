import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue03073 : Nat := fullRecordGapCenterValue - 173002

theorem fullRecordGapTerm03073_eq_value :
    recordGapCenter - 173002 = fullRecordGapValue03073 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03073_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03073 (fullRecordGapValue03073 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03073_not_prime : ¬(recordGapCenter - 173002).Prime := by
  rw [fullRecordGapTerm03073_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03073, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03073_fast_pow_mod_ne_one

def fullRecordGapValue03074 : Nat := fullRecordGapCenterValue - 172828

theorem fullRecordGapTerm03074_eq_value :
    recordGapCenter - 172828 = fullRecordGapValue03074 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03074_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03074 (fullRecordGapValue03074 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03074_not_prime : ¬(recordGapCenter - 172828).Prime := by
  rw [fullRecordGapTerm03074_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03074, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03074_fast_pow_mod_ne_one

def fullRecordGapValue03075 : Nat := fullRecordGapCenterValue - 172804

theorem fullRecordGapTerm03075_eq_value :
    recordGapCenter - 172804 = fullRecordGapValue03075 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03075_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03075 (fullRecordGapValue03075 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03075_not_prime : ¬(recordGapCenter - 172804).Prime := by
  rw [fullRecordGapTerm03075_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03075, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03075_fast_pow_mod_ne_one

def fullRecordGapValue03076 : Nat := fullRecordGapCenterValue - 172762

theorem fullRecordGapTerm03076_eq_value :
    recordGapCenter - 172762 = fullRecordGapValue03076 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03076_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03076 (fullRecordGapValue03076 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03076_not_prime : ¬(recordGapCenter - 172762).Prime := by
  rw [fullRecordGapTerm03076_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03076, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03076_fast_pow_mod_ne_one

def fullRecordGapValue03077 : Nat := fullRecordGapCenterValue - 172714

theorem fullRecordGapTerm03077_eq_value :
    recordGapCenter - 172714 = fullRecordGapValue03077 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03077_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03077 (fullRecordGapValue03077 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03077_not_prime : ¬(recordGapCenter - 172714).Prime := by
  rw [fullRecordGapTerm03077_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03077, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03077_fast_pow_mod_ne_one

def fullRecordGapValue03078 : Nat := fullRecordGapCenterValue - 172498

theorem fullRecordGapTerm03078_eq_value :
    recordGapCenter - 172498 = fullRecordGapValue03078 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03078_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03078 (fullRecordGapValue03078 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03078_not_prime : ¬(recordGapCenter - 172498).Prime := by
  rw [fullRecordGapTerm03078_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03078, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03078_fast_pow_mod_ne_one

def fullRecordGapValue03079 : Nat := fullRecordGapCenterValue - 172402

theorem fullRecordGapTerm03079_eq_value :
    recordGapCenter - 172402 = fullRecordGapValue03079 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03079_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03079 (fullRecordGapValue03079 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03079_not_prime : ¬(recordGapCenter - 172402).Prime := by
  rw [fullRecordGapTerm03079_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03079, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03079_fast_pow_mod_ne_one

def fullRecordGapValue03080 : Nat := fullRecordGapCenterValue - 171982

theorem fullRecordGapTerm03080_eq_value :
    recordGapCenter - 171982 = fullRecordGapValue03080 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03080_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03080 (fullRecordGapValue03080 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03080_not_prime : ¬(recordGapCenter - 171982).Prime := by
  rw [fullRecordGapTerm03080_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03080, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03080_fast_pow_mod_ne_one

def fullRecordGapValue03081 : Nat := fullRecordGapCenterValue - 171694

theorem fullRecordGapTerm03081_eq_value :
    recordGapCenter - 171694 = fullRecordGapValue03081 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03081_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03081 (fullRecordGapValue03081 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03081_not_prime : ¬(recordGapCenter - 171694).Prime := by
  rw [fullRecordGapTerm03081_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03081, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03081_fast_pow_mod_ne_one

def fullRecordGapValue03082 : Nat := fullRecordGapCenterValue - 171562

theorem fullRecordGapTerm03082_eq_value :
    recordGapCenter - 171562 = fullRecordGapValue03082 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03082_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03082 (fullRecordGapValue03082 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03082_not_prime : ¬(recordGapCenter - 171562).Prime := by
  rw [fullRecordGapTerm03082_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03082, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03082_fast_pow_mod_ne_one

def fullRecordGapValue03083 : Nat := fullRecordGapCenterValue - 171502

theorem fullRecordGapTerm03083_eq_value :
    recordGapCenter - 171502 = fullRecordGapValue03083 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03083_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03083 (fullRecordGapValue03083 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03083_not_prime : ¬(recordGapCenter - 171502).Prime := by
  rw [fullRecordGapTerm03083_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03083, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03083_fast_pow_mod_ne_one

def fullRecordGapValue03084 : Nat := fullRecordGapCenterValue - 171334

theorem fullRecordGapTerm03084_eq_value :
    recordGapCenter - 171334 = fullRecordGapValue03084 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03084_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03084 (fullRecordGapValue03084 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03084_not_prime : ¬(recordGapCenter - 171334).Prime := by
  rw [fullRecordGapTerm03084_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03084, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03084_fast_pow_mod_ne_one

def fullRecordGapValue03085 : Nat := fullRecordGapCenterValue - 171238

theorem fullRecordGapTerm03085_eq_value :
    recordGapCenter - 171238 = fullRecordGapValue03085 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03085_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03085 (fullRecordGapValue03085 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03085_not_prime : ¬(recordGapCenter - 171238).Prime := by
  rw [fullRecordGapTerm03085_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03085, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03085_fast_pow_mod_ne_one

def fullRecordGapValue03086 : Nat := fullRecordGapCenterValue - 171154

theorem fullRecordGapTerm03086_eq_value :
    recordGapCenter - 171154 = fullRecordGapValue03086 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03086_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03086 (fullRecordGapValue03086 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03086_not_prime : ¬(recordGapCenter - 171154).Prime := by
  rw [fullRecordGapTerm03086_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03086, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03086_fast_pow_mod_ne_one

def fullRecordGapValue03087 : Nat := fullRecordGapCenterValue - 171034

theorem fullRecordGapTerm03087_eq_value :
    recordGapCenter - 171034 = fullRecordGapValue03087 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03087_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03087 (fullRecordGapValue03087 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03087_not_prime : ¬(recordGapCenter - 171034).Prime := by
  rw [fullRecordGapTerm03087_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03087, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03087_fast_pow_mod_ne_one

def fullRecordGapValue03088 : Nat := fullRecordGapCenterValue - 170902

theorem fullRecordGapTerm03088_eq_value :
    recordGapCenter - 170902 = fullRecordGapValue03088 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03088_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03088 (fullRecordGapValue03088 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03088_not_prime : ¬(recordGapCenter - 170902).Prime := by
  rw [fullRecordGapTerm03088_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03088, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03088_fast_pow_mod_ne_one

def fullRecordGapValue03089 : Nat := fullRecordGapCenterValue - 170854

theorem fullRecordGapTerm03089_eq_value :
    recordGapCenter - 170854 = fullRecordGapValue03089 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03089_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03089 (fullRecordGapValue03089 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03089_not_prime : ¬(recordGapCenter - 170854).Prime := by
  rw [fullRecordGapTerm03089_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03089, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03089_fast_pow_mod_ne_one

def fullRecordGapValue03090 : Nat := fullRecordGapCenterValue - 170518

theorem fullRecordGapTerm03090_eq_value :
    recordGapCenter - 170518 = fullRecordGapValue03090 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03090_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03090 (fullRecordGapValue03090 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03090_not_prime : ¬(recordGapCenter - 170518).Prime := by
  rw [fullRecordGapTerm03090_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03090, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03090_fast_pow_mod_ne_one

def fullRecordGapValue03091 : Nat := fullRecordGapCenterValue - 170494

theorem fullRecordGapTerm03091_eq_value :
    recordGapCenter - 170494 = fullRecordGapValue03091 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03091_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03091 (fullRecordGapValue03091 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03091_not_prime : ¬(recordGapCenter - 170494).Prime := by
  rw [fullRecordGapTerm03091_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03091, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03091_fast_pow_mod_ne_one

def fullRecordGapValue03092 : Nat := fullRecordGapCenterValue - 170182

theorem fullRecordGapTerm03092_eq_value :
    recordGapCenter - 170182 = fullRecordGapValue03092 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03092_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03092 (fullRecordGapValue03092 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03092_not_prime : ¬(recordGapCenter - 170182).Prime := by
  rw [fullRecordGapTerm03092_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03092, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03092_fast_pow_mod_ne_one

def fullRecordGapValue03093 : Nat := fullRecordGapCenterValue - 170100

theorem fullRecordGapTerm03093_eq_value :
    recordGapCenter - 170100 = fullRecordGapValue03093 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03093_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03093 (fullRecordGapValue03093 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03093_not_prime : ¬(recordGapCenter - 170100).Prime := by
  rw [fullRecordGapTerm03093_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03093, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03093_fast_pow_mod_ne_one

def fullRecordGapValue03094 : Nat := fullRecordGapCenterValue - 169894

theorem fullRecordGapTerm03094_eq_value :
    recordGapCenter - 169894 = fullRecordGapValue03094 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03094_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03094 (fullRecordGapValue03094 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03094_not_prime : ¬(recordGapCenter - 169894).Prime := by
  rw [fullRecordGapTerm03094_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03094, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03094_fast_pow_mod_ne_one

def fullRecordGapValue03095 : Nat := fullRecordGapCenterValue - 169738

theorem fullRecordGapTerm03095_eq_value :
    recordGapCenter - 169738 = fullRecordGapValue03095 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03095_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03095 (fullRecordGapValue03095 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03095_not_prime : ¬(recordGapCenter - 169738).Prime := by
  rw [fullRecordGapTerm03095_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03095, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03095_fast_pow_mod_ne_one

def fullRecordGapValue03096 : Nat := fullRecordGapCenterValue - 169654

theorem fullRecordGapTerm03096_eq_value :
    recordGapCenter - 169654 = fullRecordGapValue03096 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03096_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03096 (fullRecordGapValue03096 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03096_not_prime : ¬(recordGapCenter - 169654).Prime := by
  rw [fullRecordGapTerm03096_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03096, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03096_fast_pow_mod_ne_one

def fullRecordGapValue03097 : Nat := fullRecordGapCenterValue - 169522

theorem fullRecordGapTerm03097_eq_value :
    recordGapCenter - 169522 = fullRecordGapValue03097 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03097_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03097 (fullRecordGapValue03097 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03097_not_prime : ¬(recordGapCenter - 169522).Prime := by
  rw [fullRecordGapTerm03097_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03097, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03097_fast_pow_mod_ne_one

def fullRecordGapValue03098 : Nat := fullRecordGapCenterValue - 169402

theorem fullRecordGapTerm03098_eq_value :
    recordGapCenter - 169402 = fullRecordGapValue03098 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03098_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03098 (fullRecordGapValue03098 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03098_not_prime : ¬(recordGapCenter - 169402).Prime := by
  rw [fullRecordGapTerm03098_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03098, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03098_fast_pow_mod_ne_one

def fullRecordGapValue03099 : Nat := fullRecordGapCenterValue - 169258

theorem fullRecordGapTerm03099_eq_value :
    recordGapCenter - 169258 = fullRecordGapValue03099 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03099_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03099 (fullRecordGapValue03099 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03099_not_prime : ¬(recordGapCenter - 169258).Prime := by
  rw [fullRecordGapTerm03099_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03099, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03099_fast_pow_mod_ne_one

def fullRecordGapValue03100 : Nat := fullRecordGapCenterValue - 169102

theorem fullRecordGapTerm03100_eq_value :
    recordGapCenter - 169102 = fullRecordGapValue03100 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03100_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03100 (fullRecordGapValue03100 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03100_not_prime : ¬(recordGapCenter - 169102).Prime := by
  rw [fullRecordGapTerm03100_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03100, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03100_fast_pow_mod_ne_one

def fullRecordGapValue03101 : Nat := fullRecordGapCenterValue - 169018

theorem fullRecordGapTerm03101_eq_value :
    recordGapCenter - 169018 = fullRecordGapValue03101 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03101_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03101 (fullRecordGapValue03101 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03101_not_prime : ¬(recordGapCenter - 169018).Prime := by
  rw [fullRecordGapTerm03101_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03101, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03101_fast_pow_mod_ne_one

def fullRecordGapValue03102 : Nat := fullRecordGapCenterValue - 168934

theorem fullRecordGapTerm03102_eq_value :
    recordGapCenter - 168934 = fullRecordGapValue03102 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03102_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03102 (fullRecordGapValue03102 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03102_not_prime : ¬(recordGapCenter - 168934).Prime := by
  rw [fullRecordGapTerm03102_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03102, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03102_fast_pow_mod_ne_one

def fullRecordGapValue03103 : Nat := fullRecordGapCenterValue - 168802

theorem fullRecordGapTerm03103_eq_value :
    recordGapCenter - 168802 = fullRecordGapValue03103 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03103_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03103 (fullRecordGapValue03103 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03103_not_prime : ¬(recordGapCenter - 168802).Prime := by
  rw [fullRecordGapTerm03103_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03103, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03103_fast_pow_mod_ne_one

def fullRecordGapValue03104 : Nat := fullRecordGapCenterValue - 168754

theorem fullRecordGapTerm03104_eq_value :
    recordGapCenter - 168754 = fullRecordGapValue03104 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03104_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03104 (fullRecordGapValue03104 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03104_not_prime : ¬(recordGapCenter - 168754).Prime := by
  rw [fullRecordGapTerm03104_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03104, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03104_fast_pow_mod_ne_one

def fullRecordGapValue03105 : Nat := fullRecordGapCenterValue - 168598

theorem fullRecordGapTerm03105_eq_value :
    recordGapCenter - 168598 = fullRecordGapValue03105 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03105_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03105 (fullRecordGapValue03105 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03105_not_prime : ¬(recordGapCenter - 168598).Prime := by
  rw [fullRecordGapTerm03105_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03105, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03105_fast_pow_mod_ne_one

def fullRecordGapValue03106 : Nat := fullRecordGapCenterValue - 168094

theorem fullRecordGapTerm03106_eq_value :
    recordGapCenter - 168094 = fullRecordGapValue03106 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03106_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03106 (fullRecordGapValue03106 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03106_not_prime : ¬(recordGapCenter - 168094).Prime := by
  rw [fullRecordGapTerm03106_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03106, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03106_fast_pow_mod_ne_one

def fullRecordGapValue03107 : Nat := fullRecordGapCenterValue - 168034

theorem fullRecordGapTerm03107_eq_value :
    recordGapCenter - 168034 = fullRecordGapValue03107 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03107_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03107 (fullRecordGapValue03107 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03107_not_prime : ¬(recordGapCenter - 168034).Prime := by
  rw [fullRecordGapTerm03107_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03107, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03107_fast_pow_mod_ne_one

def fullRecordGapValue03108 : Nat := fullRecordGapCenterValue - 167554

theorem fullRecordGapTerm03108_eq_value :
    recordGapCenter - 167554 = fullRecordGapValue03108 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03108_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03108 (fullRecordGapValue03108 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03108_not_prime : ¬(recordGapCenter - 167554).Prime := by
  rw [fullRecordGapTerm03108_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03108, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03108_fast_pow_mod_ne_one

def fullRecordGapValue03109 : Nat := fullRecordGapCenterValue - 167242

theorem fullRecordGapTerm03109_eq_value :
    recordGapCenter - 167242 = fullRecordGapValue03109 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03109_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03109 (fullRecordGapValue03109 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03109_not_prime : ¬(recordGapCenter - 167242).Prime := by
  rw [fullRecordGapTerm03109_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03109, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03109_fast_pow_mod_ne_one

def fullRecordGapValue03110 : Nat := fullRecordGapCenterValue - 167158

theorem fullRecordGapTerm03110_eq_value :
    recordGapCenter - 167158 = fullRecordGapValue03110 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03110_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03110 (fullRecordGapValue03110 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03110_not_prime : ¬(recordGapCenter - 167158).Prime := by
  rw [fullRecordGapTerm03110_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03110, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03110_fast_pow_mod_ne_one

def fullRecordGapValue03111 : Nat := fullRecordGapCenterValue - 167122

theorem fullRecordGapTerm03111_eq_value :
    recordGapCenter - 167122 = fullRecordGapValue03111 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03111_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03111 (fullRecordGapValue03111 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03111_not_prime : ¬(recordGapCenter - 167122).Prime := by
  rw [fullRecordGapTerm03111_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03111, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03111_fast_pow_mod_ne_one

def fullRecordGapValue03112 : Nat := fullRecordGapCenterValue - 166942

theorem fullRecordGapTerm03112_eq_value :
    recordGapCenter - 166942 = fullRecordGapValue03112 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03112_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03112 (fullRecordGapValue03112 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03112_not_prime : ¬(recordGapCenter - 166942).Prime := by
  rw [fullRecordGapTerm03112_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03112, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03112_fast_pow_mod_ne_one

def fullRecordGapValue03113 : Nat := fullRecordGapCenterValue - 166798

theorem fullRecordGapTerm03113_eq_value :
    recordGapCenter - 166798 = fullRecordGapValue03113 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03113_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03113 (fullRecordGapValue03113 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03113_not_prime : ¬(recordGapCenter - 166798).Prime := by
  rw [fullRecordGapTerm03113_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03113, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03113_fast_pow_mod_ne_one

def fullRecordGapValue03114 : Nat := fullRecordGapCenterValue - 166714

theorem fullRecordGapTerm03114_eq_value :
    recordGapCenter - 166714 = fullRecordGapValue03114 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03114_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03114 (fullRecordGapValue03114 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03114_not_prime : ¬(recordGapCenter - 166714).Prime := by
  rw [fullRecordGapTerm03114_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03114, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03114_fast_pow_mod_ne_one

def fullRecordGapValue03115 : Nat := fullRecordGapCenterValue - 166534

theorem fullRecordGapTerm03115_eq_value :
    recordGapCenter - 166534 = fullRecordGapValue03115 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03115_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03115 (fullRecordGapValue03115 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03115_not_prime : ¬(recordGapCenter - 166534).Prime := by
  rw [fullRecordGapTerm03115_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03115, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03115_fast_pow_mod_ne_one

def fullRecordGapValue03116 : Nat := fullRecordGapCenterValue - 166462

theorem fullRecordGapTerm03116_eq_value :
    recordGapCenter - 166462 = fullRecordGapValue03116 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03116_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03116 (fullRecordGapValue03116 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03116_not_prime : ¬(recordGapCenter - 166462).Prime := by
  rw [fullRecordGapTerm03116_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03116, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03116_fast_pow_mod_ne_one

def fullRecordGapValue03117 : Nat := fullRecordGapCenterValue - 166012

theorem fullRecordGapTerm03117_eq_value :
    recordGapCenter - 166012 = fullRecordGapValue03117 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03117_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03117 (fullRecordGapValue03117 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03117_not_prime : ¬(recordGapCenter - 166012).Prime := by
  rw [fullRecordGapTerm03117_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03117, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03117_fast_pow_mod_ne_one

def fullRecordGapValue03118 : Nat := fullRecordGapCenterValue - 165778

theorem fullRecordGapTerm03118_eq_value :
    recordGapCenter - 165778 = fullRecordGapValue03118 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03118_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03118 (fullRecordGapValue03118 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03118_not_prime : ¬(recordGapCenter - 165778).Prime := by
  rw [fullRecordGapTerm03118_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03118, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03118_fast_pow_mod_ne_one

def fullRecordGapValue03119 : Nat := fullRecordGapCenterValue - 165622

theorem fullRecordGapTerm03119_eq_value :
    recordGapCenter - 165622 = fullRecordGapValue03119 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03119_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03119 (fullRecordGapValue03119 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03119_not_prime : ¬(recordGapCenter - 165622).Prime := by
  rw [fullRecordGapTerm03119_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03119, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03119_fast_pow_mod_ne_one

def fullRecordGapValue03120 : Nat := fullRecordGapCenterValue - 165562

theorem fullRecordGapTerm03120_eq_value :
    recordGapCenter - 165562 = fullRecordGapValue03120 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03120_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03120 (fullRecordGapValue03120 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03120_not_prime : ¬(recordGapCenter - 165562).Prime := by
  rw [fullRecordGapTerm03120_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03120, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03120_fast_pow_mod_ne_one

def fullRecordGapValue03121 : Nat := fullRecordGapCenterValue - 165442

theorem fullRecordGapTerm03121_eq_value :
    recordGapCenter - 165442 = fullRecordGapValue03121 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03121_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03121 (fullRecordGapValue03121 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03121_not_prime : ¬(recordGapCenter - 165442).Prime := by
  rw [fullRecordGapTerm03121_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03121, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03121_fast_pow_mod_ne_one

def fullRecordGapValue03122 : Nat := fullRecordGapCenterValue - 165238

theorem fullRecordGapTerm03122_eq_value :
    recordGapCenter - 165238 = fullRecordGapValue03122 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03122_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03122 (fullRecordGapValue03122 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03122_not_prime : ¬(recordGapCenter - 165238).Prime := by
  rw [fullRecordGapTerm03122_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03122, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03122_fast_pow_mod_ne_one

def fullRecordGapValue03123 : Nat := fullRecordGapCenterValue - 165058

theorem fullRecordGapTerm03123_eq_value :
    recordGapCenter - 165058 = fullRecordGapValue03123 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03123_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03123 (fullRecordGapValue03123 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03123_not_prime : ¬(recordGapCenter - 165058).Prime := by
  rw [fullRecordGapTerm03123_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03123, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03123_fast_pow_mod_ne_one

def fullRecordGapValue03124 : Nat := fullRecordGapCenterValue - 164698

theorem fullRecordGapTerm03124_eq_value :
    recordGapCenter - 164698 = fullRecordGapValue03124 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03124_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03124 (fullRecordGapValue03124 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03124_not_prime : ¬(recordGapCenter - 164698).Prime := by
  rw [fullRecordGapTerm03124_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03124, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03124_fast_pow_mod_ne_one

def fullRecordGapValue03125 : Nat := fullRecordGapCenterValue - 164482

theorem fullRecordGapTerm03125_eq_value :
    recordGapCenter - 164482 = fullRecordGapValue03125 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03125_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03125 (fullRecordGapValue03125 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03125_not_prime : ¬(recordGapCenter - 164482).Prime := by
  rw [fullRecordGapTerm03125_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03125, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03125_fast_pow_mod_ne_one

def fullRecordGapValue03126 : Nat := fullRecordGapCenterValue - 164434

theorem fullRecordGapTerm03126_eq_value :
    recordGapCenter - 164434 = fullRecordGapValue03126 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03126_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03126 (fullRecordGapValue03126 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03126_not_prime : ¬(recordGapCenter - 164434).Prime := by
  rw [fullRecordGapTerm03126_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03126, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03126_fast_pow_mod_ne_one

def fullRecordGapValue03127 : Nat := fullRecordGapCenterValue - 164062

theorem fullRecordGapTerm03127_eq_value :
    recordGapCenter - 164062 = fullRecordGapValue03127 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03127_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03127 (fullRecordGapValue03127 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03127_not_prime : ¬(recordGapCenter - 164062).Prime := by
  rw [fullRecordGapTerm03127_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03127, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03127_fast_pow_mod_ne_one

def fullRecordGapValue03128 : Nat := fullRecordGapCenterValue - 163942

theorem fullRecordGapTerm03128_eq_value :
    recordGapCenter - 163942 = fullRecordGapValue03128 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03128_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03128 (fullRecordGapValue03128 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03128_not_prime : ¬(recordGapCenter - 163942).Prime := by
  rw [fullRecordGapTerm03128_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03128, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03128_fast_pow_mod_ne_one

def fullRecordGapValue03129 : Nat := fullRecordGapCenterValue - 163840

theorem fullRecordGapTerm03129_eq_value :
    recordGapCenter - 163840 = fullRecordGapValue03129 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03129_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03129 (fullRecordGapValue03129 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03129_not_prime : ¬(recordGapCenter - 163840).Prime := by
  rw [fullRecordGapTerm03129_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03129, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03129_fast_pow_mod_ne_one

def fullRecordGapValue03130 : Nat := fullRecordGapCenterValue - 163678

theorem fullRecordGapTerm03130_eq_value :
    recordGapCenter - 163678 = fullRecordGapValue03130 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03130_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03130 (fullRecordGapValue03130 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03130_not_prime : ¬(recordGapCenter - 163678).Prime := by
  rw [fullRecordGapTerm03130_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03130, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03130_fast_pow_mod_ne_one

def fullRecordGapValue03131 : Nat := fullRecordGapCenterValue - 163522

theorem fullRecordGapTerm03131_eq_value :
    recordGapCenter - 163522 = fullRecordGapValue03131 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03131_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03131 (fullRecordGapValue03131 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03131_not_prime : ¬(recordGapCenter - 163522).Prime := by
  rw [fullRecordGapTerm03131_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03131, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03131_fast_pow_mod_ne_one

def fullRecordGapValue03132 : Nat := fullRecordGapCenterValue - 163414

theorem fullRecordGapTerm03132_eq_value :
    recordGapCenter - 163414 = fullRecordGapValue03132 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03132_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03132 (fullRecordGapValue03132 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03132_not_prime : ¬(recordGapCenter - 163414).Prime := by
  rw [fullRecordGapTerm03132_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03132, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03132_fast_pow_mod_ne_one

def fullRecordGapValue03133 : Nat := fullRecordGapCenterValue - 163342

theorem fullRecordGapTerm03133_eq_value :
    recordGapCenter - 163342 = fullRecordGapValue03133 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03133_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03133 (fullRecordGapValue03133 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03133_not_prime : ¬(recordGapCenter - 163342).Prime := by
  rw [fullRecordGapTerm03133_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03133, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03133_fast_pow_mod_ne_one

def fullRecordGapValue03134 : Nat := fullRecordGapCenterValue - 163294

theorem fullRecordGapTerm03134_eq_value :
    recordGapCenter - 163294 = fullRecordGapValue03134 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03134_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03134 (fullRecordGapValue03134 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03134_not_prime : ¬(recordGapCenter - 163294).Prime := by
  rw [fullRecordGapTerm03134_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03134, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03134_fast_pow_mod_ne_one

def fullRecordGapValue03135 : Nat := fullRecordGapCenterValue - 163258

theorem fullRecordGapTerm03135_eq_value :
    recordGapCenter - 163258 = fullRecordGapValue03135 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03135_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03135 (fullRecordGapValue03135 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03135_not_prime : ¬(recordGapCenter - 163258).Prime := by
  rw [fullRecordGapTerm03135_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03135, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03135_fast_pow_mod_ne_one

def fullRecordGapValue03136 : Nat := fullRecordGapCenterValue - 163138

theorem fullRecordGapTerm03136_eq_value :
    recordGapCenter - 163138 = fullRecordGapValue03136 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03136_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03136 (fullRecordGapValue03136 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03136_not_prime : ¬(recordGapCenter - 163138).Prime := by
  rw [fullRecordGapTerm03136_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03136, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03136_fast_pow_mod_ne_one

def fullRecordGapValue03137 : Nat := fullRecordGapCenterValue - 163054

theorem fullRecordGapTerm03137_eq_value :
    recordGapCenter - 163054 = fullRecordGapValue03137 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03137_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03137 (fullRecordGapValue03137 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03137_not_prime : ¬(recordGapCenter - 163054).Prime := by
  rw [fullRecordGapTerm03137_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03137, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03137_fast_pow_mod_ne_one

def fullRecordGapValue03138 : Nat := fullRecordGapCenterValue - 162802

theorem fullRecordGapTerm03138_eq_value :
    recordGapCenter - 162802 = fullRecordGapValue03138 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03138_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03138 (fullRecordGapValue03138 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03138_not_prime : ¬(recordGapCenter - 162802).Prime := by
  rw [fullRecordGapTerm03138_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03138, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03138_fast_pow_mod_ne_one

def fullRecordGapValue03139 : Nat := fullRecordGapCenterValue - 162742

theorem fullRecordGapTerm03139_eq_value :
    recordGapCenter - 162742 = fullRecordGapValue03139 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03139_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03139 (fullRecordGapValue03139 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03139_not_prime : ¬(recordGapCenter - 162742).Prime := by
  rw [fullRecordGapTerm03139_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03139, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03139_fast_pow_mod_ne_one

def fullRecordGapValue03140 : Nat := fullRecordGapCenterValue - 162718

theorem fullRecordGapTerm03140_eq_value :
    recordGapCenter - 162718 = fullRecordGapValue03140 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03140_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03140 (fullRecordGapValue03140 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03140_not_prime : ¬(recordGapCenter - 162718).Prime := by
  rw [fullRecordGapTerm03140_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03140, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03140_fast_pow_mod_ne_one

def fullRecordGapValue03141 : Nat := fullRecordGapCenterValue - 162154

theorem fullRecordGapTerm03141_eq_value :
    recordGapCenter - 162154 = fullRecordGapValue03141 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03141_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03141 (fullRecordGapValue03141 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03141_not_prime : ¬(recordGapCenter - 162154).Prime := by
  rw [fullRecordGapTerm03141_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03141, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03141_fast_pow_mod_ne_one

def fullRecordGapValue03142 : Nat := fullRecordGapCenterValue - 162094

theorem fullRecordGapTerm03142_eq_value :
    recordGapCenter - 162094 = fullRecordGapValue03142 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03142_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03142 (fullRecordGapValue03142 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03142_not_prime : ¬(recordGapCenter - 162094).Prime := by
  rw [fullRecordGapTerm03142_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03142, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03142_fast_pow_mod_ne_one

def fullRecordGapValue03143 : Nat := fullRecordGapCenterValue - 162000

theorem fullRecordGapTerm03143_eq_value :
    recordGapCenter - 162000 = fullRecordGapValue03143 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03143_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03143 (fullRecordGapValue03143 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03143_not_prime : ¬(recordGapCenter - 162000).Prime := by
  rw [fullRecordGapTerm03143_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03143, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03143_fast_pow_mod_ne_one

def fullRecordGapValue03144 : Nat := fullRecordGapCenterValue - 161700

theorem fullRecordGapTerm03144_eq_value :
    recordGapCenter - 161700 = fullRecordGapValue03144 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03144_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03144 (fullRecordGapValue03144 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03144_not_prime : ¬(recordGapCenter - 161700).Prime := by
  rw [fullRecordGapTerm03144_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03144, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03144_fast_pow_mod_ne_one

def fullRecordGapValue03145 : Nat := fullRecordGapCenterValue - 161698

theorem fullRecordGapTerm03145_eq_value :
    recordGapCenter - 161698 = fullRecordGapValue03145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03145 (fullRecordGapValue03145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03145_not_prime : ¬(recordGapCenter - 161698).Prime := by
  rw [fullRecordGapTerm03145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03145_fast_pow_mod_ne_one

def fullRecordGapValue03146 : Nat := fullRecordGapCenterValue - 161662

theorem fullRecordGapTerm03146_eq_value :
    recordGapCenter - 161662 = fullRecordGapValue03146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03146 (fullRecordGapValue03146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03146_not_prime : ¬(recordGapCenter - 161662).Prime := by
  rw [fullRecordGapTerm03146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03146_fast_pow_mod_ne_one

def fullRecordGapValue03147 : Nat := fullRecordGapCenterValue - 161362

theorem fullRecordGapTerm03147_eq_value :
    recordGapCenter - 161362 = fullRecordGapValue03147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03147 (fullRecordGapValue03147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03147_not_prime : ¬(recordGapCenter - 161362).Prime := by
  rw [fullRecordGapTerm03147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03147_fast_pow_mod_ne_one

def fullRecordGapValue03148 : Nat := fullRecordGapCenterValue - 161338

theorem fullRecordGapTerm03148_eq_value :
    recordGapCenter - 161338 = fullRecordGapValue03148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03148 (fullRecordGapValue03148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03148_not_prime : ¬(recordGapCenter - 161338).Prime := by
  rw [fullRecordGapTerm03148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03148_fast_pow_mod_ne_one

def fullRecordGapValue03149 : Nat := fullRecordGapCenterValue - 161280

theorem fullRecordGapTerm03149_eq_value :
    recordGapCenter - 161280 = fullRecordGapValue03149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03149 (fullRecordGapValue03149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03149_not_prime : ¬(recordGapCenter - 161280).Prime := by
  rw [fullRecordGapTerm03149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03149_fast_pow_mod_ne_one

def fullRecordGapValue03150 : Nat := fullRecordGapCenterValue - 160858

theorem fullRecordGapTerm03150_eq_value :
    recordGapCenter - 160858 = fullRecordGapValue03150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03150 (fullRecordGapValue03150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03150_not_prime : ¬(recordGapCenter - 160858).Prime := by
  rw [fullRecordGapTerm03150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03150_fast_pow_mod_ne_one

def fullRecordGapValue03151 : Nat := fullRecordGapCenterValue - 160774

theorem fullRecordGapTerm03151_eq_value :
    recordGapCenter - 160774 = fullRecordGapValue03151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03151 (fullRecordGapValue03151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03151_not_prime : ¬(recordGapCenter - 160774).Prime := by
  rw [fullRecordGapTerm03151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03151_fast_pow_mod_ne_one

def fullRecordGapValue03152 : Nat := fullRecordGapCenterValue - 160618

theorem fullRecordGapTerm03152_eq_value :
    recordGapCenter - 160618 = fullRecordGapValue03152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03152 (fullRecordGapValue03152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03152_not_prime : ¬(recordGapCenter - 160618).Prime := by
  rw [fullRecordGapTerm03152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03152_fast_pow_mod_ne_one

def fullRecordGapValue03153 : Nat := fullRecordGapCenterValue - 160078

theorem fullRecordGapTerm03153_eq_value :
    recordGapCenter - 160078 = fullRecordGapValue03153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03153 (fullRecordGapValue03153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03153_not_prime : ¬(recordGapCenter - 160078).Prime := by
  rw [fullRecordGapTerm03153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03153_fast_pow_mod_ne_one

def fullRecordGapValue03154 : Nat := fullRecordGapCenterValue - 159778

theorem fullRecordGapTerm03154_eq_value :
    recordGapCenter - 159778 = fullRecordGapValue03154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03154 (fullRecordGapValue03154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03154_not_prime : ¬(recordGapCenter - 159778).Prime := by
  rw [fullRecordGapTerm03154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03154_fast_pow_mod_ne_one

def fullRecordGapValue03155 : Nat := fullRecordGapCenterValue - 159694

theorem fullRecordGapTerm03155_eq_value :
    recordGapCenter - 159694 = fullRecordGapValue03155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03155 (fullRecordGapValue03155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03155_not_prime : ¬(recordGapCenter - 159694).Prime := by
  rw [fullRecordGapTerm03155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03155_fast_pow_mod_ne_one

def fullRecordGapValue03156 : Nat := fullRecordGapCenterValue - 159634

theorem fullRecordGapTerm03156_eq_value :
    recordGapCenter - 159634 = fullRecordGapValue03156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03156 (fullRecordGapValue03156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03156_not_prime : ¬(recordGapCenter - 159634).Prime := by
  rw [fullRecordGapTerm03156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03156_fast_pow_mod_ne_one

def fullRecordGapValue03157 : Nat := fullRecordGapCenterValue - 159382

theorem fullRecordGapTerm03157_eq_value :
    recordGapCenter - 159382 = fullRecordGapValue03157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03157 (fullRecordGapValue03157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03157_not_prime : ¬(recordGapCenter - 159382).Prime := by
  rw [fullRecordGapTerm03157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03157_fast_pow_mod_ne_one

def fullRecordGapValue03158 : Nat := fullRecordGapCenterValue - 158760

theorem fullRecordGapTerm03158_eq_value :
    recordGapCenter - 158760 = fullRecordGapValue03158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03158 (fullRecordGapValue03158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03158_not_prime : ¬(recordGapCenter - 158760).Prime := by
  rw [fullRecordGapTerm03158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03158_fast_pow_mod_ne_one

def fullRecordGapValue03159 : Nat := fullRecordGapCenterValue - 158674

theorem fullRecordGapTerm03159_eq_value :
    recordGapCenter - 158674 = fullRecordGapValue03159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03159 (fullRecordGapValue03159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03159_not_prime : ¬(recordGapCenter - 158674).Prime := by
  rw [fullRecordGapTerm03159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03159_fast_pow_mod_ne_one

def fullRecordGapValue03160 : Nat := fullRecordGapCenterValue - 158482

theorem fullRecordGapTerm03160_eq_value :
    recordGapCenter - 158482 = fullRecordGapValue03160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03160 (fullRecordGapValue03160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03160_not_prime : ¬(recordGapCenter - 158482).Prime := by
  rw [fullRecordGapTerm03160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03160_fast_pow_mod_ne_one

def fullRecordGapValue03161 : Nat := fullRecordGapCenterValue - 158400

theorem fullRecordGapTerm03161_eq_value :
    recordGapCenter - 158400 = fullRecordGapValue03161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03161 (fullRecordGapValue03161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03161_not_prime : ¬(recordGapCenter - 158400).Prime := by
  rw [fullRecordGapTerm03161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03161_fast_pow_mod_ne_one

def fullRecordGapValue03162 : Nat := fullRecordGapCenterValue - 158302

theorem fullRecordGapTerm03162_eq_value :
    recordGapCenter - 158302 = fullRecordGapValue03162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03162 (fullRecordGapValue03162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03162_not_prime : ¬(recordGapCenter - 158302).Prime := by
  rw [fullRecordGapTerm03162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03162_fast_pow_mod_ne_one

def fullRecordGapValue03163 : Nat := fullRecordGapCenterValue - 158062

theorem fullRecordGapTerm03163_eq_value :
    recordGapCenter - 158062 = fullRecordGapValue03163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03163 (fullRecordGapValue03163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03163_not_prime : ¬(recordGapCenter - 158062).Prime := by
  rw [fullRecordGapTerm03163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03163_fast_pow_mod_ne_one

def fullRecordGapValue03164 : Nat := fullRecordGapCenterValue - 157978

theorem fullRecordGapTerm03164_eq_value :
    recordGapCenter - 157978 = fullRecordGapValue03164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03164 (fullRecordGapValue03164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03164_not_prime : ¬(recordGapCenter - 157978).Prime := by
  rw [fullRecordGapTerm03164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03164_fast_pow_mod_ne_one

def fullRecordGapValue03165 : Nat := fullRecordGapCenterValue - 157714

theorem fullRecordGapTerm03165_eq_value :
    recordGapCenter - 157714 = fullRecordGapValue03165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03165 (fullRecordGapValue03165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03165_not_prime : ¬(recordGapCenter - 157714).Prime := by
  rw [fullRecordGapTerm03165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03165_fast_pow_mod_ne_one

def fullRecordGapValue03166 : Nat := fullRecordGapCenterValue - 157618

theorem fullRecordGapTerm03166_eq_value :
    recordGapCenter - 157618 = fullRecordGapValue03166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03166 (fullRecordGapValue03166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03166_not_prime : ¬(recordGapCenter - 157618).Prime := by
  rw [fullRecordGapTerm03166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03166_fast_pow_mod_ne_one

def fullRecordGapValue03167 : Nat := fullRecordGapCenterValue - 157594

theorem fullRecordGapTerm03167_eq_value :
    recordGapCenter - 157594 = fullRecordGapValue03167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03167 (fullRecordGapValue03167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03167_not_prime : ¬(recordGapCenter - 157594).Prime := by
  rw [fullRecordGapTerm03167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03167_fast_pow_mod_ne_one

def fullRecordGapValue03168 : Nat := fullRecordGapCenterValue - 157582

theorem fullRecordGapTerm03168_eq_value :
    recordGapCenter - 157582 = fullRecordGapValue03168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03168 (fullRecordGapValue03168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03168_not_prime : ¬(recordGapCenter - 157582).Prime := by
  rw [fullRecordGapTerm03168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03168_fast_pow_mod_ne_one

def fullRecordGapValue03169 : Nat := fullRecordGapCenterValue - 156874

theorem fullRecordGapTerm03169_eq_value :
    recordGapCenter - 156874 = fullRecordGapValue03169 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03169_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03169 (fullRecordGapValue03169 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03169_not_prime : ¬(recordGapCenter - 156874).Prime := by
  rw [fullRecordGapTerm03169_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03169, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03169_fast_pow_mod_ne_one

def fullRecordGapValue03170 : Nat := fullRecordGapCenterValue - 156802

theorem fullRecordGapTerm03170_eq_value :
    recordGapCenter - 156802 = fullRecordGapValue03170 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03170_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03170 (fullRecordGapValue03170 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03170_not_prime : ¬(recordGapCenter - 156802).Prime := by
  rw [fullRecordGapTerm03170_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03170, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03170_fast_pow_mod_ne_one

def fullRecordGapValue03171 : Nat := fullRecordGapCenterValue - 156694

theorem fullRecordGapTerm03171_eq_value :
    recordGapCenter - 156694 = fullRecordGapValue03171 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03171_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03171 (fullRecordGapValue03171 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03171_not_prime : ¬(recordGapCenter - 156694).Prime := by
  rw [fullRecordGapTerm03171_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03171, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03171_fast_pow_mod_ne_one

def fullRecordGapValue03172 : Nat := fullRecordGapCenterValue - 156382

theorem fullRecordGapTerm03172_eq_value :
    recordGapCenter - 156382 = fullRecordGapValue03172 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03172_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03172 (fullRecordGapValue03172 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03172_not_prime : ¬(recordGapCenter - 156382).Prime := by
  rw [fullRecordGapTerm03172_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03172, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03172_fast_pow_mod_ne_one

def fullRecordGapValue03173 : Nat := fullRecordGapCenterValue - 156250

theorem fullRecordGapTerm03173_eq_value :
    recordGapCenter - 156250 = fullRecordGapValue03173 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03173_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03173 (fullRecordGapValue03173 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03173_not_prime : ¬(recordGapCenter - 156250).Prime := by
  rw [fullRecordGapTerm03173_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03173, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03173_fast_pow_mod_ne_one

def fullRecordGapValue03174 : Nat := fullRecordGapCenterValue - 156082

theorem fullRecordGapTerm03174_eq_value :
    recordGapCenter - 156082 = fullRecordGapValue03174 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03174_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03174 (fullRecordGapValue03174 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03174_not_prime : ¬(recordGapCenter - 156082).Prime := by
  rw [fullRecordGapTerm03174_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03174, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03174_fast_pow_mod_ne_one

def fullRecordGapValue03175 : Nat := fullRecordGapCenterValue - 155998

theorem fullRecordGapTerm03175_eq_value :
    recordGapCenter - 155998 = fullRecordGapValue03175 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03175_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03175 (fullRecordGapValue03175 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03175_not_prime : ¬(recordGapCenter - 155998).Prime := by
  rw [fullRecordGapTerm03175_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03175, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03175_fast_pow_mod_ne_one

def fullRecordGapValue03176 : Nat := fullRecordGapCenterValue - 155902

theorem fullRecordGapTerm03176_eq_value :
    recordGapCenter - 155902 = fullRecordGapValue03176 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03176_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03176 (fullRecordGapValue03176 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03176_not_prime : ¬(recordGapCenter - 155902).Prime := by
  rw [fullRecordGapTerm03176_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03176, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03176_fast_pow_mod_ne_one

def fullRecordGapValue03177 : Nat := fullRecordGapCenterValue - 155734

theorem fullRecordGapTerm03177_eq_value :
    recordGapCenter - 155734 = fullRecordGapValue03177 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03177_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03177 (fullRecordGapValue03177 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03177_not_prime : ¬(recordGapCenter - 155734).Prime := by
  rw [fullRecordGapTerm03177_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03177, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03177_fast_pow_mod_ne_one

def fullRecordGapValue03178 : Nat := fullRecordGapCenterValue - 155602

theorem fullRecordGapTerm03178_eq_value :
    recordGapCenter - 155602 = fullRecordGapValue03178 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03178_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03178 (fullRecordGapValue03178 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03178_not_prime : ¬(recordGapCenter - 155602).Prime := by
  rw [fullRecordGapTerm03178_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03178, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03178_fast_pow_mod_ne_one

def fullRecordGapValue03179 : Nat := fullRecordGapCenterValue - 155398

theorem fullRecordGapTerm03179_eq_value :
    recordGapCenter - 155398 = fullRecordGapValue03179 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03179_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03179 (fullRecordGapValue03179 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03179_not_prime : ¬(recordGapCenter - 155398).Prime := by
  rw [fullRecordGapTerm03179_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03179, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03179_fast_pow_mod_ne_one

def fullRecordGapValue03180 : Nat := fullRecordGapCenterValue - 155362

theorem fullRecordGapTerm03180_eq_value :
    recordGapCenter - 155362 = fullRecordGapValue03180 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03180_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03180 (fullRecordGapValue03180 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03180_not_prime : ¬(recordGapCenter - 155362).Prime := by
  rw [fullRecordGapTerm03180_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03180, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03180_fast_pow_mod_ne_one

def fullRecordGapValue03181 : Nat := fullRecordGapCenterValue - 155232

theorem fullRecordGapTerm03181_eq_value :
    recordGapCenter - 155232 = fullRecordGapValue03181 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03181_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03181 (fullRecordGapValue03181 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03181_not_prime : ¬(recordGapCenter - 155232).Prime := by
  rw [fullRecordGapTerm03181_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03181, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03181_fast_pow_mod_ne_one

def fullRecordGapValue03182 : Nat := fullRecordGapCenterValue - 154702

theorem fullRecordGapTerm03182_eq_value :
    recordGapCenter - 154702 = fullRecordGapValue03182 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03182_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03182 (fullRecordGapValue03182 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03182_not_prime : ¬(recordGapCenter - 154702).Prime := by
  rw [fullRecordGapTerm03182_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03182, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03182_fast_pow_mod_ne_one

def fullRecordGapValue03183 : Nat := fullRecordGapCenterValue - 154558

theorem fullRecordGapTerm03183_eq_value :
    recordGapCenter - 154558 = fullRecordGapValue03183 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03183_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03183 (fullRecordGapValue03183 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03183_not_prime : ¬(recordGapCenter - 154558).Prime := by
  rw [fullRecordGapTerm03183_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03183, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03183_fast_pow_mod_ne_one

def fullRecordGapValue03184 : Nat := fullRecordGapCenterValue - 154342

theorem fullRecordGapTerm03184_eq_value :
    recordGapCenter - 154342 = fullRecordGapValue03184 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03184_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03184 (fullRecordGapValue03184 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03184_not_prime : ¬(recordGapCenter - 154342).Prime := by
  rw [fullRecordGapTerm03184_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03184, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03184_fast_pow_mod_ne_one

def fullRecordGapValue03185 : Nat := fullRecordGapCenterValue - 154282

theorem fullRecordGapTerm03185_eq_value :
    recordGapCenter - 154282 = fullRecordGapValue03185 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03185_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03185 (fullRecordGapValue03185 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03185_not_prime : ¬(recordGapCenter - 154282).Prime := by
  rw [fullRecordGapTerm03185_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03185, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03185_fast_pow_mod_ne_one

def fullRecordGapValue03186 : Nat := fullRecordGapCenterValue - 154138

theorem fullRecordGapTerm03186_eq_value :
    recordGapCenter - 154138 = fullRecordGapValue03186 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03186_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03186 (fullRecordGapValue03186 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03186_not_prime : ¬(recordGapCenter - 154138).Prime := by
  rw [fullRecordGapTerm03186_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03186, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03186_fast_pow_mod_ne_one

def fullRecordGapValue03187 : Nat := fullRecordGapCenterValue - 153922

theorem fullRecordGapTerm03187_eq_value :
    recordGapCenter - 153922 = fullRecordGapValue03187 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03187_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03187 (fullRecordGapValue03187 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03187_not_prime : ¬(recordGapCenter - 153922).Prime := by
  rw [fullRecordGapTerm03187_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03187, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03187_fast_pow_mod_ne_one

def fullRecordGapValue03188 : Nat := fullRecordGapCenterValue - 153838

theorem fullRecordGapTerm03188_eq_value :
    recordGapCenter - 153838 = fullRecordGapValue03188 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03188_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03188 (fullRecordGapValue03188 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03188_not_prime : ¬(recordGapCenter - 153838).Prime := by
  rw [fullRecordGapTerm03188_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03188, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03188_fast_pow_mod_ne_one

def fullRecordGapValue03189 : Nat := fullRecordGapCenterValue - 153664

theorem fullRecordGapTerm03189_eq_value :
    recordGapCenter - 153664 = fullRecordGapValue03189 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03189_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03189 (fullRecordGapValue03189 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03189_not_prime : ¬(recordGapCenter - 153664).Prime := by
  rw [fullRecordGapTerm03189_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03189, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03189_fast_pow_mod_ne_one

def fullRecordGapValue03190 : Nat := fullRecordGapCenterValue - 153600

theorem fullRecordGapTerm03190_eq_value :
    recordGapCenter - 153600 = fullRecordGapValue03190 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03190_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03190 (fullRecordGapValue03190 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03190_not_prime : ¬(recordGapCenter - 153600).Prime := by
  rw [fullRecordGapTerm03190_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03190, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03190_fast_pow_mod_ne_one

def fullRecordGapValue03191 : Nat := fullRecordGapCenterValue - 153562

theorem fullRecordGapTerm03191_eq_value :
    recordGapCenter - 153562 = fullRecordGapValue03191 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03191_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03191 (fullRecordGapValue03191 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03191_not_prime : ¬(recordGapCenter - 153562).Prime := by
  rw [fullRecordGapTerm03191_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03191, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03191_fast_pow_mod_ne_one

def fullRecordGapValue03192 : Nat := fullRecordGapCenterValue - 153514

theorem fullRecordGapTerm03192_eq_value :
    recordGapCenter - 153514 = fullRecordGapValue03192 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03192_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03192 (fullRecordGapValue03192 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03192_not_prime : ¬(recordGapCenter - 153514).Prime := by
  rw [fullRecordGapTerm03192_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03192, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03192_fast_pow_mod_ne_one

def fullRecordGapValue03193 : Nat := fullRecordGapCenterValue - 153358

theorem fullRecordGapTerm03193_eq_value :
    recordGapCenter - 153358 = fullRecordGapValue03193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03193 (fullRecordGapValue03193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03193_not_prime : ¬(recordGapCenter - 153358).Prime := by
  rw [fullRecordGapTerm03193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03193_fast_pow_mod_ne_one

def fullRecordGapValue03194 : Nat := fullRecordGapCenterValue - 153262

theorem fullRecordGapTerm03194_eq_value :
    recordGapCenter - 153262 = fullRecordGapValue03194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03194 (fullRecordGapValue03194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03194_not_prime : ¬(recordGapCenter - 153262).Prime := by
  rw [fullRecordGapTerm03194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03194_fast_pow_mod_ne_one

def fullRecordGapValue03195 : Nat := fullRecordGapCenterValue - 153214

theorem fullRecordGapTerm03195_eq_value :
    recordGapCenter - 153214 = fullRecordGapValue03195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03195 (fullRecordGapValue03195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03195_not_prime : ¬(recordGapCenter - 153214).Prime := by
  rw [fullRecordGapTerm03195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03195_fast_pow_mod_ne_one

def fullRecordGapValue03196 : Nat := fullRecordGapCenterValue - 152962

theorem fullRecordGapTerm03196_eq_value :
    recordGapCenter - 152962 = fullRecordGapValue03196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03196 (fullRecordGapValue03196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03196_not_prime : ¬(recordGapCenter - 152962).Prime := by
  rw [fullRecordGapTerm03196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03196_fast_pow_mod_ne_one

def fullRecordGapValue03197 : Nat := fullRecordGapCenterValue - 152842

theorem fullRecordGapTerm03197_eq_value :
    recordGapCenter - 152842 = fullRecordGapValue03197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03197 (fullRecordGapValue03197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03197_not_prime : ¬(recordGapCenter - 152842).Prime := by
  rw [fullRecordGapTerm03197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03197_fast_pow_mod_ne_one

def fullRecordGapValue03198 : Nat := fullRecordGapCenterValue - 152758

theorem fullRecordGapTerm03198_eq_value :
    recordGapCenter - 152758 = fullRecordGapValue03198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03198 (fullRecordGapValue03198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03198_not_prime : ¬(recordGapCenter - 152758).Prime := by
  rw [fullRecordGapTerm03198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03198_fast_pow_mod_ne_one

def fullRecordGapValue03199 : Nat := fullRecordGapCenterValue - 152158

theorem fullRecordGapTerm03199_eq_value :
    recordGapCenter - 152158 = fullRecordGapValue03199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03199 (fullRecordGapValue03199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03199_not_prime : ¬(recordGapCenter - 152158).Prime := by
  rw [fullRecordGapTerm03199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03199_fast_pow_mod_ne_one

def fullRecordGapValue03200 : Nat := fullRecordGapCenterValue - 152064

theorem fullRecordGapTerm03200_eq_value :
    recordGapCenter - 152064 = fullRecordGapValue03200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03200 (fullRecordGapValue03200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03200_not_prime : ¬(recordGapCenter - 152064).Prime := by
  rw [fullRecordGapTerm03200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03200_fast_pow_mod_ne_one

def fullRecordGapValue03201 : Nat := fullRecordGapCenterValue - 151594

theorem fullRecordGapTerm03201_eq_value :
    recordGapCenter - 151594 = fullRecordGapValue03201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03201 (fullRecordGapValue03201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03201_not_prime : ¬(recordGapCenter - 151594).Prime := by
  rw [fullRecordGapTerm03201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03201_fast_pow_mod_ne_one

def fullRecordGapValue03202 : Nat := fullRecordGapCenterValue - 151414

theorem fullRecordGapTerm03202_eq_value :
    recordGapCenter - 151414 = fullRecordGapValue03202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03202 (fullRecordGapValue03202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03202_not_prime : ¬(recordGapCenter - 151414).Prime := by
  rw [fullRecordGapTerm03202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03202_fast_pow_mod_ne_one

def fullRecordGapValue03203 : Nat := fullRecordGapCenterValue - 151282

theorem fullRecordGapTerm03203_eq_value :
    recordGapCenter - 151282 = fullRecordGapValue03203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03203 (fullRecordGapValue03203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03203_not_prime : ¬(recordGapCenter - 151282).Prime := by
  rw [fullRecordGapTerm03203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03203_fast_pow_mod_ne_one

def fullRecordGapValue03204 : Nat := fullRecordGapCenterValue - 151258

theorem fullRecordGapTerm03204_eq_value :
    recordGapCenter - 151258 = fullRecordGapValue03204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03204 (fullRecordGapValue03204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03204_not_prime : ¬(recordGapCenter - 151258).Prime := by
  rw [fullRecordGapTerm03204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03204_fast_pow_mod_ne_one

def fullRecordGapValue03205 : Nat := fullRecordGapCenterValue - 151234

theorem fullRecordGapTerm03205_eq_value :
    recordGapCenter - 151234 = fullRecordGapValue03205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03205 (fullRecordGapValue03205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03205_not_prime : ¬(recordGapCenter - 151234).Prime := by
  rw [fullRecordGapTerm03205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03205_fast_pow_mod_ne_one

def fullRecordGapValue03206 : Nat := fullRecordGapCenterValue - 151200

theorem fullRecordGapTerm03206_eq_value :
    recordGapCenter - 151200 = fullRecordGapValue03206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03206 (fullRecordGapValue03206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03206_not_prime : ¬(recordGapCenter - 151200).Prime := by
  rw [fullRecordGapTerm03206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03206_fast_pow_mod_ne_one

def fullRecordGapValue03207 : Nat := fullRecordGapCenterValue - 150958

theorem fullRecordGapTerm03207_eq_value :
    recordGapCenter - 150958 = fullRecordGapValue03207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03207 (fullRecordGapValue03207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03207_not_prime : ¬(recordGapCenter - 150958).Prime := by
  rw [fullRecordGapTerm03207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03207_fast_pow_mod_ne_one

def fullRecordGapValue03208 : Nat := fullRecordGapCenterValue - 150694

theorem fullRecordGapTerm03208_eq_value :
    recordGapCenter - 150694 = fullRecordGapValue03208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03208 (fullRecordGapValue03208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03208_not_prime : ¬(recordGapCenter - 150694).Prime := by
  rw [fullRecordGapTerm03208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03208_fast_pow_mod_ne_one

def fullRecordGapValue03209 : Nat := fullRecordGapCenterValue - 150538

theorem fullRecordGapTerm03209_eq_value :
    recordGapCenter - 150538 = fullRecordGapValue03209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03209 (fullRecordGapValue03209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03209_not_prime : ¬(recordGapCenter - 150538).Prime := by
  rw [fullRecordGapTerm03209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03209_fast_pow_mod_ne_one

def fullRecordGapValue03210 : Nat := fullRecordGapCenterValue - 150034

theorem fullRecordGapTerm03210_eq_value :
    recordGapCenter - 150034 = fullRecordGapValue03210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03210 (fullRecordGapValue03210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03210_not_prime : ¬(recordGapCenter - 150034).Prime := by
  rw [fullRecordGapTerm03210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03210_fast_pow_mod_ne_one

def fullRecordGapValue03211 : Nat := fullRecordGapCenterValue - 149398

theorem fullRecordGapTerm03211_eq_value :
    recordGapCenter - 149398 = fullRecordGapValue03211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03211 (fullRecordGapValue03211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03211_not_prime : ¬(recordGapCenter - 149398).Prime := by
  rw [fullRecordGapTerm03211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03211_fast_pow_mod_ne_one

def fullRecordGapValue03212 : Nat := fullRecordGapCenterValue - 149134

theorem fullRecordGapTerm03212_eq_value :
    recordGapCenter - 149134 = fullRecordGapValue03212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03212 (fullRecordGapValue03212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03212_not_prime : ¬(recordGapCenter - 149134).Prime := by
  rw [fullRecordGapTerm03212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03212_fast_pow_mod_ne_one

def fullRecordGapValue03213 : Nat := fullRecordGapCenterValue - 149062

theorem fullRecordGapTerm03213_eq_value :
    recordGapCenter - 149062 = fullRecordGapValue03213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03213 (fullRecordGapValue03213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03213_not_prime : ¬(recordGapCenter - 149062).Prime := by
  rw [fullRecordGapTerm03213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03213_fast_pow_mod_ne_one

def fullRecordGapValue03214 : Nat := fullRecordGapCenterValue - 148942

theorem fullRecordGapTerm03214_eq_value :
    recordGapCenter - 148942 = fullRecordGapValue03214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03214 (fullRecordGapValue03214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03214_not_prime : ¬(recordGapCenter - 148942).Prime := by
  rw [fullRecordGapTerm03214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03214_fast_pow_mod_ne_one

def fullRecordGapValue03215 : Nat := fullRecordGapCenterValue - 148714

theorem fullRecordGapTerm03215_eq_value :
    recordGapCenter - 148714 = fullRecordGapValue03215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03215 (fullRecordGapValue03215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03215_not_prime : ¬(recordGapCenter - 148714).Prime := by
  rw [fullRecordGapTerm03215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03215_fast_pow_mod_ne_one

def fullRecordGapValue03216 : Nat := fullRecordGapCenterValue - 148462

theorem fullRecordGapTerm03216_eq_value :
    recordGapCenter - 148462 = fullRecordGapValue03216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03216 (fullRecordGapValue03216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03216_not_prime : ¬(recordGapCenter - 148462).Prime := by
  rw [fullRecordGapTerm03216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03216_fast_pow_mod_ne_one

def fullRecordGapValue03217 : Nat := fullRecordGapCenterValue - 148354

theorem fullRecordGapTerm03217_eq_value :
    recordGapCenter - 148354 = fullRecordGapValue03217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03217 (fullRecordGapValue03217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03217_not_prime : ¬(recordGapCenter - 148354).Prime := by
  rw [fullRecordGapTerm03217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03217_fast_pow_mod_ne_one

def fullRecordGapValue03218 : Nat := fullRecordGapCenterValue - 148102

theorem fullRecordGapTerm03218_eq_value :
    recordGapCenter - 148102 = fullRecordGapValue03218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03218 (fullRecordGapValue03218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03218_not_prime : ¬(recordGapCenter - 148102).Prime := by
  rw [fullRecordGapTerm03218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03218_fast_pow_mod_ne_one

def fullRecordGapValue03219 : Nat := fullRecordGapCenterValue - 148054

theorem fullRecordGapTerm03219_eq_value :
    recordGapCenter - 148054 = fullRecordGapValue03219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03219 (fullRecordGapValue03219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03219_not_prime : ¬(recordGapCenter - 148054).Prime := by
  rw [fullRecordGapTerm03219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03219_fast_pow_mod_ne_one

def fullRecordGapValue03220 : Nat := fullRecordGapCenterValue - 147840

theorem fullRecordGapTerm03220_eq_value :
    recordGapCenter - 147840 = fullRecordGapValue03220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03220 (fullRecordGapValue03220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03220_not_prime : ¬(recordGapCenter - 147840).Prime := by
  rw [fullRecordGapTerm03220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03220_fast_pow_mod_ne_one

def fullRecordGapValue03221 : Nat := fullRecordGapCenterValue - 147214

theorem fullRecordGapTerm03221_eq_value :
    recordGapCenter - 147214 = fullRecordGapValue03221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03221 (fullRecordGapValue03221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03221_not_prime : ¬(recordGapCenter - 147214).Prime := by
  rw [fullRecordGapTerm03221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03221_fast_pow_mod_ne_one

def fullRecordGapValue03222 : Nat := fullRecordGapCenterValue - 147094

theorem fullRecordGapTerm03222_eq_value :
    recordGapCenter - 147094 = fullRecordGapValue03222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03222 (fullRecordGapValue03222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03222_not_prime : ¬(recordGapCenter - 147094).Prime := by
  rw [fullRecordGapTerm03222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03222_fast_pow_mod_ne_one

def fullRecordGapValue03223 : Nat := fullRecordGapCenterValue - 146758

theorem fullRecordGapTerm03223_eq_value :
    recordGapCenter - 146758 = fullRecordGapValue03223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03223 (fullRecordGapValue03223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03223_not_prime : ¬(recordGapCenter - 146758).Prime := by
  rw [fullRecordGapTerm03223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03223_fast_pow_mod_ne_one

def fullRecordGapValue03224 : Nat := fullRecordGapCenterValue - 146662

theorem fullRecordGapTerm03224_eq_value :
    recordGapCenter - 146662 = fullRecordGapValue03224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03224 (fullRecordGapValue03224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03224_not_prime : ¬(recordGapCenter - 146662).Prime := by
  rw [fullRecordGapTerm03224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03224_fast_pow_mod_ne_one

def fullRecordGapValue03225 : Nat := fullRecordGapCenterValue - 146410

theorem fullRecordGapTerm03225_eq_value :
    recordGapCenter - 146410 = fullRecordGapValue03225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03225 (fullRecordGapValue03225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03225_not_prime : ¬(recordGapCenter - 146410).Prime := by
  rw [fullRecordGapTerm03225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03225_fast_pow_mod_ne_one

def fullRecordGapValue03226 : Nat := fullRecordGapCenterValue - 146362

theorem fullRecordGapTerm03226_eq_value :
    recordGapCenter - 146362 = fullRecordGapValue03226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03226 (fullRecordGapValue03226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03226_not_prime : ¬(recordGapCenter - 146362).Prime := by
  rw [fullRecordGapTerm03226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03226_fast_pow_mod_ne_one

def fullRecordGapValue03227 : Nat := fullRecordGapCenterValue - 146158

theorem fullRecordGapTerm03227_eq_value :
    recordGapCenter - 146158 = fullRecordGapValue03227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03227 (fullRecordGapValue03227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03227_not_prime : ¬(recordGapCenter - 146158).Prime := by
  rw [fullRecordGapTerm03227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03227_fast_pow_mod_ne_one

def fullRecordGapValue03228 : Nat := fullRecordGapCenterValue - 146038

theorem fullRecordGapTerm03228_eq_value :
    recordGapCenter - 146038 = fullRecordGapValue03228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03228 (fullRecordGapValue03228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03228_not_prime : ¬(recordGapCenter - 146038).Prime := by
  rw [fullRecordGapTerm03228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03228_fast_pow_mod_ne_one

def fullRecordGapValue03229 : Nat := fullRecordGapCenterValue - 145954

theorem fullRecordGapTerm03229_eq_value :
    recordGapCenter - 145954 = fullRecordGapValue03229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03229 (fullRecordGapValue03229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03229_not_prime : ¬(recordGapCenter - 145954).Prime := by
  rw [fullRecordGapTerm03229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03229_fast_pow_mod_ne_one

def fullRecordGapValue03230 : Nat := fullRecordGapCenterValue - 145800

theorem fullRecordGapTerm03230_eq_value :
    recordGapCenter - 145800 = fullRecordGapValue03230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03230 (fullRecordGapValue03230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03230_not_prime : ¬(recordGapCenter - 145800).Prime := by
  rw [fullRecordGapTerm03230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03230_fast_pow_mod_ne_one

def fullRecordGapValue03231 : Nat := fullRecordGapCenterValue - 145738

theorem fullRecordGapTerm03231_eq_value :
    recordGapCenter - 145738 = fullRecordGapValue03231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03231 (fullRecordGapValue03231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03231_not_prime : ¬(recordGapCenter - 145738).Prime := by
  rw [fullRecordGapTerm03231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03231_fast_pow_mod_ne_one

def fullRecordGapValue03232 : Nat := fullRecordGapCenterValue - 145438

theorem fullRecordGapTerm03232_eq_value :
    recordGapCenter - 145438 = fullRecordGapValue03232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03232 (fullRecordGapValue03232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03232_not_prime : ¬(recordGapCenter - 145438).Prime := by
  rw [fullRecordGapTerm03232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03232_fast_pow_mod_ne_one

def fullRecordGapValue03233 : Nat := fullRecordGapCenterValue - 145414

theorem fullRecordGapTerm03233_eq_value :
    recordGapCenter - 145414 = fullRecordGapValue03233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03233 (fullRecordGapValue03233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03233_not_prime : ¬(recordGapCenter - 145414).Prime := by
  rw [fullRecordGapTerm03233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03233_fast_pow_mod_ne_one

def fullRecordGapValue03234 : Nat := fullRecordGapCenterValue - 145102

theorem fullRecordGapTerm03234_eq_value :
    recordGapCenter - 145102 = fullRecordGapValue03234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03234 (fullRecordGapValue03234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03234_not_prime : ¬(recordGapCenter - 145102).Prime := by
  rw [fullRecordGapTerm03234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03234_fast_pow_mod_ne_one

def fullRecordGapValue03235 : Nat := fullRecordGapCenterValue - 144934

theorem fullRecordGapTerm03235_eq_value :
    recordGapCenter - 144934 = fullRecordGapValue03235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03235 (fullRecordGapValue03235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03235_not_prime : ¬(recordGapCenter - 144934).Prime := by
  rw [fullRecordGapTerm03235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03235_fast_pow_mod_ne_one

def fullRecordGapValue03236 : Nat := fullRecordGapCenterValue - 144862

theorem fullRecordGapTerm03236_eq_value :
    recordGapCenter - 144862 = fullRecordGapValue03236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03236 (fullRecordGapValue03236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03236_not_prime : ¬(recordGapCenter - 144862).Prime := by
  rw [fullRecordGapTerm03236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03236_fast_pow_mod_ne_one

def fullRecordGapValue03237 : Nat := fullRecordGapCenterValue - 144682

theorem fullRecordGapTerm03237_eq_value :
    recordGapCenter - 144682 = fullRecordGapValue03237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03237 (fullRecordGapValue03237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03237_not_prime : ¬(recordGapCenter - 144682).Prime := by
  rw [fullRecordGapTerm03237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03237_fast_pow_mod_ne_one

def fullRecordGapValue03238 : Nat := fullRecordGapCenterValue - 144574

theorem fullRecordGapTerm03238_eq_value :
    recordGapCenter - 144574 = fullRecordGapValue03238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03238 (fullRecordGapValue03238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03238_not_prime : ¬(recordGapCenter - 144574).Prime := by
  rw [fullRecordGapTerm03238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03238_fast_pow_mod_ne_one

def fullRecordGapValue03239 : Nat := fullRecordGapCenterValue - 144322

theorem fullRecordGapTerm03239_eq_value :
    recordGapCenter - 144322 = fullRecordGapValue03239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03239 (fullRecordGapValue03239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03239_not_prime : ¬(recordGapCenter - 144322).Prime := by
  rw [fullRecordGapTerm03239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03239_fast_pow_mod_ne_one

def fullRecordGapValue03240 : Nat := fullRecordGapCenterValue - 144178

theorem fullRecordGapTerm03240_eq_value :
    recordGapCenter - 144178 = fullRecordGapValue03240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03240 (fullRecordGapValue03240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03240_not_prime : ¬(recordGapCenter - 144178).Prime := by
  rw [fullRecordGapTerm03240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03240_fast_pow_mod_ne_one

def fullRecordGapValue03241 : Nat := fullRecordGapCenterValue - 144154

theorem fullRecordGapTerm03241_eq_value :
    recordGapCenter - 144154 = fullRecordGapValue03241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03241 (fullRecordGapValue03241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03241_not_prime : ¬(recordGapCenter - 144154).Prime := by
  rw [fullRecordGapTerm03241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03241_fast_pow_mod_ne_one

def fullRecordGapValue03242 : Nat := fullRecordGapCenterValue - 143974

theorem fullRecordGapTerm03242_eq_value :
    recordGapCenter - 143974 = fullRecordGapValue03242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03242 (fullRecordGapValue03242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03242_not_prime : ¬(recordGapCenter - 143974).Prime := by
  rw [fullRecordGapTerm03242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03242_fast_pow_mod_ne_one

def fullRecordGapValue03243 : Nat := fullRecordGapCenterValue - 143748

theorem fullRecordGapTerm03243_eq_value :
    recordGapCenter - 143748 = fullRecordGapValue03243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03243 (fullRecordGapValue03243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03243_not_prime : ¬(recordGapCenter - 143748).Prime := by
  rw [fullRecordGapTerm03243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03243_fast_pow_mod_ne_one

def fullRecordGapValue03244 : Nat := fullRecordGapCenterValue - 143722

theorem fullRecordGapTerm03244_eq_value :
    recordGapCenter - 143722 = fullRecordGapValue03244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03244 (fullRecordGapValue03244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03244_not_prime : ¬(recordGapCenter - 143722).Prime := by
  rw [fullRecordGapTerm03244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03244_fast_pow_mod_ne_one

def fullRecordGapValue03245 : Nat := fullRecordGapCenterValue - 143698

theorem fullRecordGapTerm03245_eq_value :
    recordGapCenter - 143698 = fullRecordGapValue03245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03245 (fullRecordGapValue03245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03245_not_prime : ¬(recordGapCenter - 143698).Prime := by
  rw [fullRecordGapTerm03245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03245_fast_pow_mod_ne_one

def fullRecordGapValue03246 : Nat := fullRecordGapCenterValue - 143614

theorem fullRecordGapTerm03246_eq_value :
    recordGapCenter - 143614 = fullRecordGapValue03246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03246 (fullRecordGapValue03246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03246_not_prime : ¬(recordGapCenter - 143614).Prime := by
  rw [fullRecordGapTerm03246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03246_fast_pow_mod_ne_one

def fullRecordGapValue03247 : Nat := fullRecordGapCenterValue - 143398

theorem fullRecordGapTerm03247_eq_value :
    recordGapCenter - 143398 = fullRecordGapValue03247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03247 (fullRecordGapValue03247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03247_not_prime : ¬(recordGapCenter - 143398).Prime := by
  rw [fullRecordGapTerm03247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03247_fast_pow_mod_ne_one

def fullRecordGapValue03248 : Nat := fullRecordGapCenterValue - 143098

theorem fullRecordGapTerm03248_eq_value :
    recordGapCenter - 143098 = fullRecordGapValue03248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03248 (fullRecordGapValue03248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03248_not_prime : ¬(recordGapCenter - 143098).Prime := by
  rw [fullRecordGapTerm03248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03248_fast_pow_mod_ne_one

def fullRecordGapValue03249 : Nat := fullRecordGapCenterValue - 142884

theorem fullRecordGapTerm03249_eq_value :
    recordGapCenter - 142884 = fullRecordGapValue03249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03249 (fullRecordGapValue03249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03249_not_prime : ¬(recordGapCenter - 142884).Prime := by
  rw [fullRecordGapTerm03249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03249_fast_pow_mod_ne_one

def fullRecordGapValue03250 : Nat := fullRecordGapCenterValue - 142858

theorem fullRecordGapTerm03250_eq_value :
    recordGapCenter - 142858 = fullRecordGapValue03250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03250 (fullRecordGapValue03250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03250_not_prime : ¬(recordGapCenter - 142858).Prime := by
  rw [fullRecordGapTerm03250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03250_fast_pow_mod_ne_one

def fullRecordGapValue03251 : Nat := fullRecordGapCenterValue - 142678

theorem fullRecordGapTerm03251_eq_value :
    recordGapCenter - 142678 = fullRecordGapValue03251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03251 (fullRecordGapValue03251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03251_not_prime : ¬(recordGapCenter - 142678).Prime := by
  rw [fullRecordGapTerm03251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03251_fast_pow_mod_ne_one

def fullRecordGapValue03252 : Nat := fullRecordGapCenterValue - 142342

theorem fullRecordGapTerm03252_eq_value :
    recordGapCenter - 142342 = fullRecordGapValue03252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03252 (fullRecordGapValue03252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03252_not_prime : ¬(recordGapCenter - 142342).Prime := by
  rw [fullRecordGapTerm03252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03252_fast_pow_mod_ne_one

def fullRecordGapValue03253 : Nat := fullRecordGapCenterValue - 142294

theorem fullRecordGapTerm03253_eq_value :
    recordGapCenter - 142294 = fullRecordGapValue03253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03253 (fullRecordGapValue03253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03253_not_prime : ¬(recordGapCenter - 142294).Prime := by
  rw [fullRecordGapTerm03253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03253_fast_pow_mod_ne_one

def fullRecordGapValue03254 : Nat := fullRecordGapCenterValue - 142162

theorem fullRecordGapTerm03254_eq_value :
    recordGapCenter - 142162 = fullRecordGapValue03254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03254 (fullRecordGapValue03254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03254_not_prime : ¬(recordGapCenter - 142162).Prime := by
  rw [fullRecordGapTerm03254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03254_fast_pow_mod_ne_one

def fullRecordGapValue03255 : Nat := fullRecordGapCenterValue - 142138

theorem fullRecordGapTerm03255_eq_value :
    recordGapCenter - 142138 = fullRecordGapValue03255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03255 (fullRecordGapValue03255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03255_not_prime : ¬(recordGapCenter - 142138).Prime := by
  rw [fullRecordGapTerm03255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03255_fast_pow_mod_ne_one

def fullRecordGapValue03256 : Nat := fullRecordGapCenterValue - 141874

theorem fullRecordGapTerm03256_eq_value :
    recordGapCenter - 141874 = fullRecordGapValue03256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03256 (fullRecordGapValue03256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03256_not_prime : ¬(recordGapCenter - 141874).Prime := by
  rw [fullRecordGapTerm03256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03256_fast_pow_mod_ne_one

def fullRecordGapValue03257 : Nat := fullRecordGapCenterValue - 141682

theorem fullRecordGapTerm03257_eq_value :
    recordGapCenter - 141682 = fullRecordGapValue03257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03257 (fullRecordGapValue03257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03257_not_prime : ¬(recordGapCenter - 141682).Prime := by
  rw [fullRecordGapTerm03257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03257_fast_pow_mod_ne_one

def fullRecordGapValue03258 : Nat := fullRecordGapCenterValue - 141238

theorem fullRecordGapTerm03258_eq_value :
    recordGapCenter - 141238 = fullRecordGapValue03258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03258 (fullRecordGapValue03258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03258_not_prime : ¬(recordGapCenter - 141238).Prime := by
  rw [fullRecordGapTerm03258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03258_fast_pow_mod_ne_one

def fullRecordGapValue03259 : Nat := fullRecordGapCenterValue - 140962

theorem fullRecordGapTerm03259_eq_value :
    recordGapCenter - 140962 = fullRecordGapValue03259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03259 (fullRecordGapValue03259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03259_not_prime : ¬(recordGapCenter - 140962).Prime := by
  rw [fullRecordGapTerm03259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03259_fast_pow_mod_ne_one

def fullRecordGapValue03260 : Nat := fullRecordGapCenterValue - 140878

theorem fullRecordGapTerm03260_eq_value :
    recordGapCenter - 140878 = fullRecordGapValue03260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03260 (fullRecordGapValue03260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03260_not_prime : ¬(recordGapCenter - 140878).Prime := by
  rw [fullRecordGapTerm03260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03260_fast_pow_mod_ne_one

def fullRecordGapValue03261 : Nat := fullRecordGapCenterValue - 140362

theorem fullRecordGapTerm03261_eq_value :
    recordGapCenter - 140362 = fullRecordGapValue03261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03261 (fullRecordGapValue03261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03261_not_prime : ¬(recordGapCenter - 140362).Prime := by
  rw [fullRecordGapTerm03261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03261_fast_pow_mod_ne_one

def fullRecordGapValue03262 : Nat := fullRecordGapCenterValue - 140242

theorem fullRecordGapTerm03262_eq_value :
    recordGapCenter - 140242 = fullRecordGapValue03262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03262 (fullRecordGapValue03262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03262_not_prime : ¬(recordGapCenter - 140242).Prime := by
  rw [fullRecordGapTerm03262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03262_fast_pow_mod_ne_one

def fullRecordGapValue03263 : Nat := fullRecordGapCenterValue - 140158

theorem fullRecordGapTerm03263_eq_value :
    recordGapCenter - 140158 = fullRecordGapValue03263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03263 (fullRecordGapValue03263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03263_not_prime : ¬(recordGapCenter - 140158).Prime := by
  rw [fullRecordGapTerm03263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03263_fast_pow_mod_ne_one

def fullRecordGapValue03264 : Nat := fullRecordGapCenterValue - 140038

theorem fullRecordGapTerm03264_eq_value :
    recordGapCenter - 140038 = fullRecordGapValue03264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03264 (fullRecordGapValue03264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03264_not_prime : ¬(recordGapCenter - 140038).Prime := by
  rw [fullRecordGapTerm03264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03264_fast_pow_mod_ne_one

def fullRecordGapValue03265 : Nat := fullRecordGapCenterValue - 139654

theorem fullRecordGapTerm03265_eq_value :
    recordGapCenter - 139654 = fullRecordGapValue03265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03265 (fullRecordGapValue03265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03265_not_prime : ¬(recordGapCenter - 139654).Prime := by
  rw [fullRecordGapTerm03265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03265_fast_pow_mod_ne_one

def fullRecordGapValue03266 : Nat := fullRecordGapCenterValue - 139642

theorem fullRecordGapTerm03266_eq_value :
    recordGapCenter - 139642 = fullRecordGapValue03266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03266 (fullRecordGapValue03266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03266_not_prime : ¬(recordGapCenter - 139642).Prime := by
  rw [fullRecordGapTerm03266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03266_fast_pow_mod_ne_one

def fullRecordGapValue03267 : Nat := fullRecordGapCenterValue - 139558

theorem fullRecordGapTerm03267_eq_value :
    recordGapCenter - 139558 = fullRecordGapValue03267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03267 (fullRecordGapValue03267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03267_not_prime : ¬(recordGapCenter - 139558).Prime := by
  rw [fullRecordGapTerm03267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03267_fast_pow_mod_ne_one

def fullRecordGapValue03268 : Nat := fullRecordGapCenterValue - 139474

theorem fullRecordGapTerm03268_eq_value :
    recordGapCenter - 139474 = fullRecordGapValue03268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03268 (fullRecordGapValue03268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03268_not_prime : ¬(recordGapCenter - 139474).Prime := by
  rw [fullRecordGapTerm03268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03268_fast_pow_mod_ne_one

def fullRecordGapValue03269 : Nat := fullRecordGapCenterValue - 139078

theorem fullRecordGapTerm03269_eq_value :
    recordGapCenter - 139078 = fullRecordGapValue03269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03269 (fullRecordGapValue03269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03269_not_prime : ¬(recordGapCenter - 139078).Prime := by
  rw [fullRecordGapTerm03269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03269_fast_pow_mod_ne_one

def fullRecordGapValue03270 : Nat := fullRecordGapCenterValue - 138862

theorem fullRecordGapTerm03270_eq_value :
    recordGapCenter - 138862 = fullRecordGapValue03270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03270 (fullRecordGapValue03270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03270_not_prime : ¬(recordGapCenter - 138862).Prime := by
  rw [fullRecordGapTerm03270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03270_fast_pow_mod_ne_one

def fullRecordGapValue03271 : Nat := fullRecordGapCenterValue - 138742

theorem fullRecordGapTerm03271_eq_value :
    recordGapCenter - 138742 = fullRecordGapValue03271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03271 (fullRecordGapValue03271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03271_not_prime : ¬(recordGapCenter - 138742).Prime := by
  rw [fullRecordGapTerm03271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03271_fast_pow_mod_ne_one

def fullRecordGapValue03272 : Nat := fullRecordGapCenterValue - 138682

theorem fullRecordGapTerm03272_eq_value :
    recordGapCenter - 138682 = fullRecordGapValue03272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03272 (fullRecordGapValue03272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03272_not_prime : ¬(recordGapCenter - 138682).Prime := by
  rw [fullRecordGapTerm03272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03272_fast_pow_mod_ne_one

def fullRecordGapValue03273 : Nat := fullRecordGapCenterValue - 138600

theorem fullRecordGapTerm03273_eq_value :
    recordGapCenter - 138600 = fullRecordGapValue03273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03273 (fullRecordGapValue03273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03273_not_prime : ¬(recordGapCenter - 138600).Prime := by
  rw [fullRecordGapTerm03273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03273_fast_pow_mod_ne_one

def fullRecordGapValue03274 : Nat := fullRecordGapCenterValue - 138442

theorem fullRecordGapTerm03274_eq_value :
    recordGapCenter - 138442 = fullRecordGapValue03274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03274 (fullRecordGapValue03274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03274_not_prime : ¬(recordGapCenter - 138442).Prime := by
  rw [fullRecordGapTerm03274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03274_fast_pow_mod_ne_one

def fullRecordGapValue03275 : Nat := fullRecordGapCenterValue - 138394

theorem fullRecordGapTerm03275_eq_value :
    recordGapCenter - 138394 = fullRecordGapValue03275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03275 (fullRecordGapValue03275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03275_not_prime : ¬(recordGapCenter - 138394).Prime := by
  rw [fullRecordGapTerm03275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03275_fast_pow_mod_ne_one

def fullRecordGapValue03276 : Nat := fullRecordGapCenterValue - 138238

theorem fullRecordGapTerm03276_eq_value :
    recordGapCenter - 138238 = fullRecordGapValue03276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03276 (fullRecordGapValue03276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03276_not_prime : ¬(recordGapCenter - 138238).Prime := by
  rw [fullRecordGapTerm03276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03276_fast_pow_mod_ne_one

def fullRecordGapValue03277 : Nat := fullRecordGapCenterValue - 138022

theorem fullRecordGapTerm03277_eq_value :
    recordGapCenter - 138022 = fullRecordGapValue03277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03277 (fullRecordGapValue03277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03277_not_prime : ¬(recordGapCenter - 138022).Prime := by
  rw [fullRecordGapTerm03277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03277_fast_pow_mod_ne_one

def fullRecordGapValue03278 : Nat := fullRecordGapCenterValue - 137794

theorem fullRecordGapTerm03278_eq_value :
    recordGapCenter - 137794 = fullRecordGapValue03278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03278 (fullRecordGapValue03278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03278_not_prime : ¬(recordGapCenter - 137794).Prime := by
  rw [fullRecordGapTerm03278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03278_fast_pow_mod_ne_one

def fullRecordGapValue03279 : Nat := fullRecordGapCenterValue - 137500

theorem fullRecordGapTerm03279_eq_value :
    recordGapCenter - 137500 = fullRecordGapValue03279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03279 (fullRecordGapValue03279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03279_not_prime : ¬(recordGapCenter - 137500).Prime := by
  rw [fullRecordGapTerm03279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03279_fast_pow_mod_ne_one

def fullRecordGapValue03280 : Nat := fullRecordGapCenterValue - 137458

theorem fullRecordGapTerm03280_eq_value :
    recordGapCenter - 137458 = fullRecordGapValue03280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03280 (fullRecordGapValue03280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03280_not_prime : ¬(recordGapCenter - 137458).Prime := by
  rw [fullRecordGapTerm03280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03280_fast_pow_mod_ne_one

def fullRecordGapValue03281 : Nat := fullRecordGapCenterValue - 137374

theorem fullRecordGapTerm03281_eq_value :
    recordGapCenter - 137374 = fullRecordGapValue03281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03281 (fullRecordGapValue03281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03281_not_prime : ¬(recordGapCenter - 137374).Prime := by
  rw [fullRecordGapTerm03281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03281_fast_pow_mod_ne_one

def fullRecordGapValue03282 : Nat := fullRecordGapCenterValue - 137200

theorem fullRecordGapTerm03282_eq_value :
    recordGapCenter - 137200 = fullRecordGapValue03282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03282 (fullRecordGapValue03282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03282_not_prime : ¬(recordGapCenter - 137200).Prime := by
  rw [fullRecordGapTerm03282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03282_fast_pow_mod_ne_one

def fullRecordGapValue03283 : Nat := fullRecordGapCenterValue - 137134

theorem fullRecordGapTerm03283_eq_value :
    recordGapCenter - 137134 = fullRecordGapValue03283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03283 (fullRecordGapValue03283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03283_not_prime : ¬(recordGapCenter - 137134).Prime := by
  rw [fullRecordGapTerm03283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03283_fast_pow_mod_ne_one

def fullRecordGapValue03284 : Nat := fullRecordGapCenterValue - 137062

theorem fullRecordGapTerm03284_eq_value :
    recordGapCenter - 137062 = fullRecordGapValue03284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03284 (fullRecordGapValue03284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03284_not_prime : ¬(recordGapCenter - 137062).Prime := by
  rw [fullRecordGapTerm03284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03284_fast_pow_mod_ne_one

def fullRecordGapValue03285 : Nat := fullRecordGapCenterValue - 136978

theorem fullRecordGapTerm03285_eq_value :
    recordGapCenter - 136978 = fullRecordGapValue03285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03285 (fullRecordGapValue03285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03285_not_prime : ¬(recordGapCenter - 136978).Prime := by
  rw [fullRecordGapTerm03285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03285_fast_pow_mod_ne_one

def fullRecordGapValue03286 : Nat := fullRecordGapCenterValue - 136894

theorem fullRecordGapTerm03286_eq_value :
    recordGapCenter - 136894 = fullRecordGapValue03286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03286 (fullRecordGapValue03286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03286_not_prime : ¬(recordGapCenter - 136894).Prime := by
  rw [fullRecordGapTerm03286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03286_fast_pow_mod_ne_one

def fullRecordGapValue03287 : Nat := fullRecordGapCenterValue - 136702

theorem fullRecordGapTerm03287_eq_value :
    recordGapCenter - 136702 = fullRecordGapValue03287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03287 (fullRecordGapValue03287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03287_not_prime : ¬(recordGapCenter - 136702).Prime := by
  rw [fullRecordGapTerm03287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03287_fast_pow_mod_ne_one

def fullRecordGapValue03288 : Nat := fullRecordGapCenterValue - 136342

theorem fullRecordGapTerm03288_eq_value :
    recordGapCenter - 136342 = fullRecordGapValue03288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03288 (fullRecordGapValue03288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03288_not_prime : ¬(recordGapCenter - 136342).Prime := by
  rw [fullRecordGapTerm03288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03288_fast_pow_mod_ne_one

def fullRecordGapValue03289 : Nat := fullRecordGapCenterValue - 136198

theorem fullRecordGapTerm03289_eq_value :
    recordGapCenter - 136198 = fullRecordGapValue03289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03289 (fullRecordGapValue03289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03289_not_prime : ¬(recordGapCenter - 136198).Prime := by
  rw [fullRecordGapTerm03289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03289_fast_pow_mod_ne_one

def fullRecordGapValue03290 : Nat := fullRecordGapCenterValue - 135658

theorem fullRecordGapTerm03290_eq_value :
    recordGapCenter - 135658 = fullRecordGapValue03290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03290 (fullRecordGapValue03290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03290_not_prime : ¬(recordGapCenter - 135658).Prime := by
  rw [fullRecordGapTerm03290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03290_fast_pow_mod_ne_one

def fullRecordGapValue03291 : Nat := fullRecordGapCenterValue - 135202

theorem fullRecordGapTerm03291_eq_value :
    recordGapCenter - 135202 = fullRecordGapValue03291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03291 (fullRecordGapValue03291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03291_not_prime : ¬(recordGapCenter - 135202).Prime := by
  rw [fullRecordGapTerm03291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03291_fast_pow_mod_ne_one

def fullRecordGapValue03292 : Nat := fullRecordGapCenterValue - 135118

theorem fullRecordGapTerm03292_eq_value :
    recordGapCenter - 135118 = fullRecordGapValue03292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03292 (fullRecordGapValue03292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03292_not_prime : ¬(recordGapCenter - 135118).Prime := by
  rw [fullRecordGapTerm03292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03292_fast_pow_mod_ne_one

def fullRecordGapValue03293 : Nat := fullRecordGapCenterValue - 134998

theorem fullRecordGapTerm03293_eq_value :
    recordGapCenter - 134998 = fullRecordGapValue03293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03293 (fullRecordGapValue03293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03293_not_prime : ¬(recordGapCenter - 134998).Prime := by
  rw [fullRecordGapTerm03293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03293_fast_pow_mod_ne_one

def fullRecordGapValue03294 : Nat := fullRecordGapCenterValue - 134962

theorem fullRecordGapTerm03294_eq_value :
    recordGapCenter - 134962 = fullRecordGapValue03294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03294 (fullRecordGapValue03294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03294_not_prime : ¬(recordGapCenter - 134962).Prime := by
  rw [fullRecordGapTerm03294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03294_fast_pow_mod_ne_one

def fullRecordGapValue03295 : Nat := fullRecordGapCenterValue - 134818

theorem fullRecordGapTerm03295_eq_value :
    recordGapCenter - 134818 = fullRecordGapValue03295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03295 (fullRecordGapValue03295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03295_not_prime : ¬(recordGapCenter - 134818).Prime := by
  rw [fullRecordGapTerm03295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03295_fast_pow_mod_ne_one

def fullRecordGapValue03296 : Nat := fullRecordGapCenterValue - 134782

theorem fullRecordGapTerm03296_eq_value :
    recordGapCenter - 134782 = fullRecordGapValue03296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03296 (fullRecordGapValue03296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03296_not_prime : ¬(recordGapCenter - 134782).Prime := by
  rw [fullRecordGapTerm03296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03296_fast_pow_mod_ne_one

def fullRecordGapValue03297 : Nat := fullRecordGapCenterValue - 134362

theorem fullRecordGapTerm03297_eq_value :
    recordGapCenter - 134362 = fullRecordGapValue03297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03297 (fullRecordGapValue03297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03297_not_prime : ¬(recordGapCenter - 134362).Prime := by
  rw [fullRecordGapTerm03297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03297_fast_pow_mod_ne_one

def fullRecordGapValue03298 : Nat := fullRecordGapCenterValue - 134122

theorem fullRecordGapTerm03298_eq_value :
    recordGapCenter - 134122 = fullRecordGapValue03298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03298 (fullRecordGapValue03298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03298_not_prime : ¬(recordGapCenter - 134122).Prime := by
  rw [fullRecordGapTerm03298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03298_fast_pow_mod_ne_one

def fullRecordGapValue03299 : Nat := fullRecordGapCenterValue - 133954

theorem fullRecordGapTerm03299_eq_value :
    recordGapCenter - 133954 = fullRecordGapValue03299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03299 (fullRecordGapValue03299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03299_not_prime : ¬(recordGapCenter - 133954).Prime := by
  rw [fullRecordGapTerm03299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03299_fast_pow_mod_ne_one

def fullRecordGapValue03300 : Nat := fullRecordGapCenterValue - 133894

theorem fullRecordGapTerm03300_eq_value :
    recordGapCenter - 133894 = fullRecordGapValue03300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03300 (fullRecordGapValue03300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03300_not_prime : ¬(recordGapCenter - 133894).Prime := by
  rw [fullRecordGapTerm03300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03300_fast_pow_mod_ne_one

def fullRecordGapValue03301 : Nat := fullRecordGapCenterValue - 133702

theorem fullRecordGapTerm03301_eq_value :
    recordGapCenter - 133702 = fullRecordGapValue03301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03301 (fullRecordGapValue03301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03301_not_prime : ¬(recordGapCenter - 133702).Prime := by
  rw [fullRecordGapTerm03301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03301_fast_pow_mod_ne_one

def fullRecordGapValue03302 : Nat := fullRecordGapCenterValue - 133650

theorem fullRecordGapTerm03302_eq_value :
    recordGapCenter - 133650 = fullRecordGapValue03302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03302 (fullRecordGapValue03302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03302_not_prime : ¬(recordGapCenter - 133650).Prime := by
  rw [fullRecordGapTerm03302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03302_fast_pow_mod_ne_one

def fullRecordGapValue03303 : Nat := fullRecordGapCenterValue - 133618

theorem fullRecordGapTerm03303_eq_value :
    recordGapCenter - 133618 = fullRecordGapValue03303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03303 (fullRecordGapValue03303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03303_not_prime : ¬(recordGapCenter - 133618).Prime := by
  rw [fullRecordGapTerm03303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03303_fast_pow_mod_ne_one

def fullRecordGapValue03304 : Nat := fullRecordGapCenterValue - 132982

theorem fullRecordGapTerm03304_eq_value :
    recordGapCenter - 132982 = fullRecordGapValue03304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03304 (fullRecordGapValue03304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03304_not_prime : ¬(recordGapCenter - 132982).Prime := by
  rw [fullRecordGapTerm03304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03304_fast_pow_mod_ne_one

def fullRecordGapValue03305 : Nat := fullRecordGapCenterValue - 132898

theorem fullRecordGapTerm03305_eq_value :
    recordGapCenter - 132898 = fullRecordGapValue03305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03305 (fullRecordGapValue03305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03305_not_prime : ¬(recordGapCenter - 132898).Prime := by
  rw [fullRecordGapTerm03305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03305_fast_pow_mod_ne_one

def fullRecordGapValue03306 : Nat := fullRecordGapCenterValue - 132718

theorem fullRecordGapTerm03306_eq_value :
    recordGapCenter - 132718 = fullRecordGapValue03306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03306 (fullRecordGapValue03306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03306_not_prime : ¬(recordGapCenter - 132718).Prime := by
  rw [fullRecordGapTerm03306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03306_fast_pow_mod_ne_one

def fullRecordGapValue03307 : Nat := fullRecordGapCenterValue - 132094

theorem fullRecordGapTerm03307_eq_value :
    recordGapCenter - 132094 = fullRecordGapValue03307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03307 (fullRecordGapValue03307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03307_not_prime : ¬(recordGapCenter - 132094).Prime := by
  rw [fullRecordGapTerm03307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03307_fast_pow_mod_ne_one

def fullRecordGapValue03308 : Nat := fullRecordGapCenterValue - 131962

theorem fullRecordGapTerm03308_eq_value :
    recordGapCenter - 131962 = fullRecordGapValue03308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03308 (fullRecordGapValue03308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03308_not_prime : ¬(recordGapCenter - 131962).Prime := by
  rw [fullRecordGapTerm03308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03308_fast_pow_mod_ne_one

def fullRecordGapValue03309 : Nat := fullRecordGapCenterValue - 131914

theorem fullRecordGapTerm03309_eq_value :
    recordGapCenter - 131914 = fullRecordGapValue03309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03309 (fullRecordGapValue03309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03309_not_prime : ¬(recordGapCenter - 131914).Prime := by
  rw [fullRecordGapTerm03309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03309_fast_pow_mod_ne_one

def fullRecordGapValue03310 : Nat := fullRecordGapCenterValue - 131842

theorem fullRecordGapTerm03310_eq_value :
    recordGapCenter - 131842 = fullRecordGapValue03310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03310 (fullRecordGapValue03310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03310_not_prime : ¬(recordGapCenter - 131842).Prime := by
  rw [fullRecordGapTerm03310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03310_fast_pow_mod_ne_one

def fullRecordGapValue03311 : Nat := fullRecordGapCenterValue - 131712

theorem fullRecordGapTerm03311_eq_value :
    recordGapCenter - 131712 = fullRecordGapValue03311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03311 (fullRecordGapValue03311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03311_not_prime : ¬(recordGapCenter - 131712).Prime := by
  rw [fullRecordGapTerm03311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03311_fast_pow_mod_ne_one

def fullRecordGapValue03312 : Nat := fullRecordGapCenterValue - 131662

theorem fullRecordGapTerm03312_eq_value :
    recordGapCenter - 131662 = fullRecordGapValue03312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03312 (fullRecordGapValue03312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03312_not_prime : ¬(recordGapCenter - 131662).Prime := by
  rw [fullRecordGapTerm03312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03312_fast_pow_mod_ne_one

def fullRecordGapValue03313 : Nat := fullRecordGapCenterValue - 131302

theorem fullRecordGapTerm03313_eq_value :
    recordGapCenter - 131302 = fullRecordGapValue03313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03313 (fullRecordGapValue03313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03313_not_prime : ¬(recordGapCenter - 131302).Prime := by
  rw [fullRecordGapTerm03313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03313_fast_pow_mod_ne_one

def fullRecordGapValue03314 : Nat := fullRecordGapCenterValue - 131250

theorem fullRecordGapTerm03314_eq_value :
    recordGapCenter - 131250 = fullRecordGapValue03314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03314 (fullRecordGapValue03314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03314_not_prime : ¬(recordGapCenter - 131250).Prime := by
  rw [fullRecordGapTerm03314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03314_fast_pow_mod_ne_one

def fullRecordGapValue03315 : Nat := fullRecordGapCenterValue - 131158

theorem fullRecordGapTerm03315_eq_value :
    recordGapCenter - 131158 = fullRecordGapValue03315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03315 (fullRecordGapValue03315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03315_not_prime : ¬(recordGapCenter - 131158).Prime := by
  rw [fullRecordGapTerm03315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03315_fast_pow_mod_ne_one

def fullRecordGapValue03316 : Nat := fullRecordGapCenterValue - 131038

theorem fullRecordGapTerm03316_eq_value :
    recordGapCenter - 131038 = fullRecordGapValue03316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03316 (fullRecordGapValue03316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03316_not_prime : ¬(recordGapCenter - 131038).Prime := by
  rw [fullRecordGapTerm03316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03316_fast_pow_mod_ne_one

def fullRecordGapValue03317 : Nat := fullRecordGapCenterValue - 130680

theorem fullRecordGapTerm03317_eq_value :
    recordGapCenter - 130680 = fullRecordGapValue03317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03317 (fullRecordGapValue03317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03317_not_prime : ¬(recordGapCenter - 130680).Prime := by
  rw [fullRecordGapTerm03317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03317_fast_pow_mod_ne_one

def fullRecordGapValue03318 : Nat := fullRecordGapCenterValue - 130654

theorem fullRecordGapTerm03318_eq_value :
    recordGapCenter - 130654 = fullRecordGapValue03318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03318 (fullRecordGapValue03318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03318_not_prime : ¬(recordGapCenter - 130654).Prime := by
  rw [fullRecordGapTerm03318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03318_fast_pow_mod_ne_one

def fullRecordGapValue03319 : Nat := fullRecordGapCenterValue - 130294

theorem fullRecordGapTerm03319_eq_value :
    recordGapCenter - 130294 = fullRecordGapValue03319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03319 (fullRecordGapValue03319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03319_not_prime : ¬(recordGapCenter - 130294).Prime := by
  rw [fullRecordGapTerm03319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03319_fast_pow_mod_ne_one

def fullRecordGapValue03320 : Nat := fullRecordGapCenterValue - 130258

theorem fullRecordGapTerm03320_eq_value :
    recordGapCenter - 130258 = fullRecordGapValue03320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03320 (fullRecordGapValue03320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03320_not_prime : ¬(recordGapCenter - 130258).Prime := by
  rw [fullRecordGapTerm03320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03320_fast_pow_mod_ne_one

def fullRecordGapValue03321 : Nat := fullRecordGapCenterValue - 129838

theorem fullRecordGapTerm03321_eq_value :
    recordGapCenter - 129838 = fullRecordGapValue03321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03321 (fullRecordGapValue03321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03321_not_prime : ¬(recordGapCenter - 129838).Prime := by
  rw [fullRecordGapTerm03321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03321_fast_pow_mod_ne_one

def fullRecordGapValue03322 : Nat := fullRecordGapCenterValue - 129418

theorem fullRecordGapTerm03322_eq_value :
    recordGapCenter - 129418 = fullRecordGapValue03322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03322 (fullRecordGapValue03322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03322_not_prime : ¬(recordGapCenter - 129418).Prime := by
  rw [fullRecordGapTerm03322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03322_fast_pow_mod_ne_one

def fullRecordGapValue03323 : Nat := fullRecordGapCenterValue - 129360

theorem fullRecordGapTerm03323_eq_value :
    recordGapCenter - 129360 = fullRecordGapValue03323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03323 (fullRecordGapValue03323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03323_not_prime : ¬(recordGapCenter - 129360).Prime := by
  rw [fullRecordGapTerm03323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03323_fast_pow_mod_ne_one

def fullRecordGapValue03324 : Nat := fullRecordGapCenterValue - 129322

theorem fullRecordGapTerm03324_eq_value :
    recordGapCenter - 129322 = fullRecordGapValue03324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03324 (fullRecordGapValue03324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03324_not_prime : ¬(recordGapCenter - 129322).Prime := by
  rw [fullRecordGapTerm03324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03324_fast_pow_mod_ne_one

def fullRecordGapValue03325 : Nat := fullRecordGapCenterValue - 129202

theorem fullRecordGapTerm03325_eq_value :
    recordGapCenter - 129202 = fullRecordGapValue03325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03325 (fullRecordGapValue03325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03325_not_prime : ¬(recordGapCenter - 129202).Prime := by
  rw [fullRecordGapTerm03325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03325_fast_pow_mod_ne_one

def fullRecordGapValue03326 : Nat := fullRecordGapCenterValue - 128434

theorem fullRecordGapTerm03326_eq_value :
    recordGapCenter - 128434 = fullRecordGapValue03326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03326 (fullRecordGapValue03326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03326_not_prime : ¬(recordGapCenter - 128434).Prime := by
  rw [fullRecordGapTerm03326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03326_fast_pow_mod_ne_one

def fullRecordGapValue03327 : Nat := fullRecordGapCenterValue - 128314

theorem fullRecordGapTerm03327_eq_value :
    recordGapCenter - 128314 = fullRecordGapValue03327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03327 (fullRecordGapValue03327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03327_not_prime : ¬(recordGapCenter - 128314).Prime := by
  rw [fullRecordGapTerm03327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03327_fast_pow_mod_ne_one

def fullRecordGapValue03328 : Nat := fullRecordGapCenterValue - 128302

theorem fullRecordGapTerm03328_eq_value :
    recordGapCenter - 128302 = fullRecordGapValue03328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03328 (fullRecordGapValue03328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03328_not_prime : ¬(recordGapCenter - 128302).Prime := by
  rw [fullRecordGapTerm03328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03328_fast_pow_mod_ne_one

end PrimeFactorUnimodality
